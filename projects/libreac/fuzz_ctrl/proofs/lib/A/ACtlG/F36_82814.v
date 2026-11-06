(* lib/A/ACtlG/F36_82814.v -- GLUE for the helper stage seg_F36_82814 of fuzz_ctrl image A's walk of
   LLVMFuzzerTestOneInput (lib/A/ACtl.v names no stage for it; it mirrors, in ACtl.v's CF form, Seg/F36.v's own seg_F36_82814 :2944, whose
   entry cut C_A828c0_at exists in ACtlCutP.v:2986), and the SHARED frame-shadow store layer of the three store
   stages of segment F36 (this file, F36_828b8.v, F36_827f4.v).  Written by a Theorem Labs lane (under
   a Theorem Labs lane), one writer.  Pattern: glue-pattern.md (a working note, not in this delivery) (G1-G5, section 4
   for a run that writes memory); worked example lib/A/ACtlG/A5.v; the keep layer follows the steps of
   lib/A/ACtlG/F29.v (a working branch 651b3583ed1), restated for F36's write window.  rule 24: no
   function proved (stage glue of a walk).

   WHAT IT PROVES
     glue_seg_F36_82814 : forall POST (j : nat),
       CF POST (ix_cut C_A828d8_at [Z.of_nat j]) -> CF POST (ix_cut C_A828c0_at [Z.of_nat j])
   with ACtl.v's own CF notation (SK := A.AE2k.tfib_sink_head, FP := []).  ENTRY C_A828c0_at (pc 0x828c0,
   ACtlCutP.v:2877-2888); the run 0x828c0 `sb s11,4(s3)` ; `j 828cc` writes ONE byte, the frame-shadow byte
   S(fr) + 4 (s3 = S(fr)), and changes no register; the body at 0x828cc is C_A828cc_at (ACtlCutP.v:2909-2920, the same
   text as C_A828c0_at), which the dependency glue_seg_F36_82820 (lane CALL, F36_82820.v) turns into the EXIT
   C_A828d8_at.

   THE RUN: A.Prog.Seg.F36F.f36_evt_82814_F (Seg/F36F.v:377-408), lifted at RNG := ProgBridge.RNG_W (w_H W3).

   THE PROOF (glue-pattern.md G1-G5)
   G1  the entry cut at index [Z.of_nat j]: ix_cut's index equation, then C_A828c0_at's body (Permutation, FRAC,
       c_n < 2^26, j <= 255, HB, FLSI, LK, FLSX, rgv 20, LT).
   G2  f36g_stage (below): s3 = S(fr) from FRAC; the written byte's rw_cells from FRAC's 392 frame-shadow bytes and
       ctl_rt_C's cut_shadow region (its (F) disjunct: the owned class-6 frame's shadow); its rng from the
       frame-shadow visibility of the core's al_frames.
   G3  ProgBridge.cfg_at_MS, then YA0nR.SRr_xregs_eqv to the run's canonical map Regs6ss.mkR_of regs3.
   G4  ProgBridge.fevt_of_evtF + tfibsegs_rsegs, then THE lift YA0nR.SRr_fevt_hid (the run writes memory).
   G5  back to regs3 (SRr_xregs_eqv; no register written), then f36g_stage's continuation: journal by
       YCbq.ajournal_exec with Wr = [S(fr) + 4, S(fr) + 5) (awr_byte's in_frames case: the owned class-6 frame's
       shadow), FRAC (the 392 frame-shadow bytes re-read at m'), HB / FLSI / LK / FLSX / LT (no application byte is
       written, and the only shadow written is that of [fr + 32, fr + 40), which no body conjunct reads), ctl_rt_C
       (asan_cells: the window is above RT_HI; cut_shadow / img_shadow regions: writable by wmono, present by munch
       and the written cell; ro_agree: every read-only byte is below 0x5fe000); then lane CALL's glue_seg_F36_82820
       (F36_82820.v, Required).

   ROUTE (C) (L3; ACtlCut.v (at head lib/A/ACtlCut.v:243); the walk shell from a working branch 8ce82d7e310): ctl_from's runtime premise is
   A.ACtlRtC.ctl_rt_C B ly3 S3 mem3 (was ACtlCut.ctl_rt mem3), and f36g_stage takes and gives it at ly3 S3 (the
   store keeps the journal's state).  Its one consumption, the window's wr_at, reads the (F) disjunct of
   A.ACtlRtC.cut_shadow (frames S3 holds (6, c_fpos cx), frame_addr ly3 6 (c_fpos cx) = fr); the post's two
   regions are kept by one local transport (KEEP) for any region P.  VIS0 / OWNED_RO are gone from the Section
   with glue_seg_F36_82820's switch.

   THE SHARED LAYER (sections 1-4 below, Required by F36_828b8.v and F36_827f4.v): f36g_stage is G2 + G5 for any
   run that writes the frame-shadow window [S(fr) + o, S(fr) + e) with 0 <= o < e <= 12 (n = e - o bytes) and keeps
   registers 2 3 4 8 9 18 19 21 22 23 25 26.  The three runs of this lane: o = 4, e = 5 (this file); o = 8, e = 12
   (F36_828b8.v, F36_827f4.v).

   SECTION HYPOTHESES
   - LAWS : R_YG0d.AR_laws segs B -- the core's AR law record (YCbq Section a0, YCbq.v:207), ACtl.v's own
     Hypothesis LAWS (ACtl.v:244).  Owner: the core (porter a Theorem Labs lane); discharged in ACtl.v by YG0q.AR_laws_ok.
   - the Section hypotheses lane CALL's glue_seg_F36_82820 (lib/A/ACtlG/F36_82820.v, Required) takes and this file
     passes to it: RELRO_CAT (the one shared text, owner a Theorem Labs lane), GLOBS / CM_GLOB
     (A.ACtlG.F36_82820.cm_glob_stmt) and CM_SPEC (a Theorem Labs lane's own
     A.Prog.C_reac_box_catalogue_match.treac_box_catalogue_match_spec).
     Each is cited by NAME from F36_82820.v: one text, never a second copy.
   ACtl.v's Section Ctl (ACtl.v:183-238 at a3c6b7b35017) is mirrored in its order in the stage's Section, without
   Batch3's five entries this stage never uses (RELRO_KIND_NAME, RELRO_FRAMES, MO_LE, KREPLY, KPARSE); TFIB_LIB,
   XN_LIB and the two REAC_* variables are unused and vanish at End Section, so the lemma is
   `glue_seg_F36_82814 {fx rc} B MT XM_LIB RLO RHI RELRO_IMG RELRO_CAT LAWS TFIB_SYMS GLOBS CM_GLOB CM_SPEC`
   (About).

   CITED BY NAME (all proved): A.Prog.Seg.F36F.f36_evt_82814_F; R_YA0nR.SRr_fevt_hid / SRr_xregs_eqv;
   A.ProgBridge.fevt_of_evtF / tfibsegs_rsegs / cfg_at_MS / RNG_W / rng_of_visible / fp_avoids_RNG_W / rsegs_spans;
   R_YCbq.ajournal_exec / sep_block_frame / asan_consts; R_YG0d.al_frames;
   R_YK04.find_segment_some_spec; Seg/F36.v's pure helpers f36_addr_keep / f36_stk_tr / f36_spill_keep /
   f36_ba_sub / f36_ba_some / f36_ba_present / f36_sh_frame / f36_sh_frame_of / f36_ro_lo / f36_reg_eq /
   f36_tID_len / f36_tFG_len / f36_fs_body_len (outside its Section, no frame-route premise); A.Prog.RcAsanFPLib.
   fl_bytes; A.AsanRTFacts.app_not_shadow / shadow_of_app / addressable_app / asan_cells_kept / in_shadow_range;
   A.Prog.SlotModel.OUR_length / fr50_length; the kit's kit_wx / kit_segs_low.

   FRAC IS RESTATED BY POSITION in ONE place, f36g_kt_frac (section 3), which rebuilds FRAC conjunct by conjunct;
   Batch3 (d36efc6152d) appended FRAC's fake-frame trailer conjunct q64 m (fr + 4088) (flag_addr ..), and
   f36g_kt_frac proves it with one more `apply TB` line (left disjunct: frame bytes).  f36g_stage reads FRAC by name
   (decompose + assumption).  No run here writes [fr + 4088, fr + 4096): the only bytes written are frame-SHADOW
   bytes (S(fr) + 4, S(fr) + 8 .. + 11), and fr + 4088 is an application byte of the frame; f36g_stage proves every
   application byte outside the write set (f36g_safe's first conjunct), so f36g_ktr's first conjunct keeps the q64 at
   fr + 4088.

   CLOSURE: every project Require below names the FULL directory in its From clause, and every lib/Reusable and
   lib/Lib module is used through a full-path Module alias (R_<X>, L_<X>) or a full-path notation (getrC / fpR /
   fpC / romC / romA): measured in the workspace, the partial name `Lib.Mem` binds to lib/A/Bz/Lib/Mem in this
   closure (Locate lists lib.A.Bz.Lib.Mem first), which made an earlier partial-name draft of this file fail.  No
   Import / Export of a project module; no STATEMENT names a frame-route identifier.

   BUILD STATE: type-check on 5da74c9c931, closure reaches no stand-in (glue base 121bf608343: AE2k / AF0m /
   AF0l / ACej / ACeh compiled from their own text, no port_core_refused substitution); reac_box_catalogue_match_c.v
   is the base's own ccd3e1f3c75.  No Axiom, no Parameter, no Admitted, no admit. *)

From Coq Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YK1b YI04 YM05 YO09 YI16.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK04 YA0n YA0nR YG0f YG00 YG01 YG0d YG0n YC5d YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require ExecF MState Regs6ss Mem Frame Cells Step.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require AB1v AE2k ACfn Img0 AsanRT AsanRTFacts ACtlK ACtlCut ACtlCutP ProgBridge AF0m ACeh.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require SlotModel RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require F36 F36F.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcIdentModel.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require ShadowRwOn ACtlRtC.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require SlotModel C_reac_box_catalogue_match.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlG Require Kit F36_82820.
(* lib/A/Prog/YC4b.v:23 (reached through a Theorem Labs lane's C_reac_box_catalogue_match.v) sets Zify.zify_convert_to_euclidean_division_equations_flag
   to false only Locally, so it does not reach this file. lia here needs the flag true: false is its Stdlib default in Rocq 9.2, and a Required file's global
   `Ltac ... ::=` can also set it (both measured: a Local redefinition does not pass through Require, a global one does). False takes mod / div away from lia
   (build 20261029T091735Z: `No applicable tactic` at F36_82820.v:300).  The value these proofs were checked with (true) is restored for THIS file only. *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* Full-path Module aliases for every lib/Reusable and lib/Lib module this file names: 160 lib/Reusable and
   15 lib/Lib modules have twins (lib/A/Reusable, lib/A/Bz/Lib, ...), so no partial path is used (a Theorem Labs lane
   05:28Z).  R_<X> is lib/Reusable/<X>, L_<X> is lib/Lib/<X>. *)
Module L_Cells := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells.
Module L_ExecF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.
Module L_Frame := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module L_Mem := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Module L_Regs6ss := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.
Module L_Step := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Step.
Module R_YA0n := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YA0n.
Module R_YA0nR := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YA0nR.
Module R_YC5d := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YC5d.
Module R_YCbq := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YCbq.
Module R_YG00 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG00.
Module R_YG01 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG01.
Module R_YG0d := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0d.
Module R_YG0f := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0f.
Module R_YG0n := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0n.
Module R_YK04 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK04.
Import ListNotations.
Local Open Scope Z_scope.

(* The core's segment list, as ACtlCut.v and ACtl.v bind it. *)
Local Notation segs := A.AB1v.tfibsegs.
(* Full-path names of the core's YK11 (one of the six doubled modules) and ctrl's lib/A/Reusable YK11 copy. *)
Local Notation getrC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr.
Local Notation fpR := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.fp_regs.
Local Notation fpC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.fp_csr.
Local Notation romC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.seg_rom.
Local Notation romA := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.seg_rom.
(* LPS's register read (Riscv/Sem.v:301), the one Regs6ss.mkR_of is written with. *)
Local Notation reg_get := LinuxProcessSemantics.Riscv.Sem.reg_get.

(* ---------------------------------------------------------------------------------------------------------
   1. Address facts. *)

(* The core's shadow map (YG0f.shadow_addr) is ctrl's (AsanRT.shadow_addr): both are a / 8 + 0x7fff8000. *)
Lemma f36g_sa_eq : forall a, R_YG0f.shadow_addr a = A.AsanRT.shadow_addr a.
Proof.
  intros a. unfold R_YG0f.shadow_addr, A.AsanRT.shadow_addr, R_YG0f.SHADOW_OFF, A.AsanRT.ASAN_K. lia.
Qed.

(* No byte at or above the image top 0x5fe000 is a segment byte (ProgBridge.rsegs_spans). *)
Lemma f36g_seg_none : forall a, 0x5fe000 <= a -> find_segment A.Img0.rsegs a 1 = None.
Proof.
  intros a Ha. destruct (find_segment A.Img0.rsegs a 1) as [s|] eqn:E; [|reflexivity]. exfalso.
  destruct (R_YK04.find_segment_some_spec _ _ _ _ E) as (Hin & H1 & H2).
  pose proof (in_map (fun s0 : Segment => (Z.of_N (seg_base s0), Z.of_N (seg_size s0))) _ _ Hin) as Hm.
  rewrite A.ProgBridge.rsegs_spans in Hm. cbn [In] in Hm.
  repeat (destruct Hm as [Hm | Hm]; [injection Hm as E1 E2; lia |]). destruct Hm.
Qed.

(* So a byte at or above 0x5fe000 that reads Some through lib/Lib's mrd is a byte of the memory itself. *)
Lemma f36g_mrd_high : forall (m : word -> option byte) (x : word) b,
  0x5fe000 <= bv_unsigned x -> L_Mem.mrd segs m x = Some b -> m x <> None.
Proof.
  intros m x b Hx Hb Hn. unfold L_Mem.mrd in Hb. rewrite Hn in Hb.
  (* mrd reads the image through Common.PropExec.seg_rom, which has the core YK11 seg_rom's body *)
  change (romC segs x = Some b) in Hb.
  unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.seg_rom, memory_read in Hb.
  change (Z.of_N 1) with 1 in Hb.
  pose proof (f36g_seg_none (bv_unsigned x) Hx) as Hn0. rewrite <- A.ProgBridge.tfibsegs_rsegs in Hn0.
  rewrite Hn0 in Hb. discriminate Hb.
Qed.

(* The 50 bytes t_g of a turn. *)
Lemma f36g_t_g_length : forall inp j, length (A.Prog.SlotModel.t_g inp j) = 50%nat.
Proof. intros inp j. unfold A.Prog.SlotModel.t_g. apply A.Prog.SlotModel.fr50_length. Qed.

(* ---------------------------------------------------------------------------------------------------------
   2. A write set that misses the stage bundles: no application byte, and no shadow byte of an address outside
   [fr, fr + 96) (the shadow of [fr, fr + 96) is [S(fr), S(fr) + 12), where F36's nine stores land). *)
Definition f36g_safe (fr : Z) (W : list L_Frame.ivl) : Prop :=
  (forall x, A.AsanRT.app_mem x -> L_Frame.outside W x) /\
  (forall y, 0 <= y < A.AsanRT.APPMEM_END -> ~ (fr <= y < fr + 96) ->
     L_Frame.outside W (A.AsanRT.shadow_addr y)).

Section Keep.
Variables (W : list L_Frame.ivl) (fr : Z) (m m' : word -> option byte).
Hypothesis MU : L_Frame.munch W m m'.
Hypothesis FS : f36g_safe fr W.

Lemma f36g_k_bytes : forall a bs, L_Mem.bytes_at segs m a bs ->
  (forall x, a <= x < a + Z.of_nat (length bs) -> A.AsanRT.app_mem x) ->
  L_Mem.bytes_at segs m' a bs.
Proof.
  intros a bs H Hx. exact (A.Prog.RcAsanFPLib.fl_bytes W m m' a bs H MU (fun x Hr => proj1 FS x (Hx x Hr))).
Qed.

Lemma f36g_k_addr : forall p n, A.AsanRT.addressable m p n ->
  (forall y, p <= y < p + n -> ~ (fr <= y < fr + 96)) -> A.AsanRT.addressable m' p n.
Proof.
  intros p n H Hy. pose proof H as (H0 & Hn & Hend & _).
  apply (A.Prog.Seg.F36.f36_addr_keep W m m' p n H MU). intros i Hi.
  apply (proj2 FS); [split; lia | apply Hy; lia].
Qed.

(* A spill [Ab + off] moves when the spill base Ab (register 9) is high application memory. *)
Lemma f36g_k_spill : forall (regs regs' : bvmap 5 word) Ab off v, ACtlCutP.spill regs m off v ->
  ACtlCut.rgv regs 9 Ab -> getrC regs' 9 = getrC regs 9 ->
  A.AsanRT.HIGHMEM_BEG <= Ab -> Ab + 416 <= A.AsanRT.APPMEM_END -> 0 <= off <= 400 ->
  ACtlCutP.spill regs' m' off v.
Proof.
  intros regs regs' Ab off v Hs HA E9 Hhi Htop Hoff.
  assert (Hx : forall x, Ab <= x < Ab + 416 -> L_Frame.outside W x).
  { intros x Hx. apply (proj1 FS).
    unfold A.AsanRT.app_mem. right. unfold A.AsanRT.HIGHMEM_BEG, A.AsanRT.APPMEM_END in *. lia. }
  unfold A.AsanRT.HIGHMEM_BEG, A.AsanRT.APPMEM_END in *.
  exact (A.Prog.Seg.F36.f36_spill_keep regs regs' m m' W Ab off v Hs MU E9 HA ltac:(lia) ltac:(lia) Hoff Hx).
Qed.

(* HB: the turn's block, apart from [fr, fr + 96). *)
Lemma f36g_k_hb : forall phi len,
  (forall y, phi <= y < phi + A.ACtlK.a_size len -> ~ (fr <= y < fr + 96)) ->
  ACtlCutP.HB m phi len -> ACtlCutP.HB m' phi len.
Proof. intros phi len Hy (H0 & Had). split; [exact H0|]. exact (f36g_k_addr phi _ Had Hy). Qed.
End Keep.

(* ---------------------------------------------------------------------------------------------------------
   3. What the frame-loop bundles (ACtlCutP.v:466-725) and FRAC (:980-994) read, as ONE transfer relation from a
   memory m with map regs to a memory m' with map regs': the frame's bytes and the spill / saved-register block
   [Ab, c_sp), the addressability of frame ranges at offsets >= 96, the spills through register 9, the input block's
   bytes and addressability, the frame's readable-writable range. *)
Definition f36g_ktr (fr Ab : Z) (cx : ACtlCut.ctlcx) (regs regs' : bvmap 5 word)
    (m m' : word -> option byte) : Prop :=
  (forall a bs, L_Mem.bytes_at segs m a bs ->
     (forall x, a <= x < a + Z.of_nat (length bs) -> (fr <= x < fr + 4096) \/ (Ab <= x < ACtlCut.c_sp cx)) ->
     L_Mem.bytes_at segs m' a bs) /\
  (forall p n, A.AsanRT.addressable m p n ->
     (forall y, p <= y < p + n -> fr + 96 <= y < fr + 4096) -> A.AsanRT.addressable m' p n) /\
  (forall off v, 0 <= off <= 400 -> ACtlCutP.spill regs m off v -> ACtlCutP.spill regs' m' off v) /\
  (L_Mem.bytes_at segs m (ACtlCut.c_p cx) (ACtlCut.c_in cx) ->
     L_Mem.bytes_at segs m' (ACtlCut.c_p cx) (ACtlCut.c_in cx)) /\
  (A.AsanRT.addressable m (ACtlCut.c_p cx) (ACtlCut.c_n cx) ->
     A.AsanRT.addressable m' (ACtlCut.c_p cx) (ACtlCut.c_n cx)) /\
  (L_Frame.stk segs m fr (fr + 3136) -> L_Frame.stk segs m' fr (fr + 3136)).

(* The facts a munch-run transfer takes: the frame and the input block are application memory, the input block
   misses the frame, the spill base Ab (register 9) is high application memory below c_sp, register 9 kept. *)
Definition f36g_kenv (W : list L_Frame.ivl) (fr : Z) (m m' : word -> option byte) (cx : ACtlCut.ctlcx)
    (regs regs' : bvmap 5 word) (Ab : Z) : Prop :=
  L_Frame.munch W m m' /\ f36g_safe fr W /\
  (forall y, fr <= y < fr + 4096 -> A.AsanRT.app_mem y) /\
  (forall y, ACtlCut.c_p cx <= y < ACtlCut.c_p cx + ACtlCut.c_n cx ->
     A.AsanRT.app_mem y /\ ~ (fr <= y < fr + 4096)) /\
  Z.of_nat (length (ACtlCut.c_in cx)) = ACtlCut.c_n cx /\
  ACtlCut.rgv regs 9 Ab /\ getrC regs' 9 = getrC regs 9 /\
  A.AsanRT.HIGHMEM_BEG <= Ab /\ Ab + 416 <= ACtlCut.c_sp cx /\ ACtlCut.c_sp cx <= A.AsanRT.APPMEM_END.

Lemma f36g_ktr_of_munch : forall W fr m m' cx regs regs' Ab, f36g_kenv W fr m m' cx regs regs' Ab ->
  L_Frame.wmono segs m m' -> f36g_ktr fr Ab cx regs regs' m m'.
Proof.
  intros W fr m m' cx regs regs' Ab (MU & FS & HFAPP & HCP & HLEN & R9 & E9 & HAHI & HAc & HcAPP) WM.
  split.
  { intros a bs H Hx. apply (f36g_k_bytes W fr m m' MU FS a bs H). intros x Hr.
    destruct (Hx x Hr) as [H1 | H1].
    - apply HFAPP; lia.
    - unfold A.AsanRT.app_mem. right. unfold A.AsanRT.HIGHMEM_BEG, A.AsanRT.APPMEM_END in *. lia. }
  split.
  { intros p n H Hy. apply (f36g_k_addr W fr m m' MU FS p n H). intros y Hr. pose proof (Hy y Hr). lia. }
  split.
  { intros off v Ho Hs. exact (f36g_k_spill W fr m m' MU FS regs regs' Ab off v Hs R9 E9 HAHI ltac:(lia) Ho). }
  split.
  { intros H. apply (f36g_k_bytes W fr m m' MU FS _ _ H). intros x Hr. rewrite HLEN in Hr.
    exact (proj1 (HCP x Hr)). }
  split.
  { intros H. apply (f36g_k_addr W fr m m' MU FS _ _ H). intros y Hr. destruct (HCP y Hr) as (_ & Hn). lia. }
  intros Hstk. apply (A.Prog.Seg.F36.f36_stk_tr W m m' fr (fr + 3136) Hstk MU WM). intros x Hx.
  left. apply (proj1 FS). apply HFAPP. lia.
Qed.

Section Bundles.
Variables (fr Ab : Z) (cx : ACtlCut.ctlcx) (regs regs' : bvmap 5 word) (m m' : word -> option byte).
Hypothesis HT : f36g_ktr fr Ab cx regs regs' m m'.

Let TB := proj1 HT.
Let TA := proj1 (proj2 HT).
Let SP := proj1 (proj2 (proj2 HT)).
Let TCB := proj1 (proj2 (proj2 (proj2 HT))).
Let TCA := proj1 (proj2 (proj2 (proj2 (proj2 HT)))).
Let TSTK := proj2 (proj2 (proj2 (proj2 (proj2 HT)))).

Lemma f36g_kt_pro : ACtlCutP.PRO cx fr regs m -> ACtlCutP.PRO cx fr regs' m'.
Proof.
  intros (H40 & H120 & H136 & H160 & H168 & H176 & H208 & H248 & Had & Hby & Hin & H184 & H256 & H264 & H272 & H32).
  split; [apply SP; [lia | exact H40]|]. split; [apply SP; [lia | exact H120]|].
  split; [apply SP; [lia | exact H136]|]. split; [apply SP; [lia | exact H160]|].
  split; [apply SP; [lia | exact H168]|]. split; [apply SP; [lia | exact H176]|].
  split; [apply SP; [lia | exact H208]|]. split; [apply SP; [lia | exact H248]|].
  split; [apply TA; [exact Had | intros y Hy; lia]|].
  split; [exact (TCB Hby)|].
  split; [intros Hn0; exact (TCA (Hin Hn0))|].
  split; [apply SP; [lia | exact H184]|]. split; [apply SP; [lia | exact H256]|].
  split; [apply SP; [lia | exact H264]|]. split; [apply SP; [lia | exact H272] | apply SP; [lia | exact H32]].
Qed.

Lemma f36g_kt_flsh : forall j, ACtlCutP.FLSH cx j fr regs m -> ACtlCutP.FLSH cx j fr regs' m'.
Proof.
  intros j (HP & H128 & Hstk & H144 & Had17).
  split; [exact (f36g_kt_pro HP)|]. split; [apply SP; [lia | exact H128]|].
  split; [unfold ACtlCutP.FRAME_BYTES in *; exact (TSTK Hstk)|].
  split; [apply SP; [lia | exact H144]|].
  apply TA; [exact Had17 | intros y Hy; lia].
Qed.

Lemma f36g_kt_flc : ACtlCutP.FLC fr regs m -> ACtlCutP.FLC fr regs' m'.
Proof.
  intros (C256 & C184 & C192 & C80 & C88 & C96 & C272 & C264 & Cfa & Cra & C72 & C64 & C56 & C48).
  split; [apply SP; [lia | exact C256]|]. split; [apply SP; [lia | exact C184]|].
  split; [apply SP; [lia | exact C192]|]. split; [apply SP; [lia | exact C80]|].
  split; [apply SP; [lia | exact C88]|]. split; [apply SP; [lia | exact C96]|].
  split; [apply SP; [lia | exact C272]|]. split; [apply SP; [lia | exact C264]|].
  split; [apply TA; [exact Cfa | unfold ACtlCutP.fragb; intros y Hy; lia]|].
  split; [apply TA; [exact Cra | intros y Hy; lia]|].
  split; [apply SP; [lia | exact C72]|]. split; [apply SP; [lia | exact C64]|].
  split; [apply SP; [lia | exact C56] | apply SP; [lia | exact C48]].
Qed.

Lemma f36g_kt_flsi : forall j, ACtlCutP.FLSI cx j fr regs m -> ACtlCutP.FLSI cx j fr regs' m'.
Proof.
  intros j (HH & H216 & H224 & H248 & (Had & Hby) & HC).
  split; [exact (f36g_kt_flsh j HH)|].
  split; [apply SP; [lia | exact H216]|]. split; [apply SP; [lia | exact H224]|].
  split; [apply SP; [lia | exact H248]|].
  split; [split; [exact (TCA Had) | exact (TCB Hby)] | exact (f36g_kt_flc HC)].
Qed.

Lemma f36g_kt_lk : forall j, getrC regs' 21 = getrC regs 21 ->
  ACtlCutP.LK cx fr j regs m -> ACtlCutP.LK cx fr j regs' m'.
Proof.
  intros j E21 (Hj & H21 & HOUR).
  split; [exact Hj|]. split; [exact (eq_trans E21 H21)|].
  unfold ACtlCutP.OURb in *. apply TB; [exact HOUR|].
  rewrite A.Prog.SlotModel.OUR_length. intros x Hx. change (Z.of_nat 6) with 6 in Hx. left. lia.
Qed.

Lemma f36g_kt_lt : forall j, ACtlCutP.LT cx fr j regs m -> ACtlCutP.LT cx fr j regs' m'.
Proof.
  intros j HLT.
  unfold ACtlCutP.LT, ACtlCutP.IFS, ACtlCutP.IDj, ACtlCutP.IDb, ACtlCutP.IDBe, ACtlCutP.FGj, ACtlCutP.FGb,
    ACtlCutP.FGBe, ACtlCutP.FSj, ACtlCutP.FSb in *.
  destruct HLT as ((HIDB & Hok1) & (HFGB & Hok2) & (H104 & H112 & Hbody & Had & HFI)).
  split; [split; [|exact Hok1]|split; [split; [|exact Hok2]|]].
  - apply TB; [exact HIDB|]. rewrite A.Prog.Seg.F36.f36_tID_len. intros x Hx.
    change (Z.of_nat OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcIdentModel.ID_SIZE) with 38 in Hx.
    left. lia.
  - apply TB; [exact HFGB|]. rewrite A.Prog.Seg.F36.f36_tFG_len. intros x Hx.
    change (Z.of_nat 72) with 72 in Hx. left. lia.
  - split; [apply SP; [lia | exact H104]|]. split; [apply SP; [lia | exact H112]|].
    split.
    + apply TB; [exact Hbody|]. intros x Hx.
      pose proof (A.Prog.Seg.F36.f36_fs_body_len (ACtlCut.c_in cx) (S j)) as Hl. left. lia.
    + split; [apply TA; [exact Had | intros y Hy; lia] | exact HFI].
Qed.

Lemma f36g_kt_flsx : forall j phi,
  getrC regs' 18 = getrC regs 18 -> getrC regs' 22 = getrC regs 22 -> getrC regs' 23 = getrC regs 23 ->
  getrC regs' 25 = getrC regs 25 ->
  (forall bs, Z.of_nat (length bs) <= ACtlCutP.flen cx j ->
     L_Mem.bytes_at segs m phi bs -> L_Mem.bytes_at segs m' phi bs) ->
  ACtlCutP.FLSX cx j phi fr regs m -> ACtlCutP.FLSX cx j phi fr regs' m'.
Proof.
  intros j phi E18 E22 E23 E25 TPH (HI & H18 & H22 & H23 & H25 & Hrec & H152 & H280).
  split; [exact (f36g_kt_flsi j HI)|].
  split; [exact (eq_trans E18 H18)|]. split; [exact (eq_trans E22 H22)|].
  split; [exact (eq_trans E23 H23)|]. split; [exact (eq_trans E25 H25)|].
  split.
  { intros H50. destruct (Hrec H50) as (Hp0 & Hp1 & Hg & Hpb & Hpl).
    split; [exact Hp0|]. split; [exact Hp1|].
    split; [apply TPH; [rewrite f36g_t_g_length; change (Z.of_nat 50) with 50; lia | exact Hg]|].
    split; [apply TPH; [exact Hpl | exact Hpb] | exact Hpl]. }
  split; [apply SP; [lia | exact H152] | apply SP; [lia | exact H280]].
Qed.

(* FRAC at the new map and memory, its spill base being Ab; the 392 frame-shadow bytes re-read at m'.  FRAC is
   destructed BY POSITION here, so Batch3's appended conjunct (the fake-frame trailer word q64 m (fr + 4088)
   (flag_addr ..), d36efc6152d) is one more `apply TB` line: its 8 bytes [fr + 4088, fr + 4096) are frame bytes. *)
Lemma f36g_kt_frac : forall B sel,
  ACtlCut.rgv regs 9 Ab -> 0 <= Ab < 2 ^ 64 ->
  getrC regs' 2 = getrC regs 2 -> getrC regs' 3 = getrC regs 3 -> getrC regs' 4 = getrC regs 4 ->
  getrC regs' 8 = getrC regs 8 -> getrC regs' 9 = getrC regs 9 -> getrC regs' 19 = getrC regs 19 ->
  getrC regs' 26 = getrC regs 26 ->
  (exists sh, L_Mem.bytes_at segs m' (ACtlCutP.Sfr fr) sh /\ length sh = Z.to_nat ACtlCutP.FRAME_SHADOW) ->
  ACtlCutP.FRAC B cx fr sel regs m -> ACtlCutP.FRAC B cx fr sel regs' m'.
Proof.
  intros B sel RAb HAb E2 E3 E4 E8 E9 E19 E26 Hsh'
    (A1 & sp & R2 & Hsp16 & HspZ & R4 & R8 & R9 & R3 & R19 & R26 & Hfr32 & HA32 & HAc & HspA &
     HfrA & HA416 & Hspc & HcAPP & Q304 & Q24 & Q16 & Qhdr & Qhdr16 & _ & Hsaved & Qtrl).
  pose proof HfrA as HfrA'. unfold ACtlCutP.FRAME_BYTES in HfrA'.
  assert (Hsp0 : 0 <= sp < 2 ^ 64).
  { rewrite <- HspZ. unfold R_YG0d.spZ.
    pose proof (bv_unsigned_in_range 64 (getrC regs 2)) as Hr.
    change (bv_modulus 64) with (2 ^ 64) in Hr. exact Hr. }
  assert (EA : A1 = Ab).
  { apply (A.Prog.Seg.F36.f36_reg_eq regs 9 A1 Ab R9 RAb); [unfold A.AsanRT.APPMEM_END in HcAPP; lia | exact HAb]. }
  subst A1.
  exists Ab, sp.
  split; [exact (eq_trans E2 R2)|]. split; [exact Hsp16|].
  split; [unfold R_YG0d.spZ in *; rewrite <- HspZ; exact (f_equal (@bv_unsigned 64) E2)|].
  split; [exact (eq_trans E4 R4)|]. split; [exact (eq_trans E8 R8)|]. split; [exact (eq_trans E9 R9)|].
  split; [exact (eq_trans E3 R3)|]. split; [exact (eq_trans E19 R19)|]. split; [exact (eq_trans E26 R26)|].
  split; [exact Hfr32|]. split; [exact HA32|]. split; [exact HAc|]. split; [exact HspA|]. split; [exact HfrA|].
  split; [exact HA416|]. split; [exact Hspc|]. split; [exact HcAPP|].
  unfold ACtlCutP.q64 in *.
  split.
  { apply TB; [exact Q304|]. rewrite L_Mem.length_le8. intros x Hx. change (Z.of_nat 8) with 8 in Hx.
    right. lia. }
  split.
  { apply TB; [exact Q24|]. rewrite L_Mem.length_le8. intros x Hx. change (Z.of_nat 8) with 8 in Hx.
    right. lia. }
  split.
  { apply TB; [exact Q16|]. rewrite L_Mem.length_le8. intros x Hx. change (Z.of_nat 8) with 8 in Hx.
    right. lia. }
  split.
  { apply TB; [exact Qhdr|]. rewrite L_Mem.length_le8. intros x Hx. change (Z.of_nat 8) with 8 in Hx.
    left. lia. }
  split.
  { apply TB; [exact Qhdr16|]. rewrite L_Mem.length_le8. intros x Hx. change (Z.of_nat 8) with 8 in Hx.
    left. lia. }
  split; [exact Hsh'|].
  split.
  { apply TB; [exact Hsaved|].
    assert (Hsl : length (ACtlCutP.saved_bytes cx) = 104%nat).
    { unfold ACtlCutP.saved_bytes. rewrite !length_app, !L_Mem.length_le8. reflexivity. }
    rewrite Hsl. intros x Hx. change (Z.of_nat 104) with 104 in Hx. right. lia. }
  (* the fake-frame trailer word at fr + 4088: inside the owned frame [fr, fr + 4096) *)
  apply TB; [exact Qtrl|]. rewrite L_Mem.length_le8. intros x Hx. change (Z.of_nat 8) with 8 in Hx.
  left. lia.
Qed.
End Bundles.

(* ---------------------------------------------------------------------------------------------------------
   4. The stage layer: G2 and G5 for a run that writes the frame-shadow window [S(fr) + o, S(fr) + e), from the cut
   shell and the common body prefix of the F36 cuts (Permutation, FRAC, HB, FLSI, LK, FLSX, LT) and ctl_rt_C. *)
Section F36GStore.
Context {fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.FPState}
        {rc : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.RunCeil}
        {LS : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.lib_shape}.
Variable B : R_YG0f.asyms.
Variable MT : R_YC5d.ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Hypothesis LAWS : R_YG0d.AR_laws segs B.

Lemma f36g_stage : forall (cx : ACtlCut.ctlcx) (fr k : Z) ly3 S3 W3 (regs3 : bvmap 5 word)
    (mem3 : word -> option byte) md3 (phi : Z) (j : nat) (o e : Z) (n : nat),
  ACtlCut.ctl_base B MT XM_LIB RLO RHI cx ->
  R_YCbq.ajournal (SK := A.AE2k.tfib_sink_head) segs B A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) []
    (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx)
    (ACtlCut.own6 cx) ly3 S3 W3 mem3 md3 k ->
  R_YG01.frames S3 = ACtlCut.own6 cx ->
  (forall cid pos, In (cid, pos) (ACtlCut.own6 cx) -> fr = R_YG0f.frame_addr (ACtlCut.c_ly cx) cid pos) ->
  Permutation (R_YG0d.ablocks B ly3 S3)
    (R_YG0d.ablocks B (ACtlCut.c_ly cx) (ACtlCut.c_S cx) ++ [(phi, ACtlCutP.flen cx j)]) ->
  ACtlCutP.FRAC B cx fr fr regs3 mem3 -> ACtlCutP.HB mem3 phi (ACtlCutP.flen cx j) ->
  ACtlCutP.FLSI cx j fr regs3 mem3 -> ACtlCutP.LK cx fr j regs3 mem3 -> ACtlCutP.FLSX cx j phi fr regs3 mem3 ->
  ACtlCutP.LT cx fr j regs3 mem3 -> A.ACtlRtC.ctl_rt_C B ly3 S3 mem3 ->
  0 <= o -> (0 < n)%nat -> e = o + Z.of_nat n -> e <= 12 ->
  getrC regs3 19 = Z_to_bv 64 (ACtlCutP.Sfr fr) /\ 0 <= ACtlCutP.Sfr fr /\ ACtlCutP.Sfr fr + 12 <= 2 ^ 64 /\
  (exists bs, L_Step.rw_cells A.Img0.rsegs mem3 (ACtlCutP.Sfr fr + o) [L_Cells.CB n bs]) /\
  L_ExecF.rng (A.ProgBridge.RNG_W (R_YA0n.w_H W3)) (ACtlCutP.Sfr fr + o) (Z.of_nat n) /\
  (forall (regs' : bvmap 5 word) (m' : word -> option byte) md',
     L_Frame.munch [(ACtlCutP.Sfr fr + o, ACtlCutP.Sfr fr + e)] mem3 m' ->
     L_Frame.wmono segs mem3 m' ->
     (exists cs, L_Step.rw_cells segs m' (ACtlCutP.Sfr fr + o) cs /\ L_Cells.cells_size cs = n) ->
     (forall x : word, R_YA0n.w_H W3 x = true -> m' x = mem3 x) ->
     R_YK04.same_but_materialized md3 md' ->
     getrC regs' 2 = getrC regs3 2 -> getrC regs' 3 = getrC regs3 3 -> getrC regs' 4 = getrC regs3 4 ->
     getrC regs' 8 = getrC regs3 8 -> getrC regs' 9 = getrC regs3 9 -> getrC regs' 18 = getrC regs3 18 ->
     getrC regs' 19 = getrC regs3 19 -> getrC regs' 21 = getrC regs3 21 -> getrC regs' 22 = getrC regs3 22 ->
     getrC regs' 23 = getrC regs3 23 -> getrC regs' 25 = getrC regs3 25 -> getrC regs' 26 = getrC regs3 26 ->
     R_YCbq.ajournal (SK := A.AE2k.tfib_sink_head) segs B A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) []
       (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx)
       (ACtlCut.own6 cx) ly3 S3 W3 m' md' k /\
     ACtlCutP.FRAC B cx fr fr regs' m' /\ ACtlCutP.HB m' phi (ACtlCutP.flen cx j) /\
     ACtlCutP.FLSI cx j fr regs' m' /\ ACtlCutP.LK cx fr j regs' m' /\ ACtlCutP.FLSX cx j phi fr regs' m' /\
     ACtlCutP.LT cx fr j regs' m' /\ A.ACtlRtC.ctl_rt_C B ly3 S3 m').
Proof.
  intros cx fr k ly3 S3 W3 regs3 mem3 md3 phi j o e n Hbase HJ HF HL Hperm HFRAC HHB HFLSI HLK HFLSX HLT Hrt
    Ho Hn Hoe He12.
  (* the frame, its shadow and its visibility, from the journal's AR (al_frames) and the shell's frame law *)
  pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hgone & _ & Hastk & _).
  pose proof Hly as (_ & _ & _ & _ & _ & EF & _).
  pose proof Hastk as (_ & _ & Hstklo & Hstkhi & _).
  pose proof R_YCbq.asan_consts as (Hceil & _).
  unfold A.ACfn.LLVMF_STK in Hstkhi.
  assert (Hin6 : In (6, ACtlCut.c_fpos cx) (R_YG01.frames S3)) by (rewrite HF; left; reflexivity).
  assert (Efr : fr = R_YG0f.frame_addr (ACtlCut.c_ly cx) 6 (ACtlCut.c_fpos cx))
    by (apply HL; left; reflexivity).
  assert (Efr3 : R_YG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx) = fr)
    by (rewrite Efr; unfold R_YG0f.frame_addr; rewrite EF; reflexivity).
  assert (E4096 : R_YG00.fs_frame_bytes 6 = 4096) by reflexivity.
  destruct (R_YG0d.al_frames _ _ LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin6)
    as (_ & Hfapp & _ & Hfsh).
  rewrite Efr3, E4096 in Hfapp. rewrite Efr3, E4096 in Hfsh. change (4096 / 8) with 512 in Hfsh.
  unfold R_YG0f.in_app, R_YG0f.kLowShadowBeg, R_YG0f.kHighMemBeg,
    R_YG0f.ASAN_CEIL in Hfapp.
  assert (HFAPP : forall y, fr <= y < fr + 4096 -> A.AsanRT.app_mem y).
  { intros y Hy. unfold A.AsanRT.app_mem, A.AsanRT.LOWMEM_END, A.AsanRT.HIGHMEM_BEG, A.AsanRT.APPMEM_END.
    destruct Hfapp as (H1 & [H2 | (H2 & H3)]); [left | right]; lia. }
  (* FRAC's facts by NAME, not by position (decompose + assumption, as F38.v does), so a conjunct added to FRAC
     does not move them: the spill base Ab (register 9), s3 = S(fr), the frame bounds, the 392 frame-shadow bytes *)
  pose proof HFRAC as (Ab & sp & HFR).
  assert (R9 : ACtlCut.rgv regs3 9 Ab) by (decompose [and] HFR; assumption).
  assert (R19 : ACtlCut.rgv regs3 19 (ACtlCutP.Sfr fr)) by (decompose [and] HFR; assumption).
  assert (HFB : fr mod 32 = 0 /\ Ab <= ACtlCut.c_sp cx /\ sp <= Ab /\ fr + ACtlCutP.FRAME_BYTES <= Ab /\
                Ab + 416 <= ACtlCut.c_sp cx /\ ACtlCut.c_sp cx - 4096 < sp /\ ACtlCut.c_sp cx <= A.AsanRT.APPMEM_END)
    by (decompose [and] HFR; repeat split; assumption).
  destruct HFB as (Hfr32 & HAc & HspA & HfrA & HA416 & Hspc & HcAPP).
  assert (Hshx : exists sh, L_Mem.bytes_at segs mem3 (ACtlCutP.Sfr fr) sh /\
                   length sh = Z.to_nat ACtlCutP.FRAME_SHADOW) by (decompose [and] HFR; assumption).
  destruct Hshx as (sh & Hsh & Hshl). clear HFR.
  unfold ACtlCutP.FRAME_BYTES in HfrA.
  assert (Hfr8 : fr mod 8 = 0) by (clear - Hfr32; Z.div_mod_to_equations; lia).
  assert (Hfr0 : 0 <= fr) by (destruct Hfapp; lia).
  assert (Hcsp : A.AsanRT.HIGHMEM_BEG + 4096 <= ACtlCut.c_sp cx)
    by (unfold A.AsanRT.HIGHMEM_BEG; lia).
  assert (HAHI : A.AsanRT.HIGHMEM_BEG <= Ab) by (unfold A.AsanRT.HIGHMEM_BEG in *; lia).
  assert (HcAPP' : ACtlCut.c_sp cx <= A.AsanRT.APPMEM_END) by lia.
  assert (HAb64 : 0 <= Ab < 2 ^ 64) by (unfold A.AsanRT.HIGHMEM_BEG, A.AsanRT.APPMEM_END in *; lia).
  (* the turn's block phi: live at this cut, apart from the frame *)
  assert (Hinphi : In (phi, ACtlCutP.flen cx j) (R_YG0d.ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. left. reflexivity. }
  pose proof (R_YCbq.sep_block_frame segs B LAWS ly3 S3 W3 mem3 md3 phi _ 6 (ACtlCut.c_fpos cx) HAR Hinphi Hin6)
    as Hdphi.
  rewrite Efr3, E4096 in Hdphi. unfold R_YG0f.zdisjoint in Hdphi. cbn [fst snd] in Hdphi.
  pose proof HHB as (_ & HphA).
  pose proof (A.AsanRTFacts.addressable_app _ _ _ HphA) as HphApp.
  assert (HPH : forall y, phi <= y < phi + A.ACtlK.a_size (ACtlCutP.flen cx j) ->
            A.AsanRT.app_mem y /\ ~ (fr <= y < fr + 4096)).
  { intros y Hy. split; [apply HphApp; lia|].
    assert (Hrq : R_YG00.req_size (ACtlCutP.flen cx j) = A.ACtlK.a_size (ACtlCutP.flen cx j)).
    { pose proof (A.Prog.Seg.F36.f36_len_nonneg (ACtlCut.c_in cx) j) as Hl0.
      unfold R_YG00.req_size, A.ACtlK.a_size, ACtlCutP.flen in *.
      destruct (Z.eqb_spec (A.Prog.SlotModel.t_len (ACtlCut.c_in cx) j) 0) as [E0|E0]; lia. }
    rewrite Hrq in Hdphi. lia. }
  (* the input block: live at entry, still live (FP = []), apart from the frame *)
  pose proof Hbase as ((_ & _ & _ & _ & Hpn & Hlen & _) & _).
  pose proof HFLSI as (_ & _ & _ & _ & (HinA & _) & _).
  pose proof (A.AsanRTFacts.addressable_app _ _ _ HinA) as HinApp.
  assert (HCP : forall y, ACtlCut.c_p cx <= y < ACtlCut.c_p cx + ACtlCut.c_n cx ->
            A.AsanRT.app_mem y /\ ~ (fr <= y < fr + 4096)).
  { intros y Hy. split; [apply HinApp; lia|].
    destruct Hpn as [(Hn0 & _) | (Hn0 & Hinp)]; [lia|].
    assert (Hdec : forall x y : Z * Z, {x = y} + {x <> y}) by (intros x0 y0; decide equality; apply Z.eq_dec).
    assert (Hinp3 : In (ACtlCut.c_p cx, ACtlCut.c_n cx) (R_YG0d.ablocks B ly3 S3)).
    { destruct (in_dec Hdec (ACtlCut.c_p cx, ACtlCut.c_n cx) (R_YG0d.ablocks B ly3 S3)) as [Hi|Hni];
        [exact Hi|].
      exfalso. apply (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI04.inFP_nil (ACtlCut.c_p cx + 0)).
      apply (Hgone _ _ 0 Hinp Hni). unfold R_YG00.req_size. destruct (Z.eqb_spec (ACtlCut.c_n cx) 0); lia. }
    pose proof (R_YCbq.sep_block_frame segs B LAWS ly3 S3 W3 mem3 md3 _ _ 6 (ACtlCut.c_fpos cx) HAR Hinp3 Hin6)
      as Hdin.
    rewrite Efr3, E4096 in Hdin. unfold R_YG0f.zdisjoint in Hdin. cbn [fst snd] in Hdin.
    unfold R_YG00.req_size in Hdin. destruct (Z.eqb_spec (ACtlCut.c_n cx) 0); lia. }
  assert (HLEN : Z.of_nat (length (ACtlCut.c_in cx)) = ACtlCut.c_n cx) by (symmetry; exact Hlen).
  (* the frame's 512 shadow bytes are shadow memory *)
  set (Sh := ACtlCutP.Sfr fr) in *.
  assert (ESh : Sh = A.AsanRT.shadow_addr fr) by reflexivity.
  assert (HshA : forall i, 0 <= i < 512 -> Sh + i = A.AsanRT.shadow_addr (fr + 8 * i)).
  { intros i Hi. rewrite ESh. rewrite A.Prog.Seg.F36.f36_sh_frame_of by lia. reflexivity. }
  assert (HinSh : forall i, 0 <= i < 512 -> A.AsanRT.in_shadow (Sh + i)).
  { intros i Hi. rewrite (HshA i Hi). apply A.AsanRTFacts.shadow_of_app. apply HFAPP. lia. }
  pose proof (A.AsanRTFacts.in_shadow_range _ (HinSh 0 ltac:(lia))) as HSb0.
  pose proof (A.AsanRTFacts.in_shadow_range _ (HinSh 511 ltac:(lia))) as HSb1.
  assert (HSlo : A.AsanRT.LOWMEM_END <= Sh).
  { pose proof (HinSh 0 ltac:(lia)) as H0. unfold A.AsanRT.in_shadow, A.AsanRT.LOWMEM_END,
      A.AsanRT.LOWSHADOW_END, A.AsanRT.HIGHSHADOW_BEG, A.AsanRT.HIGHMEM_BEG in *. lia. }
  assert (Hshl' : length sh = 392%nat) by (rewrite Hshl; reflexivity).
  (* the frame's 512 shadow bytes lie in ctl_rt_C's cut_shadow, by its (F) disjunct (the owned class-6 frame) *)
  assert (HCUT : forall i, 0 <= i < 512 -> A.ACtlRtC.cut_shadow B ly3 S3 (Sh + i)).
  { intros i Hi. left. exists 6, (ACtlCut.c_fpos cx). split; [exact Hin6|].
    rewrite Efr3, E4096, f36g_sa_eq, <- ESh. change (4096 / 8) with 512. lia. }
  destruct Hrt as (Hac & Hcut & Himg & Hro).
  (* ---- G2: the run's premises ---- *)
  split; [exact R19|]. split; [lia|]. split; [lia|].
  split.
  { exists (firstn n (skipn (Z.to_nat o) sh)).
    pose proof (A.Prog.Seg.F36.f36_ba_sub mem3 Sh sh (Z.to_nat o) n Hsh ltac:(lia)) as Hsub.
    rewrite Z2Nat.id in Hsub by lia.
    split; [split|].
    - cbn [L_Cells.cells_wf L_Cells.cell_wf]. split; [rewrite length_firstn, length_skipn; lia | exact I].
    - cbn [L_Cells.cells_bytes L_Cells.cbytes]. rewrite app_nil_r. exact Hsub.
    - cbn [L_Cells.cells_size L_Cells.csize]. rewrite Nat.add_0_r. unfold L_Mem.wr_at.
      split; [lia|]. split; [lia|]. intros i Hi.
      replace (Sh + o + i) with (Sh + (o + i)) by lia.
      exact (proj1 (Hcut _ (HCUT (o + i) ltac:(lia)) (HinSh (o + i) ltac:(lia)))). }
  split.
  { apply A.ProgBridge.rng_of_visible. split; [lia|]. split; [lia|]. intros a Ha.
    destruct (Hfsh (a - Sh) ltac:(lia)) as ((Hv & _) & _).
    rewrite f36g_sa_eq, <- ESh in Hv. replace (Sh + (a - Sh)) with a in Hv by lia. exact Hv. }
  (* ---- G5: the continuation at the run's end map regs' and memory m' ---- *)
  intros regs' m' md' MU WM (cs & Hcs & Hcsl) Hhid Hsbm E2 E3 E4 E8 E9 E18 E19 E21 E22 E23 E25 E26.
  assert (Hnew : forall x, Sh + o <= x < Sh + e -> exists b, L_Mem.mrd segs m' (L_Mem.wa x) = Some b).
  { intros x Hx. destruct Hcs as ((Hwf & Hba) & _).
    pose proof (L_Cells.cells_bytes_length cs Hwf) as Hcl.
    replace x with (Sh + o + (x - (Sh + o))) by lia.
    apply (A.Prog.Seg.F36.f36_ba_some m' (Sh + o) (L_Cells.cells_bytes cs)); [exact Hba|].
    rewrite Hcl, Hcsl. lia. }
  assert (FS : f36g_safe fr [(Sh + o, Sh + e)]).
  { split.
    - intros x Hx. cbn [L_Frame.outside]. split; [|exact I]. intros Hin.
      apply (A.AsanRTFacts.app_not_shadow x Hx).
      replace x with (Sh + (x - Sh)) by lia. apply HinSh. lia.
    - intros y Hy Hny. cbn [L_Frame.outside]. split; [|exact I]. intros Hin. apply Hny.
      pose proof (A.Prog.Seg.F36.f36_sh_frame fr y (A.AsanRT.shadow_addr y - Sh) Hfr0 Hfr8 ltac:(lia)
                    ltac:(rewrite <- ESh; lia)) as Hz.
      lia. }
  assert (HE : f36g_kenv [(Sh + o, Sh + e)] fr mem3 m' cx regs3 regs' Ab).
  { split; [exact MU|]. split; [exact FS|]. split; [exact HFAPP|]. split; [exact HCP|].
    split; [exact HLEN|]. split; [exact R9|]. split; [exact E9|]. split; [exact HAHI|].
    split; [exact HA416 | exact HcAPP']. }
  pose proof (f36g_ktr_of_munch _ _ _ _ _ _ _ _ HE WM) as HT.
  split.
  { (* journal: the written bytes are the owned frame's shadow (ajournal_exec, YCbq.v:636-643) *)
    eapply (R_YCbq.ajournal_exec (SK := A.AE2k.tfib_sink_head) segs B LAWS A.ACtlG.Kit.kit_segs_low)
      with (Wr := fun a => Sh + o <= a < Sh + e).
    - exact HJ.
    - intros x Hx. unfold R_YK04.mrestrict. destruct (R_YA0n.w_H W3 x); [reflexivity|].
      apply MU. cbn [L_Frame.outside]. split; [exact Hx | exact I].
    - intros x Hx. unfold R_YK04.mrestrict in *. destruct (R_YA0n.w_H W3 x); [exact Hx|].
      destruct (Z_le_gt_dec (Sh + o) (bv_unsigned x)) as [H1|H1];
        [destruct (Z_lt_ge_dec (bv_unsigned x) (Sh + e)) as [H2|H2]|].
      + destruct (Hnew (bv_unsigned x) ltac:(lia)) as (b & Hb).
        unfold L_Mem.wa in Hb.
        (* MEASURED in this file's own context (About): the bare name expands to stdpp's generic lemma, not to
           either MState copy, so it is qualified to stdpp (a Theorem Labs lane 07:01Z). *)
        rewrite stdpp.bitvector.definitions.Z_to_bv_bv_unsigned in Hb.
        apply (f36g_mrd_high m' x b); [unfold A.AsanRT.LOWMEM_END in HSlo; lia | exact Hb].
      + rewrite MU; [exact Hx|]. cbn [L_Frame.outside]. split; [lia | exact I].
      + rewrite MU; [exact Hx|]. cbn [L_Frame.outside]. split; [lia | exact I].
    - exact Hhid.
    - exact Hsbm.
    - intros a Ha. unfold R_YCbq.awr_byte, R_YCbq.in_frames. right. right. right.
      exists 6, (ACtlCut.c_fpos cx). split; [left; reflexivity|]. right.
      rewrite Efr3, E4096, f36g_sa_eq, <- ESh. unfold R_YG0n.in_zr. cbn [fst snd].
      change (4096 / 8) with 512. lia. }
  split.
  { (* FRAC: registers kept, bytes kept, the 392 frame-shadow bytes re-read at m' *)
    apply (f36g_kt_frac fr Ab cx regs3 regs' mem3 m' HT B fr R9 HAb64 E2 E3 E4 E8 E9 E19 E26); [|exact HFRAC].
    assert (Hpres : forall i, (i < 392)%nat ->
              exists b, L_Mem.mrd A.Img0.rsegs m' (L_Mem.wa (Sh + Z.of_nat i)) = Some b).
    { intros i Hi.
      destruct (Z_le_gt_dec o (Z.of_nat i)) as [H1|H1];
        [destruct (Z_lt_ge_dec (Z.of_nat i) e) as [H2|H2]|].
      - apply Hnew. lia.
      - destruct (A.Prog.Seg.F36.f36_ba_some mem3 Sh sh (Z.of_nat i) Hsh ltac:(rewrite Hshl'; lia)) as (b & Hb).
        exists b. unfold L_Mem.mrd in *. rewrite MU; [exact Hb|].
        rewrite L_Mem.wa_unsigned by lia. cbn [L_Frame.outside]. split; [lia | exact I].
      - destruct (A.Prog.Seg.F36.f36_ba_some mem3 Sh sh (Z.of_nat i) Hsh ltac:(rewrite Hshl'; lia)) as (b & Hb).
        exists b. unfold L_Mem.mrd in *. rewrite MU; [exact Hb|].
        rewrite L_Mem.wa_unsigned by lia. cbn [L_Frame.outside]. split; [lia | exact I]. }
    destruct (A.Prog.Seg.F36.f36_ba_present m' 392 Sh ltac:(lia) ltac:(lia) Hpres) as (sh' & Hb' & Hl').
    exists sh'. split; [exact Hb' | rewrite Hl'; reflexivity]. }
  split.
  { apply (f36g_k_hb [(Sh + o, Sh + e)] fr mem3 m' MU FS); [|exact HHB].
    intros y Hy. destruct (HPH y Hy) as (_ & Hn'). lia. }
  split; [exact (f36g_kt_flsi fr Ab cx regs3 regs' mem3 m' HT j HFLSI)|].
  split; [exact (f36g_kt_lk fr Ab cx regs3 regs' mem3 m' HT j E21 HLK)|].
  split.
  { apply (f36g_kt_flsx fr Ab cx regs3 regs' mem3 m' HT j phi E18 E22 E23 E25); [|exact HFLSX].
    intros bs Hbs Hb. apply (f36g_k_bytes [(Sh + o, Sh + e)] fr mem3 m' MU FS _ _ Hb).
    intros x Hx. destruct (HPH x ltac:(unfold A.ACtlK.a_size; lia)) as (Ha & _). exact Ha. }
  split; [exact (f36g_kt_lt fr Ab cx regs3 regs' mem3 m' HT j HLT)|].
  (* ctl_rt_C B ly3 S3 m': asan_cells (the window is far above RT_HI), the cut_shadow / img_shadow regions (KEEP:
     writable by wmono, present by munch outside the window and by the written cells inside), ro_agree *)
  assert (KEEP : forall P, A.ShadowRwOn.shadow_rw_on P mem3 -> A.ShadowRwOn.shadow_rw_on P m').
  { intros P HP a Hp Ha.
    destruct (HP a Hp Ha) as (Hw & b & Hb). split; [apply WM; exact Hw|].
    pose proof (A.AsanRTFacts.in_shadow_range a Ha) as Hab.
    destruct (Z_le_gt_dec (Sh + o) a) as [H1|H1]; [destruct (Z_lt_ge_dec a (Sh + e)) as [H2|H2]|].
    + apply Hnew. lia.
    + exists b. unfold L_Mem.mrd in *. rewrite MU; [exact Hb|].
      rewrite L_Mem.wa_unsigned by lia. cbn [L_Frame.outside]. split; [lia | exact I].
    + exists b. unfold L_Mem.mrd in *. rewrite MU; [exact Hb|].
      rewrite L_Mem.wa_unsigned by lia. cbn [L_Frame.outside]. split; [lia | exact I]. }
  split; [|split; [|split]].
  - apply (A.AsanRTFacts.asan_cells_kept _ mem3 m' Hac MU). cbn [L_Frame.disjoint_from].
    unfold A.AsanRT.RT_LO, A.AsanRT.RT_HI. unfold A.AsanRT.LOWMEM_END in HSlo.
    split; [left; lia | exact I].
  - exact (KEEP _ Hcut).
  - exact (KEEP _ Himg).
  - unfold A.ACtlK.ro_agree_at in *. intros a Ha.
    pose proof (A.Prog.Seg.F36.f36_ro_lo a Ha) as Hlo.
    unfold L_Mem.mrd in *. rewrite MU; [exact (Hro a Ha)|].
    cbn [L_Frame.outside]. split; [unfold A.AsanRT.LOWMEM_END in HSlo; lia | exact I].
Qed.

End F36GStore.

(* ---------------------------------------------------------------------------------------------------------
   5. The stage. *)
Section GlueF36_82814.

(* ACtl.v's Section Ctl (ACtl.v:183-238 at a3c6b7b35017) in its order, RELRO_CAT in ACtl.v's exact text and name.
   Batch3's other new entries (RELRO_KIND_NAME, RELRO_FRAMES, MO_LE, KREPLY, KPARSE) are left out: this stage never
   uses them, and as Section facts in scope a tactic (lia) could pick one up and so change the lemma's arguments.
   At End Section the lemma keeps only what it uses. *)
Context {fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.FPState} {rc : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.RunCeil} {LS : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.lib_shape}.
Variable B : R_YG0f.asyms.
Variable MT : R_YC5d.ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> R_YG0d.in_img segs a.
Hypothesis RELRO_CAT : RLO <= A.Prog.SlotModel.CAT /\ A.Prog.SlotModel.CAT + A.Prog.SlotModel.CAT_N * A.Prog.SlotModel.CAT_ROW <= RHI.
Hypothesis LAWS : R_YG0d.AR_laws segs B.
Hypothesis TFIB_SYMS : A.AF0m.CtrlTSyms B.
Hypothesis TFIB_LIB : A.ACeh.TfibLib B.
Variable REAC_CTRL_IDENTITY_REPLY_K : Z.
Variable REAC_CTRL_PARSE_BC : Z.

(* ACtl.v's notation block, verbatim. *)
Local Notation ix_cut := ACtlCut.ix_cut.
Local Notation CF POST X :=
  (ACtlCut.ctl_from (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation C_A828c0_at := (ACtlCutP.C_A828c0_at B).
Local Notation C_A828cc_at := (ACtlCutP.C_A828cc_at B).
Local Notation C_A828d8_at := (ACtlCutP.C_A828d8_at B).

(* What lane CALL's glue_seg_F36_82820 takes, cited by name from its file (one text each): the runtime's registered
   globals and the catalogue's row in them, and a Theorem Labs lane's cgif-form spec of reac_box_catalogue_match. *)
Variable GLOBS : list (Z * Z).
Hypothesis CM_GLOB : A.ACtlG.F36_82820.cm_glob_stmt GLOBS.
Hypothesis CM_SPEC : A.Prog.C_reac_box_catalogue_match.treac_box_catalogue_match_spec (SK := A.AE2k.tfib_sink_head) B RLO RHI GLOBS.

Lemma glue_seg_F36_82814 : forall POST (j : nat),
  CF POST (ix_cut C_A828d8_at [Z.of_nat j]) -> CF POST (ix_cut C_A828c0_at [Z.of_nat j]).
Proof.
  intros POST j HX.
  pose proof (A.ACtlG.F36_82820.glue_seg_F36_82820 B MT XM_LIB RLO RHI RELRO_IMG RELRO_CAT LAWS TFIB_SYMS
                GLOBS CM_GLOB CM_SPEC POST j HX) as HCC.
  intros cx idx fr k ly3 S3 W3 regs3 mem3 md3 Hbase HJ HF HL Hk Hbody Hrt.
  (* G1: the entry cut at index [Z.of_nat j] *)
  destruct Hbody as [Hidx Hb]. subst idx.
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A828c0_at ACtlCutP.ixn nth] in Hb.
  rewrite Nat2Z.id in Hb.
  destruct Hb as (phi & Hperm & HFRAC & Hcn & Hj & HHB & HFLSI & HLK & HFLSX & H20 & HLT).
  (* G2: the run's premises and the continuation's facts (f36g_stage, window [S(fr) + 4, S(fr) + 5)) *)
  destruct (f36g_stage B MT XM_LIB RLO RHI LAWS cx fr k ly3 S3 W3 regs3 mem3 md3 phi j 4 5 1%nat
              Hbase HJ HF HL Hperm HFRAC HHB HFLSI HLK HFLSX HLT Hrt
              ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia))
    as (E19 & HS0 & HS1 & (bs & HRW) & Hrng & HSTEP).
  assert (R19 : reg_get regs3 19 = Z_to_bv 64 (ACtlCutP.Sfr fr)) by exact E19.
  (* G3: the cut's configuration in the run's state form, the walk moved to the run's canonical map *)
  rewrite A.ProgBridge.cfg_at_MS.
  change (ACtlCut.cut_pc (ix_cut C_A828c0_at [Z.of_nat j])) with 0x828c0.
  apply (R_YA0nR.SRr_xregs_eqv segs W3 (L_Regs6ss.mkR_of regs3) regs3 fpR (Z_to_bv 64 0x828c0) fpC None
           mem3 (romC segs) md3 (POST cx));
    [| exact (L_Regs6ss.xregs_eqv_sym _ _ (L_Regs6ss.mkR_of_eqv regs3))].
  (* G4: the run and its lift *)
  pose proof (A.Prog.Seg.F36F.f36_evt_82814_F (A.ProgBridge.RNG_W (R_YA0n.w_H W3))
    (reg_get regs3 1) (reg_get regs3 2) (reg_get regs3 3) (reg_get regs3 4) (reg_get regs3 5) (reg_get regs3 6)
    (reg_get regs3 7) (reg_get regs3 8) (reg_get regs3 9) (reg_get regs3 10) (reg_get regs3 11)
    (reg_get regs3 12) (reg_get regs3 13) (reg_get regs3 14) (reg_get regs3 15) (reg_get regs3 16)
    (reg_get regs3 17) (reg_get regs3 18) (reg_get regs3 19) (reg_get regs3 20) (reg_get regs3 21)
    (reg_get regs3 22) (reg_get regs3 23) (reg_get regs3 24) (reg_get regs3 25) (reg_get regs3 26)
    (reg_get regs3 27) (reg_get regs3 28) (reg_get regs3 29) (reg_get regs3 30) (reg_get regs3 31)
    fpR fpC mem3 (ACtlCutP.Sfr fr) bs R19 HRW HS0 ltac:(lia) Hrng)
    as HRUN.
  change (romA A.Img0.rsegs) with (romC A.Img0.rsegs) in HRUN.
  pose proof (A.ProgBridge.fevt_of_evtF _ _ _ HRUN) as HFS.
  rewrite <- A.ProgBridge.tfibsegs_rsegs in HFS.
  apply (R_YA0nR.SRr_fevt_hid segs A.ACtlG.Kit.kit_wx W3 _ md3 (A.ProgBridge.RNG_W (R_YA0n.w_H W3)) _
           (POST cx) HFS).
  { apply A.ProgBridge.fp_avoids_RNG_W. }
  intros ms' md' HP Hhid Hsbm.
  destruct HP as (m' & Ems & MU & WM & HCS). subst ms'.
  change (forall x : word, R_YA0n.w_H W3 x = true -> m' x = mem3 x) in Hhid.
  (* G5: back to the cut's own map (the run writes no register), then the body at 0x828cc *)
  apply (R_YA0nR.SRr_xregs_eqv segs W3 regs3 (L_Regs6ss.mkR_of regs3) fpR (Z_to_bv 64 0x828cc) fpC None
           m' (romC segs) md' (POST cx)); [| exact (L_Regs6ss.mkR_of_eqv regs3)].
  change (R_YA0n.SRr segs W3
            (R_YG0d.cfg_at segs (ACtlCut.cut_pc (ix_cut C_A828cc_at [Z.of_nat j])) regs3 m' md') (POST cx)).
  destruct (HSTEP regs3 m' md' MU WM HCS Hhid Hsbm eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
              eq_refl eq_refl eq_refl eq_refl)
    as (HJ' & HFRAC' & HHB' & HFLSI' & HLK' & HFLSX' & HLT' & Hrt').
  apply (HCC cx [Z.of_nat j] fr k ly3 S3 W3 regs3 m' md' Hbase HJ' HF HL Hk); [|exact Hrt'].
  (* the body C_A828cc_at (ACtlCutP.v:2909-2920) at the same index *)
  split; [reflexivity|].
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A828cc_at ACtlCutP.ixn nth].
  rewrite Nat2Z.id.
  exists phi.
  split; [exact Hperm|]. split; [exact HFRAC'|]. split; [exact Hcn|]. split; [exact Hj|].
  split; [exact HHB'|]. split; [exact HFLSI'|].
  split; [exact HLK'|]. split; [exact HFLSX'|]. split; [exact H20 | exact HLT'].
Qed.

End GlueF36_82814.
