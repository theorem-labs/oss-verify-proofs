(* lib/A/ACtlG/Jrel.v -- GLUE for stage seg_Jrel of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput (lib/A/ACtl.v,
   W5 tail).  Written by a Theorem Labs lane; single writer.  rule 24: no function proved (stage glue of a walk;
   the released-proof position of LLVMFuzzerTestOneInput was settled for this unit: At ossv/recipes c5e779efe8c (2026-10-31), no released proof of it outside this unit).

   WHAT IT PROVES
     glue_seg_Jrel : forall POST, CF POST C_A82b9c -> CF POST C_Jrel
   with ACtl.v's own CF notation (SK := A.AE2k.tfib_sink_head, FP := []), i.e. exactly ACtl.v's Section hypothesis
   seg_Jrel.  Entry C_Jrel (0x82b80, the release join), exit C_A82b9c (the frame_release_6 call site, side arm).
   Segment Jrel runs 0x82b80 -> 0x82b9c (Seg/YTail.v seg_Jrel, side arm s5 = fr; the class-full arm s5 = 0 is the
   discharged one, ACtl.v's glue comment):
     0x82b80 lui a0,0x45e03   0x82b84 addiw a0,a0,0x60e   0x82b88 sd a0,0(s6)   0x82b8c beqz s5,0x82ba4 (not taken)
     0x82b90 lui a0,1         0x82b94 addiw a1,a0,-0x3c0  0x82b98 mv a0,s5
   so it WRITES memory: the frame header word [fr, fr + 8) becomes 0x45e0360e.

   THE PROOF (glue-pattern.md G1-G5, section 4 "run that writes memory")
   G1  C_Jrel's body: Permutation, FRAHC with header 0x41b58ab3, rgv 21 sel, rgv 22 fr (sel = fr, the shell's).
   G2  the run's premises: s5 = s6 = fr (registers 21 / 22); 0 < fr < 2 ^ 64 (AR_frames_law's in_app, FRAHC);
       rw_cells of the header (FRAHC's q64 at fr, writable from AR_frames_law's presence); stk at the empty window;
       the footprint range [fr, fr + 8) visible (AR_frames_law: frame bytes are present, so not hidden).
   G3  ProgBridge.cfg_at_MS, then YA0nR.SRr_xregs_eqv from the cut's map to mkR_of regs3.
   G4  YTailF.jrel_evt_side_F at RNG := ProgBridge.RNG_W (w_H W3), its fx := A.Reusable.YK11.mkFP of the Section's
       fp_regs / fp_csr (glue-pattern.md section 6); ProgBridge.fevt_of_evtF, tfibsegs_rsegs; YA0nR.SRr_fevt_hid.
   G5  the exit C_A82b9c at the run's end map R and memory m':
         journal  YCbq.ajournal_exec with Wr := [fr, fr + 8): outside Wr munch; mem_grows (a header byte is read back
                  from m' and is not an image byte, AR_client_img_law); hidden bytes from SRr_fevt_hid; awr_byte's
                  in_frames case (the owned class-6 frame, via the frame law and layout_le's ly_F);
         frames, frame law, k   unchanged (own6, kmax EV_LLVMF on both cuts);
         body     FRAHC with header 0x45e0360e: registers through R (computed), the new header from the run's post,
                  every other memory conjunct carried across [fr, fr + 8) by Lib.Frame.bytes_at_transport (Batch3's
                  trailer word at fr + 4088 by jr_q64_keep);
                  sel = fr, a0 = fr, a1 = FRAME_BYTES = 3136;
         ctl_rt_C asan_cells (image cells, apart from the non-image header), shadow_rw_on of both regions (the state
                  stays ly3 S3, so the regions are the entry's; a shadow byte is never the app-memory header),
                  ro_agree (a read-only byte is an image byte, never a header byte).

   SECTION HYPOTHESES
   - LAWS: the core's AR law record (YCbq Section a0's hypothesis; ACtl.v's Section Ctl LAWS).  Used for
     ajournal_exec, AR_frames_law and AR_client_img_law.
   No other hypothesis: the run is Required from the _F file of record (Seg/YTailF.v), not assumed.

   CITED BY NAME: YTailF.jrel_evt_side_F; ProgBridge RNG_W / fp_avoids_RNG_W / rng_of_visible / fevt_of_evtF /
   tfibsegs_rsegs / cfg_at_MS; YA0nR SRr_xregs_eqv / SRr_fevt_hid; YCbq ajournal_exec / find_segment_none; YK04
   find_segment_some_spec; Lib.Frame bytes_at_transport; Regs6ss mkR_of / mkR_of_eqv / xregs_eqv_sym; Kit kit_wx /
   kit_segs_low.

   CLOSURE (glue closure rule): every Require is qualified; every Reusable / Lib module is named by its FULL path
   (module aliases below), because six modules exist both as the core's lib/Reusable/<X> and ctrl's
   lib/A/Reusable/<X> and lib/A/Bz/Lib duplicates lib/Lib names (a Theorem Labs lane, 03:48Z); no statement names a
   frame-route identifier.  The closure gains Seg/YTailF.v's (Seg/YTail.v, SlotInv, AsanRTInv, Contract, FrameAPI,
   PFrameAPI, MemNorm ...), as the closure rule allows for an _F file.

   SHADOWED NAMES: getr / mkst / seg_rom / cfg_at only through the full-path aliases RK11 / RG0d / AK11.

   BUILD STATE: see the commit message (type-check, planning core, port_core_refused substitution in the build
   workspace only). *)

From Stdlib Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
(* reg_get (the explicit register binders of the _F run are Regs6ss.mkR_of's fields), as YK11.v:11 imports it *)
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK04.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YA0n.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YA0nR.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG00.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG01.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0f.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0n.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0d.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YC5d.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YCbq.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.PropExec.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Step.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AB1v.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AE2k.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Img0.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AsanRT.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlK.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCut.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCutP.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ShadowRwOn.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlRtC.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgBridge.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.YTailF.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlG.Kit.
Import ListNotations.
Local Open Scope Z_scope.

Module RK11 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
Module RM05 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.
Module RO09 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.
Module RK04 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK04.
Module RA0n := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YA0n.
Module RA0nR := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YA0nR.
Module RG00 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG00.
Module RG01 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG01.
Module RG0f := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0f.
Module RG0n := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0n.
Module RG0d := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0d.
Module RC5d := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YC5d.
Module RCbq := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YCbq.
Module LEF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.
Module LMS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Module LR6 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.
Module LPE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.PropExec.
Module LMM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Module LCE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells.
Module LST := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Step.
Module LFR := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module PB := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgBridge.
Module ART := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AsanRT.
Module AK11 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.
Module YTF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.YTailF.

(* The core's segment list, as ACtlCut.v and ACtl.v bind it. *)
Local Notation segs := A.AB1v.tfibsegs.

(* ---------------------------------------------------------------------------------------------------------
   Proof-internal facts about the image (no Section argument). *)

(* Every byte of [0x10000, 0x5fe000) lies in a segment of the image (ProgBridge.rsegs_spans: the four PT_LOADs tile
   that range). *)
Lemma jr_img_in : forall a, 0x10000 <= a < 0x5fe000 -> RG0d.in_img segs a.
Proof.
  intros a Ha.
  assert (Hm : forall b sz, In (b, sz) (map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) A.Img0.rsegs) ->
                 b <= a < b + sz -> RG0d.in_img segs a).
  { intros b sz Hin Hr. apply in_map_iff in Hin as (s & Es & Hs). injection Es as <- <-.
    exists s. split; [exact Hs | lia]. }
  rewrite PB.rsegs_spans in Hm.
  destruct (Z_lt_le_dec a 0x30000) as [h1 | h1].
  { apply (Hm 0x10000 0x20000); [left; reflexivity | lia]. }
  destruct (Z_lt_le_dec a 0x9e000) as [h2 | h2].
  { apply (Hm 0x30000 0x6e000); [right; left; reflexivity | lia]. }
  destruct (Z_lt_le_dec a 0xa1000) as [h3 | h3].
  { apply (Hm 0x9e000 0x3000); [right; right; left; reflexivity | lia]. }
  apply (Hm 0xa1000 0x55d000); [right; right; right; left; reflexivity | lia].
Qed.

(* A byte outside the image reads from memory only: mrd's ROM fallback is None there. *)
Lemma jr_mem_of_mrd : forall (m : word -> option byte) (x : word) b,
  ~ RG0d.in_img segs (bv_unsigned x) -> LMM.mrd A.Img0.rsegs m x = Some b -> m x = Some b.
Proof.
  intros m x b Hni H. unfold LMM.mrd in H. destruct (m x) as [b'|]; [exact H|].
  exfalso. unfold LPE.seg_rom, memory_read in H. cbn [Z.of_N] in H.
  change A.Img0.rsegs with segs in H.
  rewrite (RCbq.find_segment_none segs _ Hni) in H. discriminate.
Qed.

(* A q64 cell carried across a write confined to [lo, hi). *)
Lemma jr_q64_keep : forall (m m' : word -> option byte) lo hi a v,
  ACtlCutP.q64 m a v -> LFR.munch [(lo, hi)] m m' -> (a + 8 <= lo \/ hi <= a) -> ACtlCutP.q64 m' a v.
Proof.
  intros m m' lo hi a v Hq HM Hd. unfold ACtlCutP.q64 in *.
  apply (LFR.bytes_at_transport segs [(lo, hi)] m m' a _ Hq HM).
  cbn [LFR.disjoint_from]. rewrite LMM.length_le8. split; [lia | exact I].
Qed.

(* The entry registers' saved-word block is 13 words. *)
Lemma jr_saved_len : forall cx, length (ACtlCutP.saved_bytes cx) = 104%nat.
Proof. intros cx. unfold ACtlCutP.saved_bytes. rewrite !app_length, !LMM.length_le8. reflexivity. Qed.

(* A byte list read from memory is read the same from a memory that agrees on its range. *)
Lemma jr_ba_keep : forall (m m' : word -> option byte) a bs,
  (forall x : word, a <= bv_unsigned x < a + Z.of_nat (length bs) -> m' x = m x) ->
  LMM.bytes_at A.Img0.rsegs m a bs -> LMM.bytes_at A.Img0.rsegs m' a bs.
Proof.
  intros m m' a bs Hk (H0 & H1 & H). split; [exact H0|]. split; [exact H1|].
  intros i Hi. pose proof (H i Hi) as Hm. unfold LMM.mrd in Hm |- *.
  rewrite Hk; [exact Hm|]. rewrite LMM.wa_unsigned by lia. lia.
Qed.

(* ctl_rt's runtime cells (AsanRT.asan_cells: seventeen cells, all in the runtime's image range
   [RT_LO, RT_HI) = [0x9fad0, 0xa9578)) survive any write that keeps the image bytes. *)
Lemma jr_cells_keep : forall (m m' : word -> option byte),
  (forall x : word, 0x10000 <= bv_unsigned x < 0x5fe000 -> m' x = m x) ->
  A.ACtlK.asan_cells_at m -> A.ACtlK.asan_cells_at m'.
Proof.
  intros m m' Hk H. unfold A.ACtlK.asan_cells_at, ART.asan_cells in *.
  repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end.
  repeat match goal with |- _ /\ _ => split end.
  all: eapply jr_ba_keep; [|eassumption]; intros x Hx; apply Hk;
    unfold ART.CELL_K, ART.GOT_CELL_K, ART.INITED, ART.REPLACE, ART.GOT_REPLACE, ART.UAR, ART.GOT_UAR,
      ART.CANPOISON, ART.HIEND, ART.GOT_HIEND, ART.MIDBEG, ART.GOT_MIDBEG, ART.MIDEND, ART.GOT_MIDEND,
      ART.REAL_MEMCPY, ART.REAL_MEMSET, ART.GOT_REAL_MEMSET in Hx;
    rewrite ?LMM.length_le8, ?LMM.length_le4 in Hx; cbn [length Z.of_nat Pos.of_succ_nat] in Hx; lia.
Qed.

Section GlueJrel.

(* ACtl.v's Section Ctl shape (84ef756918c), in its order: the core class by full path, the same Variables and
   Hypotheses, except TFIB_SYMS / TFIB_LIB, which no glue step here reads and whose types (A.AF0m.CtrlTSyms,
   A.ACeh.TfibLib) would put two planning-core stand-in files into this file's Require closure.  End GlueJrel keeps
   only what glue_seg_Jrel uses. *)
Context {fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.FPState}
        {rc : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.RunCeil}
        {LS : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.lib_shape}.
Variable B : RG0f.asyms.
Variable MT : RC5d.ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> RG0d.in_img segs a.
(* The core's AR laws (YCbq.v Section a0's hypothesis; ACtl.v's LAWS). *)
Hypothesis LAWS : RG0d.AR_laws segs B.
Variable REAC_CTRL_IDENTITY_REPLY_K : Z.
Variable REAC_CTRL_PARSE_BC : Z.

(* ACtl.v's notation block, verbatim. *)
Local Notation ix_cut := ACtlCut.ix_cut.
Local Notation CF POST X :=
  (ACtlCut.ctl_from (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation C_Jrel := (ACtlCutP.C_Jrel B).
Local Notation C_A82b9c := (ACtlCutP.C_A82b9c B).

Lemma glue_seg_Jrel : forall POST, CF POST C_A82b9c -> CF POST C_Jrel.
Proof.
  intros POST HX cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
  (* G1: the entry cut C_Jrel (ACtlCutP.v C_Jrel). *)
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_Jrel] in Hbody.
  destruct Hbody as (HP & HFRAH & R21 & R22).
  destruct HFRAH as (A & sp & R2 & Hsp16 & Hspz & R4 & R8 & R9 & R3 & R19 & R26 & Hfr32 & HA32 & HAc & HspA &
    HfrA & HA416 & Hsplo & Hcapp & Q304 & Qhdr & Q16 & Hsh & Hsaved & Htrl).
  destruct Hrt as (Hcells & Hcut & Himg & Hro).
  (* G2: the frame, from the journal's AR (frames_law, client_img_law) and the frame law. *)
  pose proof HJ as (HAR & Hly & _).
  destruct Hly as (_ & _ & _ & _ & _ & EF & _).
  assert (Hin : In (6, ACtlCut.c_fpos cx) (RG01.frames S3)) by (rewrite HF; left; reflexivity).
  assert (Efr : fr = RG0f.frame_addr (ACtlCut.c_ly cx) 6 (ACtlCut.c_fpos cx)) by (apply HL; left; reflexivity).
  assert (EF3 : RG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx) = fr).
  { rewrite Efr. unfold RG0f.frame_addr. rewrite EF. reflexivity. }
  assert (Hfsb : RG00.fs_frame_bytes 6 = 4096) by reflexivity.
  assert (Hfl : RG0d.AR_frames_law segs B) by (destruct LAWS; assumption).
  assert (Hci : RG0d.AR_client_img_law segs B) by (destruct LAWS; assumption).
  destruct (Hfl ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin) as (_ & Happ & Hby & _).
  rewrite EF3, Hfsb in Happ, Hby.
  assert (Hnimg : forall x, fr <= x < fr + 4096 -> ~ RG0d.in_img segs x).
  { intros x Hx. refine (proj2 (Hci ly3 S3 W3 mem3 md3 x HAR _)). right; left.
    exists 6, (ACtlCut.c_fpos cx). split; [exact Hin|]. rewrite EF3, Hfsb. lia. }
  unfold RG0f.in_app, RG0f.kLowShadowBeg, RG0f.kHighMemBeg in Happ.
  unfold ACtlCutP.FRAME_BYTES in HfrA. unfold ART.APPMEM_END in Hcapp.
  assert (Hfr64 : 0 < fr < 2 ^ 64) by lia.
  assert (Hfr_img : fr + 8 <= 0x10000 \/ 0x5fe000 <= fr).
  { destruct (Z_le_gt_dec (fr + 8) 0x10000) as [H1|H1]; [left; exact H1|].
    destruct (Z_le_gt_dec 0x5fe000 fr) as [H2|H2]; [right; exact H2|].
    exfalso. apply (Hnimg (Z.max fr 0x10000)); [lia | apply jr_img_in; lia]. }
  (* the header range [fr, fr + 8) is visible, present and writable *)
  assert (Hvis : PB.range_visible (RA0n.w_H W3) fr 8).
  { split; [lia|]. split; [lia|]. intros a Ha. exact (proj1 (proj1 (Hby a ltac:(lia)))). }
  assert (HRW : LST.rw_cells A.Img0.rsegs mem3 fr [LCE.C8 (Z_to_bv 64 0x41b58ab3)]).
  { split.
    - split; [exact (conj I I) |]. cbn [LCE.cells_bytes LCE.cbytes]. rewrite app_nil_r. exact Qhdr.
    - split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi.
      destruct (proj2 (proj1 (Hby (fr + i) ltac:(lia)))) as (b & Eb).
      unfold wview, LMM.wa. rewrite Eb. discriminate. }
  assert (HSTK0 : LFR.stk A.Img0.rsegs mem3 0 0).
  { split; [lia|]. split; [lia|]. intros a Ha. lia. }
  (* G3: the cut's configuration in state form, then the walk moved to the run's canonical map. *)
  rewrite PB.cfg_at_MS.
  change (ACtlCut.cut_pc C_Jrel) with 0x82b80.
  apply (RA0nR.SRr_xregs_eqv segs W3 (LR6.mkR_of regs3) regs3 RK11.fp_regs
           (Z_to_bv 64 0x82b80) RK11.fp_csr None mem3 (RK11.seg_rom segs) md3 (POST cx));
    [| exact (LR6.xregs_eqv_sym _ _ (LR6.mkR_of_eqv regs3))].
  (* G4: the run at the site footprint, lifted with the hidden-bytes form of the lift (it writes memory). *)
  pose proof (@YTF.jrel_evt_side_F (AK11.mkFP RK11.fp_regs RK11.fp_csr) (PB.RNG_W (RA0n.w_H W3))
    (reg_get regs3 1) (reg_get regs3 2) (reg_get regs3 3) (reg_get regs3 4) (reg_get regs3 5) (reg_get regs3 6)
    (reg_get regs3 7) (reg_get regs3 8) (reg_get regs3 9) (reg_get regs3 10) (reg_get regs3 11) (reg_get regs3 12)
    (reg_get regs3 13) (reg_get regs3 14) (reg_get regs3 15) (reg_get regs3 16) (reg_get regs3 17)
    (reg_get regs3 18) (reg_get regs3 19) (reg_get regs3 20) (reg_get regs3 21) (reg_get regs3 22)
    (reg_get regs3 23) (reg_get regs3 24) (reg_get regs3 25) (reg_get regs3 26) (reg_get regs3 27)
    (reg_get regs3 28) (reg_get regs3 29) (reg_get regs3 30) (reg_get regs3 31)
    mem3 fr 0 0 R21 R22 Hfr64 HRW HSTK0 (PB.rng_of_visible _ _ _ Hvis)) as HRUN.
  pose proof (PB.fevt_of_evtF _ _ _ HRUN) as HFS.
  rewrite <- PB.tfibsegs_rsegs in HFS.
  apply (RA0nR.SRr_fevt_hid segs A.ACtlG.Kit.kit_wx W3 _ md3 (PB.RNG_W (RA0n.w_H W3)) _ (POST cx) HFS).
  { apply PB.fp_avoids_RNG_W. }
  (* G5: the continuation at the run's end state; the exit cut is taken at its own map R. *)
  intros ms' md' HQ0 Hhid Hsbm.
  destruct HQ0 as (m' & Ems & MU & WM & Hhdr & _).
  subst ms'.
  assert (Hhid' : forall x : word, RA0n.w_H W3 x = true -> m' x = mem3 x) by exact Hhid.
  clear Hhid.
  match goal with |- RA0n.SRr _ _ (mkCfg (LMS.MS ?R0 _ _ _ _ _ _) _) _ => set (R := R0) end.
  change (RA0n.SRr segs W3 (RG0d.cfg_at segs (ACtlCut.cut_pc C_A82b9c) R m' md') (POST cx)).
  assert (K2 : RK11.getr R 2 = RK11.getr regs3 2) by reflexivity.
  assert (K3 : RK11.getr R 3 = RK11.getr regs3 3) by reflexivity.
  assert (K4 : RK11.getr R 4 = RK11.getr regs3 4) by reflexivity.
  assert (K8 : RK11.getr R 8 = RK11.getr regs3 8) by reflexivity.
  assert (K9 : RK11.getr R 9 = RK11.getr regs3 9) by reflexivity.
  assert (K19 : RK11.getr R 19 = RK11.getr regs3 19) by reflexivity.
  assert (K26 : RK11.getr R 26 = RK11.getr regs3 26) by reflexivity.
  assert (K10 : RK11.getr R 10 = Z_to_bv 64 fr) by reflexivity.
  assert (K11 : RK11.getr R 11 = Z_to_bv 64 3136) by reflexivity.
  (* the header window is outside the image, the shadow and every other carried range *)
  assert (Hout : forall x : word, ~ (fr <= bv_unsigned x < fr + 8) -> m' x = mem3 x).
  { intros x Hx. apply MU. cbn [LFR.outside]. split; [exact Hx | exact I]. }
  apply (HX cx [] fr k ly3 S3 W3 R m' md' HB).
  - (* journal: ajournal_exec over the write set [fr, fr + 8) *)
    eapply (RCbq.ajournal_exec segs B LAWS A.ACtlG.Kit.kit_segs_low) with (Wr := fun a => fr <= a < fr + 8).
    + exact HJ.
    + intros x Hx. unfold RK04.mrestrict. rewrite (Hout x Hx). reflexivity.
    + intros x Hx. unfold RK04.mrestrict in *. destruct (RA0n.w_H W3 x) eqn:Ehx; [exact Hx|].
      destruct (Z_le_gt_dec fr (bv_unsigned x)) as [Hx1|Hx1];
        [destruct (Z_lt_ge_dec (bv_unsigned x) (fr + 8)) as [Hx2|Hx2]|].
      * destruct Hhdr as (_ & _ & Hb).
        pose proof (Hb (Z.to_nat (bv_unsigned x - fr)) ltac:(rewrite LMM.length_le8; lia)) as Hbx.
        rewrite Z2Nat.id in Hbx by lia.
        replace (fr + (bv_unsigned x - fr)) with (bv_unsigned x) in Hbx by lia.
        unfold LMM.wa in Hbx. rewrite stdpp.bitvector.definitions.Z_to_bv_bv_unsigned in Hbx.
        destruct (nth_error (LMM.le8 (Z_to_bv 64 0x45e0360e)) (Z.to_nat (bv_unsigned x - fr))) as [b|] eqn:Enb.
        -- rewrite (jr_mem_of_mrd m' x b ltac:(apply Hnimg; lia) Hbx). discriminate.
        -- apply nth_error_None in Enb. rewrite LMM.length_le8 in Enb. lia.
      * rewrite (Hout x ltac:(lia)). exact Hx.
      * rewrite (Hout x ltac:(lia)). exact Hx.
    + exact Hhid'.
    + exact Hsbm.
    + intros a Ha. right; right; right. exists 6, (ACtlCut.c_fpos cx). split; [left; reflexivity|].
      left. hnf. cbn [fst snd]. rewrite EF3, Hfsb. lia.
  - (* frames: own6 on both cuts *)
    exact HF.
  - (* the frame law: own6 on both cuts *)
    exact HL.
  - (* the event bound: EV_LLVMF on both cuts *)
    exact Hk.
  - (* the exit body, C_A82b9c (ACtlCutP.v C_A82b9c) *)
    cbv beta iota delta [ACtlCut.cut_body ACtlCutP.C_A82b9c].
    split; [exact HP|].
    split.
    { exists A, sp.
      split; [rewrite K2; exact R2|]. split; [exact Hsp16|].
      split; [unfold RG0d.spZ in *; rewrite K2; exact Hspz|].
      split; [rewrite K4; exact R4|].
      split; [unfold ACtlCut.rgv; rewrite K8; exact R8|].
      split; [unfold ACtlCut.rgv; rewrite K9; exact R9|].
      split; [rewrite K3; exact R3|].
      split; [unfold ACtlCut.rgv; rewrite K19; exact R19|].
      split; [unfold ACtlCut.rgv; rewrite K26; exact R26|].
      split; [exact Hfr32|]. split; [exact HA32|]. split; [exact HAc|]. split; [exact HspA|].
      split; [unfold ACtlCutP.FRAME_BYTES; exact HfrA|]. split; [exact HA416|]. split; [exact Hsplo|].
      split; [unfold ART.APPMEM_END; exact Hcapp|].
      split; [apply (jr_q64_keep mem3 m' fr (fr + 8) (A + 304) fr Q304 MU); lia|].
      split; [exact Hhdr|].
      split; [apply (jr_q64_keep mem3 m' fr (fr + 8) (fr + 16) A.ACfn.A_LLVMF Q16 MU); lia|].
      split.
      { destruct Hsh as (sh & Hsh1 & Hsh2). exists sh. split; [|exact Hsh2].
        apply (LFR.bytes_at_transport segs [(fr, fr + 8)] mem3 m' _ sh Hsh1 MU).
        cbn [LFR.disjoint_from]. rewrite Hsh2.
        change (Z.of_nat (Z.to_nat ACtlCutP.FRAME_SHADOW)) with 392.
        unfold ACtlCutP.Sfr, ART.shadow_addr, ART.ASAN_K.
        pose proof (Z.div_mod fr 8 ltac:(lia)). pose proof (Z.mod_pos_bound fr 8 ltac:(lia)).
        split; [lia | exact I]. }
      split.
      { apply (LFR.bytes_at_transport segs [(fr, fr + 8)] mem3 m' _ _ Hsaved MU).
        cbn [LFR.disjoint_from]. rewrite jr_saved_len. split; [lia | exact I]. }
      (* Batch3's fake-frame trailer word at fr + 4088: the run writes only the header [fr, fr + 8). *)
      apply (jr_q64_keep mem3 m' fr (fr + 8) (fr + 4088) _ Htrl MU); lia. }
    split; [reflexivity|].
    split; [unfold ACtlCut.a0v, ACtlCut.rgv; exact K10|].
    unfold ACtlCut.rgv, ACtlCutP.FRAME_BYTES. exact K11.
  - (* ctl_rt_C across the header store; the state stays ly3 S3, so each region is the entry's *)
    (* every shadow byte lies outside the app-memory header, whatever region names it *)
    assert (Hkeep : forall Pr : Z -> Prop, A.ShadowRwOn.shadow_rw_on Pr mem3 -> A.ShadowRwOn.shadow_rw_on Pr m').
    { intros Pr Hon a HRg Ha. destruct (Hon a HRg Ha) as (Hw & b & Hb).
      unfold ART.in_shadow, ART.LOWMEM_END, ART.LOWSHADOW_END, ART.HIGHSHADOW_BEG, ART.HIGHMEM_BEG in Ha.
      assert (Ea : m' (LMM.wa a) = mem3 (LMM.wa a)).
      { apply Hout. rewrite LMM.wa_unsigned by lia. lia. }
      split.
      * unfold wview in *. rewrite Ea. exact Hw.
      * exists b. unfold LMM.mrd in *. rewrite Ea. exact Hb. }
    split; [|split; [|split]].
    + (* the runtime cells are image bytes, the header is not *)
      apply (jr_cells_keep mem3 m'); [|exact Hcells].
      intros x Hx. apply Hout. lia.
    + exact (Hkeep _ Hcut).
    + exact (Hkeep _ Himg).
    + (* a read-only byte is an image byte, never a header byte *)
      intros x Hx.
      destruct (Z_le_gt_dec fr (bv_unsigned x)) as [Hx1|Hx1];
        [destruct (Z_lt_ge_dec (bv_unsigned x) (fr + 8)) as [Hx2|Hx2]|].
      * exfalso. unfold LMM.ro_addr in Hx.
        destruct (find_segment A.Img0.rsegs (bv_unsigned x) 1) as [sg|] eqn:Ef; [|discriminate].
        destruct (RK04.find_segment_some_spec _ _ _ _ Ef) as (Hs & Hb1 & Hb2).
        apply (Hnimg (bv_unsigned x)); [lia|]. exists sg. split; [exact Hs | lia].
      * pose proof (Hro x Hx) as E. unfold LMM.mrd in E |- *. rewrite (Hout x ltac:(lia)). exact E.
      * pose proof (Hro x Hx) as E. unfold LMM.mrd in E |- *. rewrite (Hout x ltac:(lia)). exact E.
Qed.

End GlueJrel.
