(* lib/A/ACtlG/P11.v -- GLUE for stage seg_P11 of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput
   (lib/A/ACtl.v:733).  Written by a Theorem Labs lane; single writer.  rule 24: no function proved
   (kind: segment lemma).  Pattern: glue-pattern.md (a working note, not in this delivery), shape of
   the pilot lib/A/ACtlG/A5.v.
   REUSE SEARCH (FREE-PIECES rule 17; `proof-index glue_seg_P11 seg_P11`, index built 2026-10-29T07:26:27Z, run 07:34Z,
   output reuse-P11.txt): glue_seg_P11: 0 named, 0 by address, 0 related,
   0 released, the delivered package 0; declared only on this branch (a working branch). seg_P11: 0 released; no match in the
   delivered proofs; its working-branch hits are the stage hypothesis (ACtl.v) and source lemma
   (Seg/P11.v, image B twin) this file builds on.  Written new.
   At ossv/recipes c5e779efe8c (2026-10-31), glue_seg_P11 and seg_P11 are defined only in this unit (glue_seg_P11 in
   this file; seg_P11 at the stage hypotheses lib/A/ACtl.v:733 and lib/B/ACtl.v:508, the source lemmas lib/A/Prog/Seg/P11.v:231 and
   lib/B/Prog/Seg/P11.v:184, and image B's lib/B/ACtlW3b.v:2022).

   WHAT IT PROVES
     glue_seg_P11 : forall POST, CF POST C_A81c84 -> CF POST C_A81c60
   with ACtl.v's own CF notation (SK := A.AE2k.tfib_sink_head, FP := []), i.e. exactly ACtl.v:550's Section
   hypothesis seg_P11.  Segment P11 is 0x81c60 -> 0x81c80, nine instructions and the call of
   reac_ctrl_kind_name@0x8351c with x = 14, which returns QMARK and writes only its 16-byte stack window
   [sp - 16, sp) (Seg/P11.v:1-28).

   THE RUN: lib/A/Prog/Seg/P11F.v p11_evt_F_on (a Theorem Labs lane's route (C) twin of p11_evt_F, a Theorem Labs lane's mechanical
   re-run of Seg/P11.v p11_evt:171; p11_evt_F's statement without the premise shadow_rw m), Required qualified.
   Its first premise is the callee's footprint contract reac_ctrl_kind_name_contract_F_on (a Theorem Labs lane,
   lib/A/Prog/reac_ctrl_kind_name_c.v; no shadow premise: its region R is empty); it is DISCHARGED here, not
   assumed, by the proved closed theorem A.Prog.reac_ctrl_kind_nameF.reac_ctrl_kind_name_holds_F_on
   (a Theorem Labs lane, lib/A/Prog/reac_ctrl_kind_nameF.v:13).
   MEASURED FINDING (this lane, build-20261029T043157Z rc=0): that file DOES compile on the v1.9 base --
   A.AsanRT.shadow_addr A.Prog.reac_ctrl_kind_name_c.KIND_NAME vm_computes to 2147532012 (KIND_NAME =
   0x9e760 = 649056, 649056 / 8 = 81132, + ASAN_K 2147450880), which is exactly the literal its line 16
   uses.  The note in P11F.rng.tsv (a working note, not in this delivery) / F7F.v (not in this delivery) / F8F.v (not in this delivery) ("does not compile on v1.9; v1.9's shadow_addr
   KIND_NAME = 2147531948") is arithmetically wrong.  Confirmed by a Theorem Labs lane 04:3xZ; lifted-callee rule
   per a Theorem Labs lane 04:39Z (a LIFTED callee's contract_F premise is discharged by its proved closed theorem;
   <f>_SRr_at is for split sites only, and itself takes contract_F).

   THE PROOF, step by step (glue-pattern.md section 3)
   G1  unfold the entry cut C_A81c60 (ACtlCutP.v:1923-1934), 17 conjuncts.
   G2  the run's premises.  Registers from the body (a0 = -1) and from FRAC (s1 = A, sp).  Memory: the XC
       spill [A + 280] = fr + 3040 and the cleared code byte at fr + 3040 from the body; the kind-name
       table bytes from the core pre's arodata_okS carried to the cut by the journal's image conjunct
       (YCbq.v:362); the kind-name strings from ctl_rt_C's ro_agree (Seg/P11.v:116 p11_strings); the callee
       stack window's presence (stk) from the journal's presence conjunct (YCbq.v:368); addressable of the
       table from the zero shadow (ARm's am_zshadow at B's as_zero_shadow row (0x20ec0, 0xa4380 - 0x20ec0),
       AF0m.v:280 through TFIB_SYMS's ts_zsh).  Footprints: ProgBridge.img_vis_W (the image range),
       ProgWorldVisWin.win_vis (the two stack ranges), ProgWorldVisFrame.frame_vis (the code byte in the
       class-6 frame) and the zero shadow again (the 14 shadow bytes of the table).
       All numeric bounds come from VISIBLE state: 4096 <= fr and the frame's ceiling from
       YCbq.frames_bounds, alloc_ceiling + LLVMF_STK <= c_sp cx from the journal's astk_ok (YCbq.v:333-335),
       c_sp cx - 4096 < sp <= A <= c_sp cx < APPMEM_END from FRAC.
   G3  register maps: ProgBridge.cfg_at_MS, then YA0nR.SRr_xregs_eqv from the cut's map regs3 to the run's
       canonical one (Regs6ss.mkR_of regs3 = mkR (getr regs3 1) .. (getr regs3 31)).
   G4  lift: ProgBridge.fevt_of_evtF, ProgBridge.tfibsegs_rsegs, then YA0nR.SRr_fevt_hid (the run WRITES
       memory, so the journal needs the hidden-bytes premise) at RNG := ProgBridge.RNG_W (w_H W3).
   G5  the continuation at the run's end map R and memory m':
         journal  YCbq.ajournal_exec with Wr := the callee window [sp - 16, sp), whose awr_byte case is the
                  stack one (c_sp cx - LLVMF_STK <= sp - 16 and sp <= c_sp cx);
         frames, frame law, k bound  unchanged (own6 and kmax 14 on both cuts);
         body     the register conjuncts hold by conversion (the end map's kept slots are literally
                  getr regs3 i); every memory conjunct moves across the callee's munch, because every
                  address it names is either below alloc_ceiling (the frame, the image, the shadow) or at
                  A + off / c_sp cx - 104 with A >= sp (the spill area), and the window is [sp - 16, sp);
                  addressable moves by AsanRTFacts.addressable_kept over munch_meta (the window is
                  application memory, so no shadow byte changes);
         ctl_rt_C the exit cut keeps the entry's state (ly3, S3), so its regions do not move: asan_cells by
                  AsanRTFacts.asan_cells_kept, the two shadow regions (cut_shadow B ly3 S3 and img_shadow) by
                  ShadowRwOnT.shadow_rw_on_kept, ro_agree because a read-only address lies in the image,
                  below the window.

   SECTION HYPOTHESES (exact text at the declarations below)
   - LAWS : the core's AR law record, ACtl.v:183's own hypothesis (frames_bounds, ajournal_exec,
     al_blocks, the visibility lemmas).
   - TFIB_SYMS : A.AF0m.CtrlTSyms B, ACtl.v:191's own hypothesis (ts_zsh for the zero-shadow row,
     ts_owned / ts_errno for the journal's image conjunct).
  - RELRO_KIND_NAME : ACtl.v's own hypothesis (ACtl.v:204 at d36efc6152d, same name and text): the kind-name table
    [0x9e760, 0x9e760 + 112) lies in the core pre's read-only span [RLO, RHI).  (This lane's RELRO_KN before Batch3.)

   FROM THE SHARED KIT lib/A/ACtlG/Kit.v (Required, never copied): kit_wx (SRr_fevt_hid's premise) and
   kit_segs_low (ajournal_exec's premise).  kit_frac_move is not needed: the run's end map keeps every
   register FRAC reads as the literal getr regs3 i, so FRAC's register conjuncts hold by conversion.

   CLOSURE: every Require below is qualified (no Import / Export of a project module); no statement here
   names a frame-route identifier.  EVERY project name is written from the lib root (lib.Reusable.X,
   lib.Lib.X, lib.A.X, lib.Prog.X) and Required from its directory: this file's closure reaches ctrl's
   ASan-side copies (lib/A/Reusable/YP09, YK04 ..., lib/A/Bz/Lib/Mem, Frame ...) through Seg/P11F.v, so a
   partial name such as Reusable.YP09.mbyte or Lib.Mem.wa resolves to the WRONG copy (measured: it did, at
   this lane's builds 3-11; porter a Theorem Labs lane 04:24Z / 04:33Z for the six twins).  Measured closure (a Theorem Labs lane's
   fclosure.py at e42c431c851): 577 files; no lib/AZ/AsanW (not in this delivery), no W6, no SegCF / *_cfw file, not lib/A/AD2l.v;
   its lib/AZ files are AZ/Lib/{Cells,Exec,FP,Frame,LiaHints,LiaOrc,LiaTuning,MState,Mem,PropExec,Step,StepDiet,
   ZBridge,ZifyLit} (not in this delivery) (the frame route's, reached through Seg/P11F.v, closure rule 1), AZ/LibA/AcctCore and
   AZ/Spec/{AsanCtrl,AsanCtrlProps,STree}.  The frame-route blobs are the v1.9 blobs of record (listed in the
   commit message of f13e09aa792).
   NOT USED, because they do not compile on this base (core errors, reported): lib/A/ACeg.v:24
   (port_core_refused_103b0 undefined, not in the workspace patch list) and lib/A/AB1h.v:50 (its segment
   table says 0x9e000 has size 8192; the image's is 12288).  ProgWorld.v / ProgWorldShadow.v are not on
   this base; the two facts this file needs from them (aview at a visible address is mrd; the zero shadow of
   an as_zero_shadow row or a constant shadow cell is addressable) are proved locally below (p11g_aview_mrd,
   HSHB / HADDR).  SHADOW ROWS ARE FOUND BY COMPUTATION, NEVER BY POSITION (a Theorem Labs lane 05:52Z): a byte's shadow
   comes from the first zero-shadow row of A.AF0m.Tfib_zero_shadow that covers it, or from a constant shadow
   cell z1 (ANum (shadow_addr a)) v of A.AF0m.Tfib_const with shadow_ok a v (p11g_shb, decided by vm_compute).
   On the planning list the kind-name table and QMARK lie in the row (0x20ec0, 0xa4380 - 0x20ec0); on a Theorem Labs lane's
   record list (a working branch e56483f863b, AF0m.v:2955-2964) the table lies in
   (0x21aa0, 0x9e7d0 - 0x21aa0) and QMARK in NO zero row: its granule's shadow is the constant cell
   z1 (ANum 0x7fffc23c) 0x2 (AF0m.v:2179 there).  The same proof checks on both.
   FRAC AT THE NEW MEMORY (the only place this file re-establishes FRAC / FRAHC: the exit body, after the
   kind_name call) is a generic conjunct walk (p11g_walk): a register or arithmetic conjunct is carried
   unchanged, a byte conjunct moves across the callee's window by Frame.bytes_at_transport; it needs no edit
   when FRAC gains a trailer conjunct inside [fr, fr + 4096) (the frame is fs_frame_bytes 6 = 4096 bytes and
   lies below alloc_ceiling, so below the window).

   SHADOWED NAMES: getr / mkst / seg_rom / cfg_at are lib.Reusable.YK11 / lib.Reusable.YG0d-qualified.

   BUILD STATE (honest): TYPE-CHECK WITH WORKSPACE STAND-INS (provisional): gbuild.sh on a build machine workspace
   (internal path) (FACTS ed6b6b7b0ab + PAU pau-libreac-v190), base a working branch 46eb24cd4b3
   merged; the closure reaches lib/A/AE2k.v, lib/A/AF0l.v and lib/A/AF0m.v, whose port_core_refused_* names the workspace
   patches.  Print Assumptions glue_seg_P11: Rocq primitives (PrimInt63, PrimString, PrimArray) and
   functional_extensionality_dep only; no CtrlB_syms (AD2l is not in the closure).  No Axiom, no
   Parameter, no Admitted, no admit. *)

From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YK1b YM05 YO09 YI16 YI04.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YA0n YA0nR YK04 YG00 YG01 YG0f.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YG0n YG0d YG0v YC5d YCbq YE01 YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require AB1v ACfn AE2k AF0m Img0 AsanRT AsanRTFacts ACtlK.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require ACtlCut ACtlCutP ProgBridge ProgWorldVisWin ProgWorldVisFrame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require ShadowRwOn ShadowRwOnT ACtlRtC.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require MemNorm MemNormTr BzBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlG Require Kit.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require ImgBounds SlotModel reac_ctrl_kind_name_c reac_ctrl_kind_nameF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require P11 P11F.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcIdentModel.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require ExecF MState Regs6ss Mem Frame PropExec.
Import ListNotations.
Local Open Scope Z_scope.

(* The core's segment list, as lib.A.ACtlCut.v:74 and ACtl.v:163 bind it. *)
Local Notation segs := lib.A.AB1v.tfibsegs.

(* ---------------------------------------------------------------------------------------------------------
   Local bridge lemmas (proof-internal; no glue statement names a frame-route identifier).  They say the one
   thing the cut layer's reader (the core's aview over the world's hidden set) and ctrl's byte reader
   (lib/Lib/Mem's mrd over the image) have in common at a VISIBLE address.  Same content as
   lib/A/ProgWorld.v's aview_vis_mrd, which does not compile on this base (its closure reaches
   lib/A/AE2k.v's port_core_refused_* names), restated over the two readers this file uses. *)

Section P11gBridge.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.

Lemma p11g_segrom_eq : forall a, lib.Reusable.YK11.seg_rom segs a = lib.Lib.PropExec.seg_rom lib.A.Img0.rsegs a.
Proof. reflexivity. Qed.

Lemma p11g_mbyte_mrd : forall (H : word -> bool) (m : word -> option byte) (a : Z),
  H (Z_to_bv 64 a) = false ->
  lib.Reusable.YP09.mbyte segs (lib.Reusable.YK04.mrestrict H m) a = lib.Lib.Mem.mrd lib.A.Img0.rsegs m (lib.Lib.Mem.wa a).
Proof.
  intros H m a Hh. unfold lib.Reusable.YP09.mbyte, lib.Reusable.YK04.mrestrict, lib.Lib.Mem.mrd, lib.Lib.Mem.wa.
  rewrite Hh. destruct (m (Z_to_bv 64 a)) as [b|]; [reflexivity | apply p11g_segrom_eq].
Qed.

Lemma p11g_aview_mrd : forall (H : word -> bool) (m : word -> option byte) (a : Z),
  H (Z_to_bv 64 a) = false ->
  lib.Reusable.YG0n.aview segs H m a
    = option_map (fun b : byte => bv_unsigned b) (lib.Lib.Mem.mrd lib.A.Img0.rsegs m (lib.Lib.Mem.wa a)).
Proof.
  intros H m a Hh. unfold lib.Reusable.YG0n.aview.
  f_equal. exact (p11g_mbyte_mrd H m a Hh).
Qed.

Lemma p11g_opt_inj : forall x y : option byte,
  option_map (fun b : byte => bv_unsigned b) x = option_map (fun b : byte => bv_unsigned b) y -> x = y.
Proof.
  intros [a|] [b|] H; cbn in H; try discriminate H; [|reflexivity].
  injection H as H. f_equal. apply bv_eq. exact H.
Qed.

(* A read-only address of the image lies inside the loaded image (so, below the machine stack). *)
Lemma p11g_ro_low : forall a : word, lib.Lib.Mem.ro_addr lib.A.Img0.rsegs a = true -> bv_unsigned a < 0x5fe000.
Proof.
  intros a Ha. destruct (Z_lt_le_dec (bv_unsigned a) 0x5fe000) as [h | h]; [exact h |].
  exfalso. unfold lib.Lib.Mem.ro_addr in Ha.
  destruct (find_segment lib.A.Img0.rsegs (bv_unsigned a) 1) as [s | ] eqn:E; [| discriminate Ha].
  destruct (lib.A.BzBridge.find_segment_below lib.A.Img0.rsegs lib.A.Prog.ImgBounds.IMG_HI (bv_unsigned a) 1 s
              lib.A.MemNormTr.rsegs_below_img E ltac:(lia)) as [L | L];
    [unfold lib.A.Prog.ImgBounds.IMG_HI in L; lia | discriminate L].
Qed.

(* No image segment reaches an address at or above IMG_HI = 0x5fe000 (the machine stack lies there). *)
Lemma p11g_noseg : forall x : word, 0x5fe000 <= bv_unsigned x ->
  find_segment lib.A.Img0.rsegs (bv_unsigned x) 1 = None.
Proof.
  intros x Hx. destruct (find_segment lib.A.Img0.rsegs (bv_unsigned x) 1) as [s | ] eqn:E; [| reflexivity].
  destruct (lib.A.BzBridge.find_segment_below lib.A.Img0.rsegs lib.A.Prog.ImgBounds.IMG_HI (bv_unsigned x) 1 s
              lib.A.MemNormTr.rsegs_below_img E ltac:(lia)) as [L | L];
    [unfold lib.A.Prog.ImgBounds.IMG_HI in L; lia | discriminate L].
Qed.

(* A byte that memory holds is in the writable view (lib/Lib/Mem.v:253-257's step, isolated). *)
Lemma p11g_wview_some : forall (m : word -> option byte) (x : word) (b : byte),
  m x = Some b -> wview lib.A.Img0.rsegs m x <> None.
Proof. intros m x b H. unfold wview. rewrite H. discriminate. Qed.
End P11gBridge.

(* ---- shadow rows decided by computation (no row named by position) ---- *)
Definition p11g_num (e : lib.Reusable.YG0f.aexp) : option Z :=
  match e with lib.Reusable.YG0f.ANum z => Some z | _ => None end.

Lemma p11g_num_some : forall e z, p11g_num e = Some z -> e = lib.Reusable.YG0f.ANum z.
Proof. intros e z H. destruct e; cbn in H; try discriminate H. injection H as ->. reflexivity. Qed.

(* a constant one-byte shadow cell at shadow_addr a whose value v makes byte a addressable *)
Definition p11g_cellb (a : Z) (c : lib.Reusable.YG0f.acell) : bool :=
  match p11g_num (lib.Reusable.YG0f.c_at c), lib.Reusable.YG0f.c_w c, lib.Reusable.YG0f.c_val c with
  | Some s, 1%nat, lib.Reusable.YG0f.AV e =>
      match p11g_num e with
      | Some v => (s =? lib.A.AsanRT.shadow_addr a) && (0 <=? v) && (v <? 128) &&
                  ((v =? 0) || ((a mod 8 <? v) && (v <=? 7)))
      | None => false
      end
  | _, _, _ => false
  end.

(* byte a's shadow is known: a zero-shadow row covers a, or a constant shadow cell gives it *)
Definition p11g_shb (ly : lib.Reusable.YG0f.alayout) (a : Z) : bool :=
  existsb (fun r => (fst r <=? a) && (a <? fst r + 8 * (snd r / 8))) lib.A.AF0m.Tfib_zero_shadow
  || existsb (p11g_cellb a) (lib.A.AF0m.Tfib_const ly).

Lemma p11g_le_byte1 : forall v, 0 <= v < 256 -> lib.Reusable.YG0f.le_byte v 1 0 = v.
Proof.
  intros v Hv. unfold lib.Reusable.YG0f.le_byte.
  change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
  change (2 ^ 8) with 256. rewrite (Z.mod_small v 256) by lia. rewrite (Z.mod_small v 256) by lia.
  reflexivity.
Qed.

(* same statement and proof as a Theorem Labs lane's ProgWorldShadow.pwsh_byte_signed_small (not on this base) *)
Lemma p11g_signed_small : forall b : byte, bv_unsigned b < 128 -> bv_signed b = bv_unsigned b.
Proof.
  intros b H. pose proof (bv_unsigned_in_range 8 b) as R.
  unfold bv_signed. apply bv_swrap_small. change (bv_half_modulus 8) with 128. lia.
Qed.

(* ---- the generic FRAC walk: carry each conjunct of a FRAC hypothesis at mem3 to the goal at m' ---- *)
Ltac p11g_side :=
  first [ right; lia
        | left; rewrite ?lib.Lib.Mem.length_le8; lia
        | left; unfold lib.A.ACtlCutP.Sfr, lib.A.AsanRT.shadow_addr, lib.A.AsanRT.ASAN_K,
            lib.A.ACtlCutP.FRAME_SHADOW, lib.A.ACtlCutP.FRAME_BYTES; Z.div_mod_to_equations; lia ].

Ltac p11g_one BAK H :=
  first
  [ exact H
  | lazymatch type of H with
    | ex _ =>
        let sh := fresh "sh" in let Hsh := fresh "Hsh" in let Hl := fresh "Hl" in
        destruct H as (sh & Hsh & Hl); exists sh; split;
        [apply BAK; [exact Hsh | rewrite Hl; p11g_side] | exact Hl]
    end
  | apply BAK; [exact H | p11g_side] ].

Ltac p11g_walk BAK H :=
  lazymatch type of H with
  | _ /\ _ =>
      let H1 := fresh "Fc" in let H2 := fresh "Fs" in
      destruct H as [H1 H2]; split; [p11g_one BAK H1 | p11g_walk BAK H2]
  | _ => p11g_one BAK H
  end.


Section GlueP11.

(* ACtl.v's Section shape (ACtl.v:170-174), restricted to what this stage uses. *)
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {LS : lib.Reusable.YO09.lib_shape}.
Variable B : lib.Reusable.YG0f.asyms.
Variable MT : lib.Reusable.YC5d.ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.

(* ACtl.v's notation block (ACtl.v:182-183, :260-261), verbatim. *)
Local Notation CF POST X :=
  (lib.A.ACtlCut.ctl_from (SK := lib.A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation C_A81c60 := (lib.A.ACtlCutP.C_A81c60 B).
Local Notation C_A81c84 := (lib.A.ACtlCutP.C_A81c84 B).

(* The core's AR law record (YCbq.v:207 Section a0's hypothesis), ACtl.v:183. *)
Hypothesis LAWS : lib.Reusable.YG0d.AR_laws segs B.
(* The core's symbol facts for B, ACtl.v:191. *)
Hypothesis TFIB_SYMS : lib.A.AF0m.CtrlTSyms B.
(* The kind-name table [KIND_NAME, KIND_NAME + 112) = [0x9e760, 0x9e7d0) lies in the core pre's read-only
   span [RLO, RHI) (lib.A.ACfn.tfib_lib_pre_x's arodata_okS, ACfn.v:41).  NEEDED because the table is .data.rel.ro:
   lib/Lib/Mem.ro_addr of those bytes vm_computes to FALSE (measured, this lane), so ctl_rt_C's ro_agree does not
   reach them and the only source of their image value is that span.  This is the companion of ACtl.v:179's
   RELRO_IMG, which is there for the same reason.  TRUE at the instantiation: ACtl.v section 9 fixes RLO / RHI
   at the GNU_RELRO filesz span 0x9e348 / 0xa07c8 (A/ACtlK.v:17), so it is discharged there by `vm_compute; lia`. *)
Hypothesis RELRO_KIND_NAME : RLO <= 0x9e760 /\ 0x9e760 + 112 <= RHI.

Lemma glue_seg_P11 : forall POST, CF POST C_A81c84 -> CF POST C_A81c60.
Proof.
  intros POST HX cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hb Hrt.
  (* ---- G1: the entry cut's body (lib.A.ACtlCutP.v:1923-1934) ---- *)
  cbv beta iota zeta delta [lib.A.ACtlCut.cut_body lib.A.ACtlCutP.C_A81c60] in Hb.
  destruct Hb as (HP & HFRAC & Hn & HOUR & HCUR & HPRO & HS144 & HAD2691 & HS192 & HADfg & HAD2688 &
    HIDB & HFGB & Ha0 & Hcode & HXC & HAD2880).
  pose proof HFRAC as (Av & spv & E2 & Hsp16 & Hspz & E4 & E8 & E9 & E3 & E19 & E26 & Hfr32 & HA32 & HAcsp &
    HspA & HfrA & HA416 & Hsp4096 & HcspApp & Hq304 & Hq24 & Hq16 & Hqhdr & Hqent & Hshw & Hsav).
  pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hos & Hfrs & Hnev & Hk0 & Hkeep9 & Hkeep10 & HimgK & Hfrk &
    Hfpk & Hpres & Hstkok & Hextra & HQT).
  pose proof HB as (HPRE & Hsp1).
  pose proof HPRE as (Hafn & Hra & Hr10 & Hr11 & Hpn & Hnlen & Hgarr & Hfr0 & Hnev0 & Hbbytes & HRO & _).
  (* ---- G2a: the numeric frame ---- *)
  assert (Hin6 : In (6, lib.A.ACtlCut.c_fpos cx) (lib.Reusable.YG01.frames S3)) by (rewrite HF; left; reflexivity).
  destruct (lib.Reusable.YCbq.frames_bounds segs B LAWS ly3 S3 W3 mem3 md3 6 (lib.A.ACtlCut.c_fpos cx) HAR Hin6)
    as (Hf4096 & Hfceil & Hfapp).
  pose proof Hly as (_ & _ & _ & _ & _ & EF & _).
  assert (Efr : fr = lib.Reusable.YG0f.frame_addr (lib.A.ACtlCut.c_ly cx) 6 (lib.A.ACtlCut.c_fpos cx))
    by (apply HL; left; reflexivity).
  assert (Efr3 : lib.Reusable.YG0f.frame_addr ly3 6 (lib.A.ACtlCut.c_fpos cx) = fr)
    by (rewrite Efr; unfold lib.Reusable.YG0f.frame_addr; rewrite EF; reflexivity).
  rewrite Efr3 in Hf4096, Hfceil, Hfapp.
  assert (Hfb6 : lib.Reusable.YG00.fs_frame_bytes 6 = 4096) by reflexivity.
  rewrite Hfb6 in Hfceil.
  destruct Hstkok as (Hsp0m & HSTK0 & Hceilstk & Hstklo & Hsphi & Hstk47 & Hbot & Hsptop & Htophi).
  pose proof (@lib.Reusable.YM05.alloc_ceiling_value rc) as Hacv.
  unfold lib.A.ACfn.LLVMF_STK in Hstklo.
  unfold lib.A.ACtlCutP.FRAME_BYTES in HfrA. unfold lib.A.AsanRT.APPMEM_END in HcspApp.
  unfold lib.A.ACtlCut.rgv in E8, E9, E19, E26, Ha0.
  assert (Esp : bv_unsigned (lib.Reusable.YK11.getr regs3 2) = spv)
    by (unfold lib.Reusable.YG0d.spZ in Hspz; exact Hspz).
  assert (HAv64 : 0 <= Av < 2 ^ 64) by lia.
  (* ---- G2b: visibility ---- *)
  pose proof (lib.A.ProgBridge.img_vis_W W3) as VIMG.
  unfold lib.A.Prog.ImgBounds.IMG_LO, lib.A.Prog.ImgBounds.IMG_HI in VIMG.
  assert (VIS : forall a, 0x10000 <= a < 0x5fe000 -> lib.Reusable.YA0n.w_H W3 (Z_to_bv 64 a) = false)
    by (intros a Ha; exact (proj2 (proj2 VIMG) a ltac:(lia))).
  (* ---- G2c: shadow bytes of image globals: zero-shadow rows and constant shadow cells of B, found by
     computation (p11g_shb), never by position ---- *)
  pose proof (lib.Reusable.YG0n.am_zshadow B ly3 S3 _ (proj1 HAR)) as HZok.
  unfold lib.Reusable.YG0n.zshadow_ok, lib.Reusable.YG0n.zero_shadow_ranges in HZok.
  pose proof (lib.Reusable.YG0n.am_syms B ly3 S3 _ (proj1 HAR)) as Hsyms.
  assert (Hzs : Forall (fun r => 0 <= fst r /\ 0 <= snd r /\ fst r mod 8 = 0 /\ snd r mod 8 = 0 /\
                                 fst r + snd r <= lib.Reusable.YG0f.kLowMemEnd) (lib.Reusable.YG0f.as_zero_shadow B))
    by (destruct Hsyms; assumption).
  assert (HZS : forall r a, In r (lib.Reusable.YG0f.as_zero_shadow B) -> fst r <= a < fst r + 8 * (snd r / 8) ->
      lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W3) mem3 (lib.A.AsanRT.shadow_addr a) = Some 0).
  { intros r a Hr Ha.
    pose proof (proj1 (Forall_forall _ _) HZok r (or_intror Hr)) as Hz. cbv beta in Hz.
    destruct (proj1 (Forall_forall _ _) Hzs r Hr) as (Hr0 & Hs0 & Hr8 & Hs8 & Hlow).
    unfold lib.Reusable.YG0v.zero_shadow in Hz.
    specialize (Hz ((a - fst r) / 8) ltac:(Z.div_mod_to_equations; lia)).
    replace (lib.Reusable.YG0v.shadow_of_addr lib.Reusable.YG0f.SHADOW_OFF (fst r) + (a - fst r) / 8)
      with (lib.A.AsanRT.shadow_addr a) in Hz; [exact Hz|].
    unfold lib.Reusable.YG0v.shadow_of_addr, lib.Reusable.YG0f.SHADOW_OFF, lib.A.AsanRT.shadow_addr,
      lib.A.AsanRT.ASAN_K. Z.div_mod_to_equations. lia. }
  assert (HSHB : forall a, p11g_shb ly3 a = true ->
      exists v, lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W3) mem3 (lib.A.AsanRT.shadow_addr a) = Some v
                /\ 0 <= v < 128 /\ lib.A.AsanRT.shadow_ok a v).
  { intros a Hb. unfold p11g_shb in Hb. apply Bool.orb_true_iff in Hb. destruct Hb as [Hb | Hb].
    - rewrite <- (lib.A.AF0m.ts_zsh B TFIB_SYMS) in Hb.
      apply existsb_exists in Hb as (r & Hr & Hb). apply andb_prop in Hb as [H1 H2].
      apply Z.leb_le in H1. apply Z.ltb_lt in H2.
      exists 0. split; [exact (HZS r a Hr ltac:(lia))|]. split; [lia | left; reflexivity].
    - rewrite <- (lib.A.AF0m.ts_const B TFIB_SYMS ly3) in Hb.
      apply existsb_exists in Hb as (c & Hc & Hb).
      pose proof (proj1 (Forall_forall _ _) (lib.Reusable.YG0n.am_const B ly3 S3 _ (proj1 HAR)) c Hc) as Hch.
      destruct c as [cat cw cval]. unfold p11g_cellb in Hb.
      cbn [lib.Reusable.YG0f.c_at lib.Reusable.YG0f.c_w lib.Reusable.YG0f.c_val] in Hb.
      destruct (p11g_num cat) as [s|] eqn:Es; [|discriminate Hb].
      destruct cw as [|[|cw']]; try discriminate Hb.
      destruct cval as [e|mask v0]; [|discriminate Hb].
      destruct (p11g_num e) as [v|] eqn:Ev; [|discriminate Hb].
      apply p11g_num_some in Es. apply p11g_num_some in Ev. subst cat e.
      repeat rewrite Bool.andb_true_iff in Hb. destruct Hb as (((Hs & H0) & H1) & Hok).
      apply Z.eqb_eq in Hs. apply Z.leb_le in H0. apply Z.ltb_lt in H1.
      unfold lib.Reusable.YG0f.cell_holds in Hch.
      cbn [lib.Reusable.YG0f.c_at lib.Reusable.YG0f.c_w lib.Reusable.YG0f.c_val lib.Reusable.YG0f.aeval] in Hch.
      specialize (Hch 0%nat ltac:(lia)). cbn [Z.of_nat] in Hch. rewrite Z.add_0_r in Hch.
      rewrite (p11g_le_byte1 v ltac:(lia)) in Hch.
      exists v. split; [rewrite <- Hs; exact Hch|]. split; [lia|].
      unfold lib.A.AsanRT.shadow_ok. apply Bool.orb_true_iff in Hok. destruct Hok as [Hok | Hok].
      + left. apply Z.eqb_eq in Hok. exact Hok.
      + right. apply andb_prop in Hok as [Ha1 Ha2]. apply Z.ltb_lt in Ha1. apply Z.leb_le in Ha2. lia. }
  assert (HADDR : forall p n, 0 <= p -> 0 <= n -> p + n <= 0x7fff8000 ->
      forallb (fun i => p11g_shb ly3 (p + Z.of_nat i)) (seq 0 (Z.to_nat n)) = true ->
      lib.A.AsanRT.addressable mem3 p n).
  { intros p n Hp0 Hnn Hpnb Hall. split; [lia|]. split; [lia|].
    split; [unfold lib.A.AsanRT.APPMEM_END; lia|].
    intros i Hi. split; [unfold lib.A.AsanRT.app_mem, lib.A.AsanRT.LOWMEM_END; left; lia|].
    pose proof (proj1 (forallb_forall _ _) Hall (Z.to_nat i) ltac:(apply in_seq; lia)) as Hb.
    cbv beta in Hb. rewrite Z2Nat.id in Hb by lia.
    destruct (HSHB (p + i) Hb) as (v & Hv & Hv128 & Hok).
    assert (Hh : lib.Reusable.YA0n.w_H W3 (Z_to_bv 64 (lib.A.AsanRT.shadow_addr (p + i))) = false)
      by (apply (lib.A.ProgWorldVisFrame.vis_of_aview segs W3 mem3); rewrite Hv; discriminate).
    rewrite (p11g_aview_mrd _ mem3 _ Hh) in Hv.
    destruct (lib.Lib.Mem.mrd lib.A.Img0.rsegs mem3 (lib.Lib.Mem.wa (lib.A.AsanRT.shadow_addr (p + i))))
      as [bb|] eqn:Eb; [|discriminate Hv].
    cbn [option_map] in Hv. injection Hv as Hv.
    exists bb. split; [reflexivity|].
    rewrite (p11g_signed_small bb ltac:(lia)), Hv. exact Hok. }
  assert (HKNb : forallb (fun i => p11g_shb ly3 (lib.A.Prog.reac_ctrl_kind_name_c.KIND_NAME + Z.of_nat i))
                   (seq 0 112) = true) by (vm_compute; reflexivity).
  (* ---- G2d: the kind-name table's bytes, from the core pre's read-only span through the journal ---- *)
  assert (HROa : forall a, 0x10000 <= a < 0x5fb000 -> RLO <= a < RHI ->
      ~ Exists (lib.Reusable.YG0n.in_zr a) (lib.Reusable.YG0f.as_owned_static B) ->
      ~ (lib.Reusable.YG0f.as_errno B <= a < lib.Reusable.YG0f.as_errno B + 4) ->
      lib.Lib.Mem.mrd lib.A.Img0.rsegs mem3 (lib.Lib.Mem.wa a) = lib.Lib.PropExec.seg_rom lib.A.Img0.rsegs (lib.Lib.Mem.wa a)).
  { intros a Ha Hrel Hown Herr.
    assert (Himg : lib.Reusable.YG0d.in_img segs a).
    { assert (V : forall b sz, In (b, sz) (map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_size s))) lib.A.Img0.rsegs) ->
                  b <= a < b + sz -> lib.Reusable.YG0d.in_img segs a).
      { intros b sz Hin Hb. apply in_map_iff in Hin as (s & Es & Hs). injection Es as <- <-.
        exists s. split; [exact Hs | exact Hb]. }
      rewrite lib.A.ProgBridge.rsegs_spans in V.
      destruct (Z_lt_le_dec a 0x30000) as [h1|h1]; [apply (V 0x10000 0x20000); [apply in_eq | lia]|].
      destruct (Z_lt_le_dec a 0x9e000) as [h2|h2]; [apply (V 0x30000 0x6e000); [apply in_cons, in_eq | lia]|].
      destruct (Z_lt_le_dec a 0xa1000) as [h3|h3];
        [apply (V 0x9e000 0x3000); [apply in_cons, in_cons, in_eq | lia]|].
      apply (V 0xa1000 0x55d000); [apply in_cons, in_cons, in_cons, in_eq | lia]. }
    assert (Hsp : lib.Reusable.YCbq.fp_spares (SK := lib.A.AE2k.tfib_sink_head) ([] : list (Z * Z)) a).
    { apply lib.Reusable.YCbq.fp_spares_off. unfold lib.Reusable.YCbq.AOFL_HEAD.
      vm_compute (lib.Reusable.YI16.sk_ofl_head). lia. }
    pose proof (HimgK a Himg Hown Herr Hsp) as Ejrn.
    pose proof (HRO a (or_intror Hrel) Hown Herr) as Erom.
    rewrite Erom in Ejrn. clear Erom.
    rewrite (p11g_aview_mrd (lib.Reusable.YA0n.w_H W3) mem3 a (VIS a ltac:(lia))) in Ejrn.
    rewrite p11g_segrom_eq in Ejrn.
    apply p11g_opt_inj. exact Ejrn. }
  assert (HKNB : lib.Lib.Mem.bytes_at lib.A.Img0.rsegs mem3 lib.A.Prog.reac_ctrl_kind_name_c.KIND_NAME
                   lib.A.Prog.reac_ctrl_kind_name_c.kind_name_bytes).
  { assert (HLn : length lib.A.Prog.reac_ctrl_kind_name_c.kind_name_bytes = 112%nat) by reflexivity.
    split; [unfold lib.A.Prog.reac_ctrl_kind_name_c.KIND_NAME; lia|].
    split; [rewrite HLn; change (Z.of_nat 112) with 112;
            unfold lib.A.Prog.reac_ctrl_kind_name_c.KIND_NAME; lia|].
    intros i Hi. rewrite HLn in Hi.
    rewrite (HROa (lib.A.Prog.reac_ctrl_kind_name_c.KIND_NAME + Z.of_nat i)
      ltac:(unfold lib.A.Prog.reac_ctrl_kind_name_c.KIND_NAME; lia)
      ltac:(unfold lib.A.Prog.reac_ctrl_kind_name_c.KIND_NAME in *; lia)
      ltac:(rewrite (lib.A.AF0m.ts_owned B TFIB_SYMS); intros HE; rewrite Exists_exists in HE;
            destruct HE as (r & Hr & Hzr); unfold lib.A.AF0m.Tfib_owned_static in Hr; cbn [In] in Hr;
            unfold lib.Reusable.YG0n.in_zr in Hzr; cbn [fst snd] in Hzr;
            repeat (destruct Hr as [Hr | Hr]; [subst r; cbn [fst snd] in Hzr;
                     unfold lib.A.Prog.reac_ctrl_kind_name_c.KIND_NAME in *; lia |]); destruct Hr)
      ltac:(rewrite (lib.A.AF0m.ts_errno B TFIB_SYMS); unfold lib.A.AF0m.TFIB_ERRNO,
            lib.A.Prog.reac_ctrl_kind_name_c.KIND_NAME in *; lia)).
    exact (lib.A.Prog.Seg.P11.p11_kn_rom i Hi). }
  (* ---- G2e: the kind-name strings and the stack window ---- *)
  pose proof Hrt as (HAC & Hcut & Himg & HROag).
  assert (HKNS : lib.A.Prog.reac_ctrl_kind_name_c.kind_name_strings mem3)
    by exact (lib.A.Prog.Seg.P11.p11_strings mem3 HROag).
  assert (HSTK : lib.Lib.Frame.stk lib.A.Img0.rsegs mem3
                   (bv_unsigned (lib.Reusable.YK11.getr regs3 2) - lib.A.Prog.reac_ctrl_kind_name_c.REAC_CTRL_KIND_NAME_FRAME)
                   (bv_unsigned (lib.Reusable.YK11.getr regs3 2))).
  { unfold lib.A.Prog.reac_ctrl_kind_name_c.REAC_CTRL_KIND_NAME_FRAME.
    split; [lia|]. split; [lia|]. intros a Ha.
    destruct (Hpres a ltac:(unfold lib.A.ACfn.LLVMF_STK; lia)) as (Hh & bb & Hbb).
    split; [exact (p11g_wview_some mem3 (lib.Lib.Mem.wa a) bb Hbb)|].
    exists bb. unfold lib.Lib.Mem.mrd, lib.Lib.Mem.wa. rewrite Hbb. reflexivity. }
  assert (HOUT : forall x, lib.A.AsanRT.GOT_CELL_K <= x < lib.A.AsanRT.GOT_CELL_K + 8 \/
                   lib.A.AsanRT.CELL_K <= x < lib.A.AsanRT.CELL_K + 8 \/ lib.A.AsanRT.in_shadow x ->
                 lib.Lib.Frame.outside [(bv_unsigned (lib.Reusable.YK11.getr regs3 2) -
                     lib.A.Prog.reac_ctrl_kind_name_c.REAC_CTRL_KIND_NAME_FRAME,
                     bv_unsigned (lib.Reusable.YK11.getr regs3 2))] x).
  { intros x Hx. cbn [lib.Lib.Frame.outside]. split; [|exact I]. intros [H1 H2].
    unfold lib.A.AsanRT.GOT_CELL_K, lib.A.AsanRT.CELL_K, lib.A.AsanRT.in_shadow, lib.A.AsanRT.LOWMEM_END,
      lib.A.AsanRT.LOWSHADOW_END, lib.A.AsanRT.HIGHSHADOW_BEG, lib.A.AsanRT.HIGHMEM_BEG,
      lib.A.Prog.reac_ctrl_kind_name_c.REAC_CTRL_KIND_NAME_FRAME in *. lia. }
  (* ---- G2f: the five footprint ranges ---- *)
  assert (V280 : lib.A.ProgBridge.range_visible (lib.Reusable.YA0n.w_H W3) (Av + 280) 8).
  { apply (lib.A.ProgWorldVisWin.win_vis B lib.A.ACfn.LLVMF_STK (lib.A.ACtlCut.c_sp cx) []
      (lib.A.ACtlCut.c_ly cx) (lib.A.ACtlCut.c_S cx) (lib.A.ACtlCut.c_W cx) (lib.A.ACtlCut.c_mem cx) (lib.A.ACtlCut.c_md cx)
      (lib.A.ACtlCut.own6 cx) ly3 S3 W3 mem3 md3 k (Av + 280) 8 HJ);
      unfold lib.A.ACfn.LLVMF_STK; lia. }
  assert (VWIN : lib.A.ProgBridge.range_visible (lib.Reusable.YA0n.w_H W3)
                   (bv_unsigned (lib.Reusable.YK11.getr regs3 2) -
                    lib.A.Prog.reac_ctrl_kind_name_c.REAC_CTRL_KIND_NAME_FRAME)
                   lib.A.Prog.reac_ctrl_kind_name_c.REAC_CTRL_KIND_NAME_FRAME).
  { unfold lib.A.Prog.reac_ctrl_kind_name_c.REAC_CTRL_KIND_NAME_FRAME.
    apply (lib.A.ProgWorldVisWin.win_vis B lib.A.ACfn.LLVMF_STK (lib.A.ACtlCut.c_sp cx) []
      (lib.A.ACtlCut.c_ly cx) (lib.A.ACtlCut.c_S cx) (lib.A.ACtlCut.c_W cx) (lib.A.ACtlCut.c_mem cx) (lib.A.ACtlCut.c_md cx)
      (lib.A.ACtlCut.own6 cx) ly3 S3 W3 mem3 md3 k _ 16 HJ);
      unfold lib.A.ACfn.LLVMF_STK; lia. }
  assert (VCODE : lib.A.ProgBridge.range_visible (lib.Reusable.YA0n.w_H W3) (fr + 3040) 1).
  { destruct (lib.A.ProgWorldVisFrame.frame_vis B LAWS ly3 S3 W3 mem3 md3 6 (lib.A.ACtlCut.c_fpos cx) (fr + 3040) 1
      HAR Hin6 ltac:(rewrite Efr3; lia) ltac:(rewrite Efr3, Hfb6; lia)) as [Vc _].
    exact Vc. }
  assert (VSH : lib.A.ProgBridge.range_visible (lib.Reusable.YA0n.w_H W3)
                  (lib.A.AsanRT.shadow_addr lib.A.Prog.reac_ctrl_kind_name_c.KIND_NAME) 14).
  { split; [unfold lib.A.AsanRT.shadow_addr, lib.A.AsanRT.ASAN_K, lib.A.Prog.reac_ctrl_kind_name_c.KIND_NAME; lia|].
    split; [unfold lib.A.AsanRT.shadow_addr, lib.A.AsanRT.ASAN_K, lib.A.Prog.reac_ctrl_kind_name_c.KIND_NAME; lia|].
    intros a Ha.
    assert (Ha' : 2147532012 <= a < 2147532012 + 14).
    { unfold lib.A.AsanRT.shadow_addr, lib.A.AsanRT.ASAN_K, lib.A.Prog.reac_ctrl_kind_name_c.KIND_NAME in Ha.
      Z.div_mod_to_equations. lia. }
    pose proof (proj1 (forallb_forall _ _) HKNb (Z.to_nat (8 * (a - 2147532012))) ltac:(apply in_seq; lia)) as Hb.
    cbv beta in Hb. rewrite Z2Nat.id in Hb by lia.
    assert (Ea : lib.A.AsanRT.shadow_addr (lib.A.Prog.reac_ctrl_kind_name_c.KIND_NAME + 8 * (a - 2147532012)) = a).
    { unfold lib.A.AsanRT.shadow_addr, lib.A.AsanRT.ASAN_K, lib.A.Prog.reac_ctrl_kind_name_c.KIND_NAME.
      Z.div_mod_to_equations. lia. }
    destruct (HSHB _ Hb) as (v & Hv & _).
    apply (lib.A.ProgWorldVisFrame.vis_of_aview segs W3 mem3). rewrite <- Ea, Hv. discriminate. }
  (* ---- G3: the cut's configuration as the run's start state, then the register-map move ---- *)
  change (lib.A.ACtlCut.cut_pc C_A81c60) with 0x81c60.
  rewrite lib.A.ProgBridge.cfg_at_MS.
  apply (lib.Reusable.YA0nR.SRr_xregs_eqv segs W3 (lib.Lib.Regs6ss.mkR_of regs3) regs3 lib.Reusable.YK11.fp_regs
           (Z_to_bv 64 0x81c60) lib.Reusable.YK11.fp_csr None mem3 (lib.Reusable.YK11.seg_rom segs) md3 (POST cx));
    [| exact (lib.Lib.Regs6ss.xregs_eqv_sym _ _ (lib.Lib.Regs6ss.mkR_of_eqv regs3))].
  (* ---- G4: the run, then the lift ---- *)
  pose proof (lib.A.Prog.Seg.P11F.p11_evt_F_on lib.A.Prog.reac_ctrl_kind_nameF.reac_ctrl_kind_name_holds_F_on
      (lib.A.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W3))
      (lib.Reusable.YK11.getr regs3 1) (lib.Reusable.YK11.getr regs3 2) (lib.Reusable.YK11.getr regs3 3)
      (lib.Reusable.YK11.getr regs3 4) (lib.Reusable.YK11.getr regs3 5) (lib.Reusable.YK11.getr regs3 6)
      (lib.Reusable.YK11.getr regs3 7) (lib.Reusable.YK11.getr regs3 8) (lib.Reusable.YK11.getr regs3 9)
      (lib.Reusable.YK11.getr regs3 10) (lib.Reusable.YK11.getr regs3 11) (lib.Reusable.YK11.getr regs3 12)
      (lib.Reusable.YK11.getr regs3 13) (lib.Reusable.YK11.getr regs3 14) (lib.Reusable.YK11.getr regs3 15)
      (lib.Reusable.YK11.getr regs3 16) (lib.Reusable.YK11.getr regs3 17) (lib.Reusable.YK11.getr regs3 18)
      (lib.Reusable.YK11.getr regs3 19) (lib.Reusable.YK11.getr regs3 20) (lib.Reusable.YK11.getr regs3 21)
      (lib.Reusable.YK11.getr regs3 22) (lib.Reusable.YK11.getr regs3 23) (lib.Reusable.YK11.getr regs3 24)
      (lib.Reusable.YK11.getr regs3 25) (lib.Reusable.YK11.getr regs3 26) (lib.Reusable.YK11.getr regs3 27)
      (lib.Reusable.YK11.getr regs3 28) (lib.Reusable.YK11.getr regs3 29) (lib.Reusable.YK11.getr regs3 30)
      (lib.Reusable.YK11.getr regs3 31)
      lib.Reusable.YK11.fp_regs lib.Reusable.YK11.fp_csr mem3 Av (fr + 3040)
      (bv_unsigned (lib.Reusable.YK11.getr regs3 2) - lib.A.Prog.reac_ctrl_kind_name_c.REAC_CTRL_KIND_NAME_FRAME)
      E9 Ha0 ltac:(lia) (proj1 HXC Av E9 HAv64) Hcode HKNB HKNS HSTK ltac:(lia)
      ltac:(unfold lib.A.Prog.reac_ctrl_kind_name_c.KIND_NAME,
              lib.A.Prog.reac_ctrl_kind_name_c.REAC_CTRL_KIND_NAME_FRAME in *; lia)
      HAC (HADDR lib.A.Prog.reac_ctrl_kind_name_c.KIND_NAME 112
        ltac:(unfold lib.A.Prog.reac_ctrl_kind_name_c.KIND_NAME; lia) ltac:(lia)
        ltac:(unfold lib.A.Prog.reac_ctrl_kind_name_c.KIND_NAME; lia) HKNb) HOUT
      (lib.A.ProgBridge.rng_of_visible _ _ _ V280) (lib.A.ProgBridge.rng_of_visible _ _ _ VCODE)
      (lib.A.ProgBridge.rng_of_visible _ _ _ VIMG) (lib.A.ProgBridge.rng_of_visible _ _ _ VWIN)
      (lib.A.ProgBridge.rng_of_visible _ _ _ VSH)) as HRUN.
  pose proof (lib.A.ProgBridge.fevt_of_evtF _ _ _ HRUN) as HFS.
  rewrite <- lib.A.ProgBridge.tfibsegs_rsegs in HFS.
  apply (lib.Reusable.YA0nR.SRr_fevt_hid segs lib.A.ACtlG.Kit.kit_wx W3 _ md3
           (lib.A.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W3)) _ (POST cx) HFS).
  { exact (lib.A.ProgBridge.fp_avoids_RNG_W (lib.Reusable.YA0n.w_H W3)). }
  (* ---- G5: the continuation ---- *)
  intros ms' md' HQ0 Hhid Hsbm.
  destruct HQ0 as (a1' & a2' & m' & Ems & MU & WM & ST').
  subst ms'. cbn [ms_mem] in Hhid.
  unfold lib.A.Prog.reac_ctrl_kind_name_c.REAC_CTRL_KIND_NAME_FRAME in MU, ST'.
  rewrite Esp in MU, ST'.
  change (lib.Reusable.YA0n.SRr segs W3
    (lib.Reusable.YG0d.cfg_at segs (lib.A.ACtlCut.cut_pc C_A81c84)
      (lib.Lib.Frame.mkR (Z_to_bv 64 0x81c84) (lib.Reusable.YK11.getr regs3 2) (lib.Reusable.YK11.getr regs3 3)
        (lib.Reusable.YK11.getr regs3 4) (lib.Reusable.YK11.getr regs3 5) (lib.Reusable.YK11.getr regs3 6)
        (lib.Reusable.YK11.getr regs3 7) (lib.Reusable.YK11.getr regs3 8) (lib.Reusable.YK11.getr regs3 9)
        (Z_to_bv 64 lib.A.Prog.reac_ctrl_kind_name_c.QMARK) a1' a2'
        (lib.Reusable.YK11.getr regs3 13) (lib.Reusable.YK11.getr regs3 14) (lib.Reusable.YK11.getr regs3 15)
        (lib.Reusable.YK11.getr regs3 16) (lib.Reusable.YK11.getr regs3 17) (lib.Reusable.YK11.getr regs3 18)
        (lib.Reusable.YK11.getr regs3 19) (lib.Reusable.YK11.getr regs3 20) (lib.Reusable.YK11.getr regs3 21)
        (lib.Reusable.YK11.getr regs3 22) (lib.Reusable.YK11.getr regs3 23) (lib.Reusable.YK11.getr regs3 24)
        (lib.Reusable.YK11.getr regs3 25) (lib.Reusable.YK11.getr regs3 26) (lib.Reusable.YK11.getr regs3 27)
        (lib.Reusable.YK11.getr regs3 28) (lib.Reusable.YK11.getr regs3 29) (lib.Reusable.YK11.getr regs3 30)
        (lib.Reusable.YK11.getr regs3 31))
      m' md') (POST cx)).
  (* transport helpers over the callee's window *)
  assert (MK : lib.A.AsanRTFacts.meta_kept mem3 m').
  { apply (lib.A.AsanRTFacts.munch_meta [(spv - 16, spv)] mem3 m' MU).
    cbn [lib.A.AsanRTFacts.all_app]. split; [|exact I].
    intros a Ha. unfold lib.A.AsanRT.app_mem, lib.A.AsanRT.HIGHMEM_BEG, lib.A.AsanRT.APPMEM_END. right. lia. }
  assert (ADK : forall p nn, lib.A.AsanRT.addressable mem3 p nn -> lib.A.AsanRT.addressable m' p nn)
    by (intros p nn H; exact (lib.A.AsanRTFacts.addressable_kept mem3 m' p nn H MK)).
  assert (BAK : forall a bs, lib.Lib.Mem.bytes_at segs mem3 a bs ->
      (a + Z.of_nat (length bs) <= spv - 16 \/ spv <= a) -> lib.Lib.Mem.bytes_at segs m' a bs).
  { intros a bs Hba Hd.
    apply (lib.Lib.Frame.bytes_at_transport segs [(spv - 16, spv)] mem3 m' a bs Hba MU).
    cbn [lib.Lib.Frame.disjoint_from]. split; [lia | exact I]. }
  assert (HROag' : lib.A.MemNorm.ro_agree lib.A.Img0.rsegs m').
  { intros a Ha. unfold lib.Lib.Mem.mrd.
    rewrite (MU a ltac:(cbn [lib.Lib.Frame.outside]; split; [|exact I];
               pose proof (p11g_ro_low a Ha) as Hro; lia)).
    exact (HROag a Ha). }
  assert (HAeq : forall A0 off, 0 <= off <= 512 -> lib.A.ACtlCut.rgv regs3 9 A0 ->
      0 <= A0 + off -> A0 + off + 8 <= 2 ^ 64 -> A0 = Av).
  { intros A0 off Hoff Hrg Hlo Hhi. unfold lib.A.ACtlCut.rgv in Hrg. rewrite E9 in Hrg.
    assert (Hu : bv_unsigned (Z_to_bv 64 A0) = bv_unsigned (Z_to_bv 64 Av)) by (rewrite Hrg; reflexivity).
    rewrite !Z_to_bv_unsigned in Hu. unfold bv_wrap, bv_modulus in Hu.
    change (2 ^ Z.of_N 64) with (2 ^ 64) in Hu. Z.div_mod_to_equations. lia. }
  assert (SPK : forall off v, 0 <= off <= 512 -> lib.A.ACtlCutP.spill regs3 mem3 off v ->
      lib.A.ACtlCutP.spill (lib.Lib.Frame.mkR (Z_to_bv 64 0x81c84) (lib.Reusable.YK11.getr regs3 2)
        (lib.Reusable.YK11.getr regs3 3) (lib.Reusable.YK11.getr regs3 4) (lib.Reusable.YK11.getr regs3 5)
        (lib.Reusable.YK11.getr regs3 6) (lib.Reusable.YK11.getr regs3 7) (lib.Reusable.YK11.getr regs3 8)
        (lib.Reusable.YK11.getr regs3 9) (Z_to_bv 64 lib.A.Prog.reac_ctrl_kind_name_c.QMARK) a1' a2'
        (lib.Reusable.YK11.getr regs3 13) (lib.Reusable.YK11.getr regs3 14) (lib.Reusable.YK11.getr regs3 15)
        (lib.Reusable.YK11.getr regs3 16) (lib.Reusable.YK11.getr regs3 17) (lib.Reusable.YK11.getr regs3 18)
        (lib.Reusable.YK11.getr regs3 19) (lib.Reusable.YK11.getr regs3 20) (lib.Reusable.YK11.getr regs3 21)
        (lib.Reusable.YK11.getr regs3 22) (lib.Reusable.YK11.getr regs3 23) (lib.Reusable.YK11.getr regs3 24)
        (lib.Reusable.YK11.getr regs3 25) (lib.Reusable.YK11.getr regs3 26) (lib.Reusable.YK11.getr regs3 27)
        (lib.Reusable.YK11.getr regs3 28) (lib.Reusable.YK11.getr regs3 29) (lib.Reusable.YK11.getr regs3 30)
        (lib.Reusable.YK11.getr regs3 31)) m' off v).
  { intros off v Hoff (A0 & Hrg & Hq).
    pose proof Hq as (Hq0 & Hq8 & _).
    rewrite lib.Lib.Mem.length_le8 in Hq8. change (Z.of_nat 8) with 8 in Hq8.
    pose proof (HAeq A0 off Hoff Hrg Hq0 Hq8) as ->.
    exists Av. split; [exact Hrg|].
    apply BAK; [exact Hq|]. rewrite lib.Lib.Mem.length_le8. change (Z.of_nat 8) with 8. right. lia. }
  (* the exit cut *)
  apply (HX cx [] fr k ly3 S3 W3 _ m' md' HB).
  - (* the journal across the callee's write *)
    eapply (lib.Reusable.YCbq.ajournal_exec segs B LAWS lib.A.ACtlG.Kit.kit_segs_low)
      with (Wr := fun a => spv - 16 <= a < spv).
    + exact HJ.
    + intros x Hx. unfold lib.Reusable.YK04.mrestrict.
      destruct (lib.Reusable.YA0n.w_H W3 x); [reflexivity|]. apply MU. cbn [lib.Lib.Frame.outside]. split; [exact Hx | exact I].
    + intros x Hx. unfold lib.Reusable.YK04.mrestrict in *.
      destruct (lib.Reusable.YA0n.w_H W3 x); [exact Hx|].
      pose proof (bv_unsigned_in_range 64 x) as Rx. change (bv_modulus 64) with (2 ^ 64) in Rx.
      destruct (Z_le_gt_dec (spv - 16) (bv_unsigned x)) as [h1|h1];
        [destruct (Z_lt_ge_dec (bv_unsigned x) spv) as [h2|h2]|].
      * destruct (proj2 (proj2 ST') (bv_unsigned x) ltac:(lia)) as (_ & bm & Hbm).
        assert (Ex : lib.Lib.Mem.wa (bv_unsigned x) = x).
        { apply bv_eq. apply lib.Lib.Mem.wa_unsigned. exact Rx. }
        rewrite Ex in Hbm.
        assert (Hbm' : lib.Lib.Mem.mrd lib.A.Img0.rsegs m' x = Some bm) by exact Hbm.
        pose proof (lib.A.MemNorm.seg_rom_unmapped lib.A.Img0.rsegs x (p11g_noseg x ltac:(lia))) as Hrn.
        unfold lib.Lib.Mem.mrd in Hbm'.
        destruct (m' x) as [b'|] eqn:Em; [discriminate | rewrite Hrn in Hbm'; discriminate Hbm'].
      * rewrite (MU x ltac:(cbn [lib.Lib.Frame.outside]; split; [lia | exact I])). exact Hx.
      * rewrite (MU x ltac:(cbn [lib.Lib.Frame.outside]; split; [lia | exact I])). exact Hx.
    + intros x Hx. exact (Hhid x Hx).
    + exact Hsbm.
    + intros a Ha. unfold lib.Reusable.YCbq.awr_byte. left. unfold lib.A.ACfn.LLVMF_STK. lia.
  - exact HF.
  - exact HL.
  - exact Hk.
  - (* the exit body, C_A81c84 (lib.A.ACtlCutP.v:1938-1949) *)
    cbv beta iota zeta delta [lib.A.ACtlCut.cut_body lib.A.ACtlCutP.C_A81c84].
    split; [exact HP|].
    split.
    { (* FRAC: the registers it reads are kept by conversion; its memory lies at A + off, fr, the frame
         shadow and [c_sp cx - 104, c_sp cx), all outside the window *)
      pose proof HFRAC as HFw. unfold lib.A.ACtlCutP.FRAC in HFw |- *.
      destruct HFw as (A1 & sp1 & HFw). exists A1, sp1.
      p11g_walk BAK HFw. }
    split; [exact Hn|].
    split.
    { (* OURb: six bytes at fr + 2624, inside the frame *)
      unfold lib.A.ACtlCutP.OURb in *. apply BAK; [exact HOUR|].
      rewrite lib.A.Prog.SlotModel.OUR_length. left. lia. }
    split; [unfold lib.A.ACtlCut.a0v, lib.A.ACtlCut.rgv; reflexivity|].
    split; [exact (lib.A.Prog.Seg.P11.p11_strings m' HROag')|].
    split; [apply ADK; apply (HADDR lib.A.Prog.reac_ctrl_kind_name_c.QMARK 2);
            [unfold lib.A.Prog.reac_ctrl_kind_name_c.QMARK; lia | lia
            | unfold lib.A.Prog.reac_ctrl_kind_name_c.QMARK; lia | vm_compute; reflexivity]|].
    split.
    { (* XC *)
      unfold lib.A.ACtlCutP.XC in *. destruct HXC as (HXCq & HXCa). split.
      - intros A0 Hrg HA0. pose proof (HAeq A0 280 ltac:(lia) Hrg) as HA0e.
        pose proof (HXCq A0 Hrg HA0) as Hq. pose proof Hq as (Hq0 & Hq8 & _).
        rewrite lib.Lib.Mem.length_le8 in Hq8. change (Z.of_nat 8) with 8 in Hq8.
        rewrite (HA0e Hq0 Hq8) in *. apply BAK; [exact Hq|].
        rewrite lib.Lib.Mem.length_le8. change (Z.of_nat 8) with 8. right. lia.
      - apply ADK. exact HXCa. }
    split; [exact HCUR|].
    split.
    { (* PRO *)
      unfold lib.A.ACtlCutP.PRO in *.
      destruct HPRO as (P40 & P120 & P136 & P160 & P168 & P176 & P208 & P248 & Pad & Pin & Pg & P184 & P256 &
        P264 & P272 & P32).
      split; [exact (SPK 40 _ ltac:(lia) P40)|]. split; [exact (SPK 120 _ ltac:(lia) P120)|].
      split; [exact (SPK 136 _ ltac:(lia) P136)|]. split; [exact (SPK 160 _ ltac:(lia) P160)|].
      split; [exact (SPK 168 _ ltac:(lia) P168)|]. split; [exact (SPK 176 _ ltac:(lia) P176)|].
      split; [exact (SPK 208 _ ltac:(lia) P208)|]. split; [exact (SPK 248 _ ltac:(lia) P248)|].
      split; [apply ADK; exact Pad|].
      split.
      { apply BAK; [exact Pin|].
        destruct (Z.eq_dec (lib.A.ACtlCut.c_n cx) 0) as [Hn0|Hn0].
        - rewrite <- Hnlen. rewrite Hn0. left.
          destruct Hpn as [[_ Hp0] | [Hn26 _]];
            [rewrite Hp0; unfold lib.A.ACfn.A_EMPTY; lia | lia].
        - assert (Hinb : In (lib.A.ACtlCut.c_p cx, lib.A.ACtlCut.c_n cx) (lib.Reusable.YG0d.ablocks B ly3 S3)).
          { destruct Hpn as [[H0 _] | [_ Hinb]]; [lia|].
            apply (Permutation_in _ (Permutation_sym HP)). exact Hinb. }
          destruct (lib.Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 _ _ HAR Hinb)
            as (_ & Hb4096 & Hbceil & _).
          left. rewrite <- Hnlen.
          unfold lib.Reusable.YG00.req_size in Hbceil.
          destruct (Z.eqb_spec (lib.A.ACtlCut.c_n cx) 0) as [Hz|Hz]; lia. }
      split.
      { intros Hn0. apply ADK. exact (Pg Hn0). }
      split; [exact (SPK 184 _ ltac:(lia) P184)|]. split; [exact (SPK 256 _ ltac:(lia) P256)|].
      split; [exact (SPK 264 _ ltac:(lia) P264)|]. split; [exact (SPK 272 _ ltac:(lia) P272)|].
      exact (SPK 32 _ ltac:(lia) P32). }
    split; [exact (SPK 144 _ ltac:(lia) HS144)|].
    split; [apply ADK; exact HAD2691|].
    split; [exact (SPK 192 _ ltac:(lia) HS192)|].
    split; [apply ADK; exact HADfg|].
    split; [apply ADK; exact HAD2688|].
    split.
    { unfold lib.A.ACtlCutP.IDBe in *. apply BAK; [exact HIDB|].
      left. unfold lib.Prog.RcIdentModel.ID0. rewrite repeat_length.
      change (Z.of_nat lib.Prog.RcIdentModel.ID_SIZE) with 38. lia. }
    split.
    { unfold lib.A.ACtlCutP.FGBe in *. apply BAK; [exact HFGB|].
      left. rewrite lib.A.Prog.SlotModel.z72_length.
      lia. }
    apply ADK. exact HAD2880.
  - (* ctl_rt_C at the exit: the exit cut is taken at the entry's state (ly3, S3), so the regions do not move *)
    split.
    { apply (lib.A.AsanRTFacts.asan_cells_kept [(spv - 16, spv)] mem3 m' HAC MU).
      cbn [lib.Lib.Frame.disjoint_from]. split; [|exact I].
      unfold lib.A.AsanRT.RT_LO, lib.A.AsanRT.RT_HI. left. lia. }
    split; [exact (lib.A.ShadowRwOnT.shadow_rw_on_kept _ mem3 m' Hcut MK WM)|].
    split; [exact (lib.A.ShadowRwOnT.shadow_rw_on_kept _ mem3 m' Himg MK WM)|].
    exact HROag'.
Qed.

End GlueP11.
