(* lib/A/ACtlG/Y3.v -- GLUE for stage seg_Y3 of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput (lib/A/ACtl.v:882):
   the EXIT stage, the one stage that fixes POST (ACtl.v:639: "POST is quantified, the exit stage seg_Y3 alone
   fixes it").  Written by a Theorem Labs lane's glue lane; single writer of this file.
   rule 24: no function proved - glue of an already-proved segment run through an already-proved bridge to a
   fixed stage statement; the released-proof position of LLVMFuzzerTestOneInput was settled earlier for this
   unit (At ossv/recipes c5e779efe8c (2026-10-31), no released proof of it outside this unit; the released ASan donor is cgif/cgif_file_fuzzer at origin/ossv/recipes
   c8557374ad2e, whose own exit lx_leaf_fail, A/ACfj.v:180-207, is the pattern this file follows).

   WHAT IT PROVES
     glue_seg_Y3 : CF ctl_post_leaf C_A82bb0
   with ACtl.v's own CF notation (SK := A.AE2k.tfib_sink_head, FP := []) and ACtl.v's own ctl_post_leaf
   (ACtl.v:338-345, restated verbatim below, same Section arguments, so ACtl.v discharges seg_Y3 by conversion).
   Segment Y3 is 0x82bb0 -> RA_LLVMF, the function's epilogue (Seg/YTail.v:2, the run y3_evt :169):
     0x82bb0 li a0,0   addi sp,s0,-416   ld ra/s0..s11 from [S-104, S)   addi sp,sp,416   ret.

   HOW Y3'S STATEMENT FIXES POST (ACtl.v departure 1, ACtl.v:42-50)
   Every other stage is `forall POST, ..`: it carries an arbitrary continuation across its segment.  seg_Y3 has
   no POST binder: it is `CF ctl_post_leaf C_A82bb0`, the walk's last cut AT the core's own lib post with the
   leaf fuzz_ctrl's shape fixes, LL 0 (m_fs (c_md cx)) [].  So this file does not move a continuation; it
   DISCHARGES one.  After the run returns to RA_LLVMF the walk is over, and `Reusable.YA0n.SRr_ret`
   (YA0n.v:39) turns the goal into `ctl_post_leaf cx W3 c'`, i.e. the fifteen conjuncts of
   A.ACfn.tfib_lib_post_x (ACfn.v:47-58) at the end state.  That is the whole content of this stage, and it is
   why ACtl.v's backward chain can be proved for every POST while the top consumes ctl_walk_leaf (ACtl.v:830).

   THE PROOF, step by step (glue-pattern.md section 3)
   G1  unfold the entry cut C_A82bb0 (ACtlCutP.v:3025-3032, five conjuncts), and the entry context ctl_base
       (ACtlCut.v:120-123) into the core's lib pre (ACfn.v:33-46, sixteen conjuncts) and its afn_pre
       (YCbq.v:336-343, nine conjuncts).
   G2  the run's premises.  The register premise is the body's `rgv regs 8 (c_sp cx)`; the saved-register bytes
       are the body's `bytes_at segs m (c_sp cx - 104) (saved_bytes cx)` (ACtlCutP.v:431-435), which is exactly
       y3_evt_F's thirteen-word reload list with w27..w8 := getr (c_regs cx) 27..8 and w1 := w64 RA_LLVMF; the
       two numeric bounds 416 <= c_sp cx < 2 ^ 64 come from VISIBLE state only (astk_ok of the pre, YCbq.v:333:
       alloc_ceiling <= ly_stk_lo ly, ly_stk_lo ly + LLVMF_STK <= spZ, spZ <= ly_stk_hi ly <= 2 ^ 47, with
       YCbq.asan_consts for alloc_ceiling), never from a hypothesis.
   G3  register maps: ProgBridge.cfg_at_MS turns the cut's cfg_at into MS regs3 fp_regs 0x82bb0 fp_csr None
       mem3 (seg_rom segs); the run starts at the canonical map Regs6ss.mkR_of regs3, and the walk is moved
       there by Reusable.YA0nR.SRr_xregs_eqv, as the pilot A5.v:181-185 does.
   G4  lift: ProgBridge.fevt_of_evtF, ProgBridge.tfibsegs_rsegs, then YA0nR.SRr_fevt at the footprint
       ProgBridge.RNG_W (w_H W3).  The run READS [c_sp cx - 104, c_sp cx) and writes nothing, so the one
       ExecF.rng premise is ProgBridge.rng_of_visible of a range_visible fact, and that fact is the journal's
       own presence conjunct (YCbq.v:368: every byte of [sp0 - LLVMF_STK, sp0) is apresent, and apresent is
       `w_H W (w64 a) = false /\ ..`, YG0n.v:28).  A read-only run may use either lift (glue-pattern section 4).
   G5  the post.  SRr_ret, then the fifteen conjuncts of tfib_lib_post_x at ly3 S3 W3 R mem3 md' k:
         journal     ajournal_exec across the model's materialization (empty write set: the run writes no byte)
                     and then the FP lift [] -> [sink_token] (Kit.kit_ajournal_fp_nil);
         k           k <= EV_LLVMF (the cut's bound) <= EV_LIB (Kit.kit_ev_llvmf_le);
         registers   aregs_preserved from the reload list (2 is the frame-pointer restore, 3 / 4 the body's gp /
                     tp pins, 8 9 18-27 the reloaded saved registers), a0 = 0 from `li a0,0`;
         blocks      the body's Permutation;
         fds / fs    aos_step_closed of the journal's aos_step at FP = [] (YCbq.v:80, with sink_closed_nil);
         the leaf    ll_ret / ll_out by reflexivity, fs_sorted from the pre;
         asink_none  YE01.asink_none_kept, ameta_inv YE01.ameta_inv_kept, both at the image's sink laws AIL
                     (Section hypothesis below; discharged by A.AD1u.tfib_AIL, PROVED in the core, AD1u.v:34);
         the input   the journal's kept-block conjunct (YCbq.v:360-361) at FP = [] through YI04.inFP_nil,
                     exactly as the donor's lx_leaf_fail does (ACfj.v:201-206).

   SECTION HYPOTHESES LEFT (exact text at their declarations below; both listed in the lane report)
   - LAWS: ACtl.v's own (ACtl.v:183); ACtl.v discharges it where it discharges the donor-form laws (its
     section 9, Reusable.YG0q.AR_laws_ok).
   - AIL: the image's sink laws `asink_img_laws segs B tfib_K` (YE01.v:28), the premise of YE01's two kept
     lemmas, exactly as the donor's walk takes it (its Section hypothesis AIL, A/ACfj.v:193 and :199).  It is
     PROVED in the core as A.AD1u.tfib_AIL (AD1u.v:34) from ACtl.v's TFIB_SYMS, so ACtl.v discharges it with
     `A.AD1u.tfib_AIL B TFIB_SYMS`.  It is a hypothesis here and not a citation for ONE reason, the closure:
     AD1u Requires AD1y, which Requires the core's program walks (AB12, AB1h, AB13, AD2j, AD2i, AD1t, AE22,
     YCe5); a glue file of one epilogue should not carry them, and on the D5 pack AB1h does not even compile
     (measured: AB1h.v:50, the image's third segment is 8192 bytes, AB1h states 12288).
   - MO_LE: the meter, ACtl.v's own Section Ctl hypothesis (ACtl.v:217 at glue base 8ee48574229, Batch3), the
     same name and text, so ACtl.v passes it by `exact`.  tfib_lib_post_x's thirteenth conjunct is
     `mo_le MT S S' (XN_LIB n)`, and NOTHING in the cut layer carries a meter fact: ctl_base has only
     `mo_ok MT S (XM_LIB n)` and no cut body or ctl_from premise mentions MT.  ACtl.v discharges it in its
     section 9 at MT := Reusable.YCbp.ameter_triv by mo_le_triv.

   FROM THE SHARED KIT lib/A/ACtlG/Kit.v (Required qualified, never copied): Kit.kit_wx (G4), Kit.kit_segs_low,
   Kit.kit_ajournal_fp_nil and Kit.kit_ev_llvmf_le (G5).  The last two are a Theorem Labs lane's kit lemmas (Kit.v
   :120 and :138 at glue base 8ee48574229); this file's former local copies (y3_ajournal_fp_nil, the inline lia
   for EV_LLVMF <= EV_LIB) are deleted.

   CLOSURE (the glue closure rule, a Theorem Labs lane 23:32Z, porter 23:38Z / 23:40Z): every Require below is qualified, no
   Import / Export of a project module; no statement here names a frame-route identifier (the `_F` file's own
   closure reaches the frame route, which closure rule 1 allows).

   SHADOWED NAMES.  SIX modules exist both as the core's lib/Reusable/<X> and as ctrl's lib/A/Reusable/<X>:
   YI04, YI16, YK11, YK1b, YM05, YO09 (a Theorem Labs lane, 03:48Z, via a Theorem Labs lane).  A partial name resolves to
   whichever was loaded last, so this file names each of the five it uses (YI16 no longer: the FP lift is the
   kit's) through a Module alias bound to its FULL path (below); no partial `Reusable.YI04.` / `.YI16.` /
   `.YK11.` / `.YK1b.` / `.YM05.` / `.YO09.` occurs.  getr / mkst / seg_rom / cfg_at are RK11.* /
   Reusable.YG0d.cfg_at only.

   BUILD STATE: see the commit message and the lane report (type-check; the label, the closure scan and
   `Print Assumptions glue_seg_Y3` come with each build).  No Axiom, no Parameter, no Admitted, no admit, no
   Abort. *)

From Coq Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Sem.
(* The twin modules (lib/Reusable/X and lib/A/Reusable/X) this file uses are Required by their CORE path
   (porter a Theorem Labs lane, 04:33Z: `From ..lib Require Reusable.X` matches both copies and FAILS the gate). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YK1b YI04 YM05 YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YA0n Reusable.YA0nR Reusable.YG0f.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG00 Reusable.YG01 Reusable.YG0n.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG0d Reusable.YC5d Reusable.YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YE00 Reusable.YE01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.AB1v A.ACfn A.AE2k.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Img0 A.ACtlK A.ACtlCut A.ACtlCutP A.ProgBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require ExecF MState Regs6ss Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlG.Kit.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.Seg.YTailF.
Import ListNotations.
Local Open Scope Z_scope.

(* The five collided modules this file uses, each bound to its FULL path (header, SHADOWED NAMES). *)
Module RI04 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI04.
Module RK11 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
Module RK1b := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.
Module RM05 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.
Module RO09 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.
(* The `_F` file of record for this segment (a Theorem Labs lane's YTailF.v: y3_evt_F :173-243). *)
Module YTF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.YTailF.

(* The core's segment list, as ACtlCut.v:74 and ACtl.v:161 bind it. *)
Local Notation segs := A.AB1v.tfibsegs.

Section GlueY3.

(* ACtl.v's Section shape (ACtl.v:170-192), restricted to what this stage uses, in ACtl.v's order. *)
Context {fx : RK11.FPState} {rc : RM05.RunCeil} {LS : RO09.lib_shape}.
Variable B : Reusable.YG0f.asyms.
Variable MT : Reusable.YC5d.ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
(* The core's AR law record (ACtl.v:183). *)
Hypothesis LAWS : Reusable.YG0d.AR_laws segs B.
(* The meter: ACtl.v's Section Ctl hypothesis MO_LE (ACtl.v:217), its exact name and text.  See the header: the cut
   layer carries no meter fact. *)
Hypothesis MO_LE : forall (S S' : Reusable.YG00.astate) (m : Z), Reusable.YC5d.mo_le MT S S' m.
(* The image's sink laws (YE01.v:28), the premise of YE01.asink_none_kept / ameta_inv_kept; the donor's walk
   takes the same Section hypothesis (A/ACfj.v:193, :199).  Discharged in ACtl.v by A.AD1u.tfib_AIL B TFIB_SYMS
   (PROVED, AD1u.v:34); see the header for why it is not cited here. *)
Hypothesis AIL : Reusable.YE01.asink_img_laws (SK := A.AE2k.tfib_sink_head) segs B A.AE2k.tfib_K.

(* ACtl.v's notation block (ACtl.v:214-216 and :316-318), verbatim. *)
Local Notation CF POST X :=
  (ACtlCut.ctl_from (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation C_A82bb0 := (ACtlCutP.C_A82bb0 B).
Local Notation ctlcx := ACtlCut.ctlcx.
Local Notation c_md := ACtlCut.c_md.
Local Notation c_mem := ACtlCut.c_mem.

(* ACtl.v:338-345, verbatim: ctl_post with its leaf fixed to the one fuzz_ctrl's tree takes (departure 1). *)
Definition ctl_post_leaf (cx : ctlcx) : Reusable.YA0n.world segs -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md' k,
    c' = Reusable.YG0d.cfg_at segs A.ACfn.RA_LLVMF regs' mem' md' /\
    A.ACfn.tfib_lib_post_x B MT XN_LIB
      (ACtlCut.c_regs cx) (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx)
      (c_mem cx) (c_md cx) (ACtlCut.c_p cx) (ACtlCut.c_n cx) (ACtlCut.c_M cx)
      (RO09.LL 0 (m_fs (c_md cx)) [])
      ly' S' W' regs' mem' md' k.

(* ---------------------------------------------------------------------------------------------------------
   The stage. *)
Lemma glue_seg_Y3 : CF ctl_post_leaf C_A82bb0.
Proof.
  intros cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
  (* G1: the entry cut (C_A82bb0, ACtlCutP.v:3025-3032) and the entry context (ACtlCut.v:120-123). *)
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A82bb0] in Hbody.
  destruct Hbody as (HPerm & R8 & R3 & R4 & HSAV).
  destruct HB as [HPRE Hsp1].
  destruct HPRE as (HAFN & Hra & Hp10 & Hn11 & Hpn & Hnpl & HGARR & HFRM0 & HEV & HLIVE &
                    HROS & HSNK0 & HFD0 & HSORT0 & HAM0 & HMOK).
  destruct HAFN as (HAR0 & Hret & Hra4096 & Hgp0 & Htp0 & HSTK & HPRES0 & HCH & HQT0).
  pose proof HJ as (HARj & Hlyj & Hsecsj & Hwlej & Hioj & Hfrsj & Hnevj & Hkj & G1 & G2 & G3 & G4 &
                    Hgonej & HPRESJ & Hstaticj & G5 & HQTj).
  (* G2: the two numeric bounds, from visible state only (astk_ok of the pre). *)
  destruct HSTK as (Hsp16 & HSTKnn & Hcl & Hstklo & Hstkhi & Hhi47 & _).
  pose proof Reusable.YCbq.asan_consts as [Hac _].
  assert (HspLo : 416 <= ACtlCut.c_sp cx).
  { unfold ACtlCut.c_sp. unfold A.ACfn.LLVMF_STK in Hstklo. lia. }
  assert (HspHi : ACtlCut.c_sp cx < 2 ^ 64).
  { unfold ACtlCut.c_sp. change (2 ^ 47) with 140737488355328 in Hhi47. lia. }
  (* the saved-register window is visible: the journal's presence conjunct over [sp0 - LLVMF_STK, sp0) *)
  assert (HVIS : A.ProgBridge.range_visible (Reusable.YA0n.w_H W3) (ACtlCut.c_sp cx - 104) 104).
  { split; [lia|]. split; [lia|]. intros a Ha.
    exact (proj1 (HPRESJ a ltac:(unfold A.ACfn.LLVMF_STK; lia))). }
  (* G3: the cut's configuration in the run's state form, then the walk moved to the canonical map. *)
  rewrite A.ProgBridge.cfg_at_MS.
  change (ACtlCut.cut_pc C_A82bb0) with 0x82bb0.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (Lib.Regs6ss.mkR_of regs3) regs3 RK11.fp_regs
           (Z_to_bv 64 0x82bb0) RK11.fp_csr None mem3 (RK11.seg_rom segs) md3 (ctl_post_leaf cx));
    [| exact (Lib.Regs6ss.xregs_eqv_sym _ _ (Lib.Regs6ss.mkR_of_eqv regs3))].
  (* G4: the _F run of record (YTailF.v:120-190) at the footprint RNG_W (w_H W3). *)
  pose proof (YTF.y3_evt_F (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))
      (Sem.reg_get regs3 1) (Sem.reg_get regs3 2) (Sem.reg_get regs3 3) (Sem.reg_get regs3 4)
      (Sem.reg_get regs3 5) (Sem.reg_get regs3 6) (Sem.reg_get regs3 7)
      (Sem.reg_get regs3 10) (Sem.reg_get regs3 11) (Sem.reg_get regs3 12) (Sem.reg_get regs3 13)
      (Sem.reg_get regs3 14) (Sem.reg_get regs3 15) (Sem.reg_get regs3 16) (Sem.reg_get regs3 17)
      (Sem.reg_get regs3 28) (Sem.reg_get regs3 29) (Sem.reg_get regs3 30) (Sem.reg_get regs3 31)
      (Sem.reg_get regs3 8) (Sem.reg_get regs3 9)
      (Sem.reg_get regs3 18) (Sem.reg_get regs3 19) (Sem.reg_get regs3 20) (Sem.reg_get regs3 21)
      (Sem.reg_get regs3 22) (Sem.reg_get regs3 23) (Sem.reg_get regs3 24) (Sem.reg_get regs3 25)
      (Sem.reg_get regs3 26) (Sem.reg_get regs3 27)
      RK11.fp_regs RK11.fp_csr mem3 (ACtlCut.c_sp cx) A.ACfn.RA_LLVMF
      (Z_to_bv 64 A.ACfn.RA_LLVMF)
      (RK11.getr (ACtlCut.c_regs cx) 8) (RK11.getr (ACtlCut.c_regs cx) 9)
      (RK11.getr (ACtlCut.c_regs cx) 18) (RK11.getr (ACtlCut.c_regs cx) 19)
      (RK11.getr (ACtlCut.c_regs cx) 20) (RK11.getr (ACtlCut.c_regs cx) 21)
      (RK11.getr (ACtlCut.c_regs cx) 22) (RK11.getr (ACtlCut.c_regs cx) 23)
      (RK11.getr (ACtlCut.c_regs cx) 24) (RK11.getr (ACtlCut.c_regs cx) 25)
      (RK11.getr (ACtlCut.c_regs cx) 26) (RK11.getr (ACtlCut.c_regs cx) 27)
      ltac:(unfold ACtlCut.rgv in R8; exact R8)
      (conj HspLo HspHi)
      ltac:(unfold A.ACfn.RA_LLVMF; reflexivity)
      ltac:(unfold A.ACfn.RA_LLVMF; lia)
      eq_refl
      ltac:(unfold ACtlCutP.saved_bytes in HSAV; exact HSAV)
      (A.ProgBridge.rng_of_visible _ _ _ HVIS)) as HRUN.
  pose proof (A.ProgBridge.fevt_of_evtF _ _ _ HRUN) as HFS.
  rewrite <- A.ProgBridge.tfibsegs_rsegs in HFS.
  apply (Reusable.YA0nR.SRr_fevt segs A.ACtlG.Kit.kit_wx W3 _ md3
           (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) _ (ctl_post_leaf cx) HFS).
  { apply A.ProgBridge.fp_avoids_RNG_W. }
  (* G5: the end state is the return configuration at RA_LLVMF; the walk is over. *)
  intros ms' md' HQ0 Hsbm.
  destruct HQ0 as (q0 & q1 & q2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & q3 & q4 & q5 & q6 & Ems).
  subst ms'.
  apply Reusable.YA0n.SRr_ret.
  (* the journal across the model's materialization: no byte written, the model materialized *)
  assert (HJ' : Reusable.YCbq.ajournal (SK := A.AE2k.tfib_sink_head) segs B A.ACfn.LLVMF_STK
                  (ACtlCut.c_sp cx) [] (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx)
                  (c_mem cx) (c_md cx) [] ly3 S3 W3 mem3 md' k).
  { eapply (Reusable.YCbq.ajournal_exec segs B LAWS A.ACtlG.Kit.kit_segs_low) with (Wr := fun _ : Z => False);
      [exact HJ | intros x _; reflexivity | apply RK1b.mem_grows_refl | intros x _; reflexivity
      | exact Hsbm | intros a Ha; destruct Ha]. }
  destruct (Reusable.YCbq.aos_step_closed [] (c_md cx) md'
              Reusable.YCbq.sink_closed_nil
              ltac:(pose proof HJ' as (_ & _ & _ & _ & Hio' & _); exact Hio')) as (Efd & Efsys & Eproc & Eio).
  unfold ctl_post_leaf.
  do 6 eexists.
  split; [reflexivity|].
  unfold A.ACfn.tfib_lib_post_x.
  split; [apply A.ACtlG.Kit.kit_ajournal_fp_nil; exact HJ'|].
  split; [change (ACtlCut.cut_kmax C_A82bb0 cx idx) with A.ACtlK.EV_LLVMF in Hk;
          pose proof A.ACtlG.Kit.kit_ev_llvmf_le; lia|].
  split.
  { (* aregs_preserved: 2 from the frame-pointer restore, 3 / 4 from the body, 8 9 18-27 reloaded *)
    intros r Hr. unfold Reusable.YG0d.acallee_saved in Hr.
    destruct Hr as [-> | [-> | [-> | [-> | [-> | Hr]]]]].
    - cbn. unfold ACtlCut.c_sp, Reusable.YG0d.spZ. apply stdpp.bitvector.definitions.Z_to_bv_bv_unsigned.
    - cbn. unfold ACtlCut.rgv in R3. cbn in R3. exact R3.
    - cbn. unfold ACtlCut.rgv in R4. cbn in R4. exact R4.
    - reflexivity.
    - reflexivity.
    - assert (Hr' : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/
                    r = 26 \/ r = 27) by lia.
      repeat (destruct Hr' as [-> | Hr']; [reflexivity|]). subst r. reflexivity. }
  split; [reflexivity|].
  split; [exact HPerm|].
  split; [intros fd; unfold m_fds; rewrite Efd; reflexivity|].
  split; [cbn [RO09.ll_fs]; unfold m_fs; rewrite Efsys; reflexivity|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [cbn [RO09.ll_fs]; exact HSORT0|].
  split.
  { eapply (Reusable.YE01.asink_none_kept (SK := A.AE2k.tfib_sink_head) segs B A.AE2k.tfib_K AIL);
      [exact HJ' | intros Ho; exact (Reusable.YCbq.sink_closed_nil Ho) | exact HSNK0]. }
  split.
  { eapply (Reusable.YE01.ameta_inv_kept (SK := A.AE2k.tfib_sink_head) segs B A.AE2k.tfib_K AIL);
      [exact HJ' | exact HAM0]. }
  split; [apply MO_LE|].
  (* the input bytes are kept: the journal's block conjunct at FP = [] (donor ACfj.v:201-206) *)
  intros i Hi.
  destruct Hpn as [[Hn0 _] | [Hnpos Hpin]]; [exfalso; lia|].
  pose proof HJ' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2' & _).
  apply (F2' (ACtlCut.c_p cx) (ACtlCut.c_n cx) i Hpin).
  - eapply Permutation_in; [apply Permutation_sym; exact HPerm | exact Hpin].
  - unfold Reusable.YG00.req_size.
    destruct (Z.eqb_spec (ACtlCut.c_n cx) 0) as [Heq0 | Hne0]; [exfalso; lia | exact Hi].
  - apply RI04.inFP_nil.
Qed.

End GlueY3.
