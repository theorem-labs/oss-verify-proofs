(* lib/A/ACtlG/P6.v -- GLUE for stage seg_P6 of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput (lib/A/ACtl.v:723).
   Written by a Theorem Labs lane; single writer.  rule 24: no function proved (stage glue of a walk).
   Pattern: glue-pattern.md sections 3, 4, 8 (a working note, not in this delivery) (a cgif-form callee).

   WHAT IT PROVES
     glue_seg_P6 : forall POST, CF POST C_A81bf8 -> CF POST C_A81bd8
   with ACtl.v's own CF notation (SK := A.AE2k.tfib_sink_head, FP := []), i.e. exactly ACtl.v's Section hypothesis
   seg_P6.  Segment P6 is 0x81bd8 -> 0x81bf8: eight instructions (li a0,0; li a1,0; ld s7,232(s1); mv a2,s7;
   ld s8,224(s1); mv a3,s8; mv a4,s4; jal reac_ctrl_identity_reply), i.e. reply(fr = 0, len = 0, pa = [A+232],
   pp = [A+224], pn = s4), whose return address 0x81bf8 IS the exit cut.

   THE PROOF
   G1  the entry cut C_A81bd8 (ACtlCutP.v:1856-1872): its body, FRAC (ACtlCutP.v:982-997), the journal's AR / window /
       astk_ok and layout_le, ctl_base's afn_pre, input block and arodata_okS.
   G2  the pre stretch's premises: s1 = A (FRAC's spill base; the body's own A is the same by Z_to_bv injectivity),
       the spill bytes q64 (A + 232) pa / (A + 224) pp, and their rng rows from the journal's present window.
   G3  the walk moved from regs3 to mkR_of regs3 (YA0nR.SRr_xregs_eqv).
   G4  the lift of the MINIMAL pre stretch A.Prog.Seg.P6Fs.p6_evt_pre_Fs (route (A), a Theorem Labs lane 04:21Z, a Theorem Labs lane's
       narrowed-stretch rule) by YA0nR.SRr_fevt at RNG_W (w_H W3): the run reads, never writes, memory.
   G5  the callee: a Theorem Labs lane's treac_ctrl_identity_reply_spec (a Section hypothesis, REPLY_SPEC) at the callee entry
       0x83f8c, through YA0n.SRr_bind; its 23 premises from the cut (fr = 0, so the reply_args premises are
       vacuous); its post's continuation is the exit cut 0x81bf8, so no post stretch.
   G6  the exit cut C_A81bf8 (ACtlCutP.v:1876-1887) at the callee's end state: the journal is the post's (EV_REPLY =
       0); frames / frame law / k unchanged; registers through aregs_preserved; every memory conjunct through the
       post's tcj_kept (stack: the ceiling clause; the class-6 frame and its shadow: the frames clause; the input
       block: the blocks clause) after reading visibility from the entry journal and AR; the input block's shadow
       from the AR shadow law at both states; a0 = reply_ret 0 .. = -1; FRAC's trailer word q64 (fr + 4088) (Batch3,
       ACtlCutP.v:997) from the entry FRAC through the frames clause, the step that keeps the header words
       (fr + 4088 + 8 = fr + 4096, the class-6 frame's end); the exit cut's ctl_rt_C (route (C), A.ACtlRtC) by
       a Theorem Labs lane's PROVED A.ProgWorldCtlRtC.ctl_rt_C_of_AR at the post journal's AR (L3-recipe.md section 2(d) (a working note, not in this delivery)), cited by name.

   SECTION HYPOTHESES (exact text below); ACtl.v discharges seg_P6 with
     glue_seg_P6 B MT XM_LIB RLO RHI REAC_CTRL_IDENTITY_REPLY_K REAC_CTRL_PARSE_BC RELRO_IMG LAWS TFIB_SYMS TREPLY
   - RELRO_IMG, LAWS, TFIB_SYMS: ACtl.v (at head lib/A/ACtl.v:226, :244 and :259; from a working branch 1899bed1aee).  TFIB_SYMS is ACtl.v's text
     character for character; RELRO_IMG and LAWS name the same constants as ACtl.v's (checked by About), spelled
     lib.Reusable.YG0d.<X> (the full path) where ACtl.v writes Reusable.YG0d.<X>.
   - REPLY_SPEC: ACtl.v:316's TREPLY, a Theorem Labs lane's A.Prog.C_reac_ctrl_identity_reply.treac_ctrl_identity_reply_spec
     (SK := A.AE2k.tfib_sink_head) B RLO RHI, cited by name (a Theorem Labs lane's file is on the glue base since batch 4; the earlier
     restated copy, Module P6Reply, is deleted).  It is a cgif-form spec over the journal and AR: it has no shadow_rw
     premise, so route (C) leaves it as it is.
   - TFIB_SYMS and LAWS are also the two premises of a Theorem Labs lane's PROVED A.ProgWorldCtlRtC.ctl_rt_C_of_AR (statement
     ctl_rt_C_of_AR_stmt: no AR_states_vis0_shadow, no AR_states_owned_ro premise), which the proof cites by name for
     the exit cut's ctl_rt_C.  The walk's route (C) cut form (ACtlCut.ctl_from over A.ACtlRtC.ctl_rt_C, a Theorem Labs lane's
     working branch) removed the old VIS0 / OWNED_RO hypotheses (ACtl.v's AR_states_vis0_shadow / AR_states_owned_ro), which
     only the universal ctlrt_of_AR needed.  The entry cut's ctl_rt_C is not used.
   No other: no kit stand-in (A.ACtlG.Kit's kit_wx and kit_segs_low are Required), and no
   pin on REAC_CTRL_IDENTITY_REPLY_K / REAC_CTRL_PARSE_BC (route (A): the minimal stretch and the cgif spec use
   neither; the entry body's two addressable conjuncts on them are simply not used).  The generic memory steps (an
   aview equality on a visible byte gives an mrd equality; bytes_at and AsanRT.addressable move along mrd
   equalities; a byte with a view is visible) are proved inline, as asserts (KitMem candidates, none committed).

   CLOSURE: every project Require is qualified, with explicit paths; no statement names a frame-route identifier
   (the lifted stretch is Required from Seg/P6Fs.v, whose closure is the frame route's, as the glue closure rule
   allows).  The six twin modules are written lib.Reusable.<X> (the core's copy) everywhere.  The one doubled name
   written in a proof, Z_to_bv_bv_unsigned, is written stdpp.bitvector.definitions.Z_to_bv_bv_unsigned, the constant
   `About` names in this file's context.  No MemNorm name and no Module alias.

   MEM_INV (a Theorem Labs lane via a Theorem Labs lane 13:50Z): no contract with a mem_inv premise is applied here (the stretch p6_evt_pre_Fs has
   none; the callee is crossed by REPLY_SPEC).  Seg/P6.v enters the closure only through Seg/P6Fs.v / Seg/P6F.v's
   Requires; no lemma of it is used here.

   BUILD STATE: see the commit message (a working branch 1899bed1aee). *)

From Coq Require Import ZArith List Lia Permutation Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YK1b YI16 YM05 YO09 YI04 YI00.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YA0i YA0n YA0nR YK04 YK0s YP09 YG00 YG01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YG0f YG0n YG0d YG0v YC5d YCbq YE01 APostBase.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require AB1v ACfn AE2k Img0 AsanRT ACtlK.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require ACtlCut ACtlCutP ProgBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require AF0m ProgWorld ACtlRtC ProgWorldCtlRtC.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require C_reac_ctrl_identity_reply.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require PaTable CtrlList CtrlPa CtrlImg CtrlCallerJ SlotModel.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcReply RcIdentModel.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require ExecF MState Regs6ss Mem PropExec.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require P6Fs.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlG Require Kit.
Import ListNotations.
Local Open Scope Z_scope.

(* The core's segment list, as ACtlCut.v:73 and ACtl.v:176 bind it. *)
Local Notation segs := A.AB1v.tfibsegs.

Section GlueP6.

(* ACtl.v's Section shape (ACtl.v:183-187, :227-228), restricted to what this stage uses. *)
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {LS : lib.Reusable.YO09.lib_shape}.
Variable B : lib.Reusable.YG0f.asyms.
Variable MT : lib.Reusable.YC5d.ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable REAC_CTRL_IDENTITY_REPLY_K : Z.
Variable REAC_CTRL_PARSE_BC : Z.

(* ACtl.v's notation block (ACtl.v:261-262, :299-300): the same constants (About), written A.ACtlCut / A.ACtlCutP. *)
Local Notation CF POST X :=
  (A.ACtlCut.ctl_from (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation C_A81bd8 := (A.ACtlCutP.C_A81bd8 B REAC_CTRL_IDENTITY_REPLY_K REAC_CTRL_PARSE_BC).
Local Notation C_A81bf8 := (A.ACtlCutP.C_A81bf8 B).

(* ---------------------------------------------------------------------------------------------------------
   Section hypotheses (sources in the header). *)
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> lib.Reusable.YG0d.in_img segs a.
Hypothesis LAWS : lib.Reusable.YG0d.AR_laws segs B.
Hypothesis TFIB_SYMS : A.AF0m.CtrlTSyms B.
Hypothesis REPLY_SPEC : A.Prog.C_reac_ctrl_identity_reply.treac_ctrl_identity_reply_spec (SK := A.AE2k.tfib_sink_head) B RLO RHI.

(* ---------------------------------------------------------------------------------------------------------
   The stage. *)
Lemma glue_seg_P6 : forall POST, CF POST C_A81bf8 -> CF POST C_A81bd8.
Proof.
  intros POST HX cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
  (* ---- G1: the entry cut, the journal, the base ---- *)
  cbv beta iota zeta delta [A.ACtlCut.cut_body A.ACtlCutP.C_A81bd8] in Hbody.
  destruct Hbody as (HP & HFRAC & Hn & HOUR & HCUR & HPRO & S144 & A2691 & S192 & AFR72 & A2688 & HIDB & HFGB &
    HXC & A1 & pa & pp & f & R9b & HA1 & Hpa & Hpp & Q232 & Q224 & Q192 & _ & _ & A2880).
  pose proof HFRAC as (A & sp & R2 & Hsp16 & EspZ & R4 & R8 & R9 & R3 & R19 & R26 & Hfr32 & HA32 & HAc & HspA &
    HfrA & HA416 & Hsp4096 & HcAPP & Q304 & Q24 & Q16 & QH0 & QH16 & (sh & Hsh & Hshlen) & HSAVED & HTRL).
  unfold A.ACtlCutP.FRAME_BYTES in HfrA. unfold A.AsanRT.APPMEM_END in HcAPP.
  pose proof HJ as (HAR3 & Hly3 & _ & _ & _ & _ & _ & _ & _ & _ & F3j & _ & _ & Fwin3 & Hastk3 & _).
  destruct Hly3 as (_ & _ & _ & _ & _ & EF & _).
  pose proof Hastk3 as (_ & _ & Hceil & Hstklo & _).
  unfold A.ACfn.LLVMF_STK in Fwin3, Hstklo.
  pose proof HB as ((HAFN & _ & _ & _ & Hblk0 & Hnlen & _ & _ & _ & _ & HROS0 & _) & _).
  pose proof HAFN as (_ & _ & _ & Hgp0 & _).
  assert (Hin6 : In (6, A.ACtlCut.c_fpos cx) (lib.Reusable.YG01.frames S3)) by (rewrite HF; left; reflexivity).
  assert (Efr : fr = lib.Reusable.YG0f.frame_addr (A.ACtlCut.c_ly cx) 6 (A.ACtlCut.c_fpos cx))
    by (apply HL; left; reflexivity).
  assert (Efr3 : lib.Reusable.YG0f.frame_addr ly3 6 (A.ACtlCut.c_fpos cx) = fr).
  { rewrite Efr. unfold lib.Reusable.YG0f.frame_addr. rewrite EF. reflexivity. }
  assert (Hsp0 : 0 <= sp) by (rewrite <- EspZ; unfold lib.Reusable.YG0d.spZ; apply bv_unsigned_in_range).
  (* the body's spill base is FRAC's *)
  assert (Hinj : forall x y : Z, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> Z_to_bv 64 x = Z_to_bv 64 y -> x = y).
  { intros x y Hx Hy E. apply (f_equal bv_unsigned) in E. rewrite !Z_to_bv_unsigned in E. unfold bv_wrap in E.
    change (bv_modulus 64) with (2 ^ 64) in E. rewrite !Z.mod_small in E by lia. exact E. }
  assert (EA1 : A1 = A).
  { apply Hinj; [lia | lia |]. unfold A.ACtlCut.rgv in R9, R9b. rewrite <- R9b, <- R9. reflexivity. }
  subst A1.
  (* ---- G2: the arodata_okS view along a journal from the entry (FP = []) ---- *)
  assert (Hro_keep : forall ly' S' (W' : lib.Reusable.YA0n.world segs) mem' md' own k',
            lib.Reusable.YCbq.ajournal (SK := A.AE2k.tfib_sink_head) segs B A.ACfn.LLVMF_STK (A.ACtlCut.c_sp cx) []
              (A.ACtlCut.c_ly cx) (A.ACtlCut.c_S cx) (A.ACtlCut.c_W cx) (A.ACtlCut.c_mem cx) (A.ACtlCut.c_md cx)
              own ly' S' W' mem' md' k' ->
            lib.Reusable.YE01.arodata_okS segs B RLO RHI
              (lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W') mem')).
  { intros ly' S' W' mem' md' own k' HJ' a Hro Ho He.
    pose proof HJ' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
    rewrite (F3 a); [exact (HROS0 a Hro Ho He) | | exact Ho | exact He |].
    - destruct Hro as [(s & Hs & _ & Hr) | Hgot]; [exists s; split; [exact Hs | exact Hr] |].
      exact (RELRO_IMG a Hgot).
    - apply (lib.Reusable.YCbq.fp_spares_closed (SK := A.AE2k.tfib_sink_head)). intros Ho'.
      exact (lib.Reusable.YCbq.sink_closed_nil Ho'). }
  (* ---- G3: the cut's configuration in the run's state form, the walk moved to mkR_of regs3 ---- *)
  rewrite A.ProgBridge.cfg_at_MS.
  change (A.ACtlCut.cut_pc C_A81bd8) with 0x81bd8.
  apply (lib.Reusable.YA0nR.SRr_xregs_eqv segs W3 (lib.Lib.Regs6ss.mkR_of regs3) regs3 lib.Reusable.YK11.fp_regs
           (Z_to_bv 64 0x81bd8) lib.Reusable.YK11.fp_csr None mem3 (lib.Reusable.YK11.seg_rom segs) md3 (POST cx));
    [| exact (lib.Lib.Regs6ss.xregs_eqv_sym _ _ (lib.Lib.Regs6ss.mkR_of_eqv regs3))].
  unfold lib.Lib.Regs6ss.mkR_of.
  (* ---- G4: the minimal pre stretch, lifted at RNG_W (w_H W3) ---- *)
  assert (Hvis_win : forall a, sp <= a < A.ACtlCut.c_sp cx -> lib.Reusable.YA0n.w_H W3 (Z_to_bv 64 a) = false).
  { intros a Ha. exact (proj1 (Fwin3 a ltac:(lia))). }
  eapply (lib.Reusable.YA0nR.SRr_fevt segs A.ACtlG.Kit.kit_wx W3 _ md3
            (A.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W3))).
  { apply A.ProgBridge.fevt_of_evtF.
    eapply (A.Prog.Seg.P6Fs.p6_evt_pre_Fs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
              A pa pp).
    - exact R9.
    - exact Q232.
    - exact Q224.
    - apply A.ProgBridge.rng_RNG_W; [lia | lia | intros a Ha; apply Hvis_win; lia].
    - apply A.ProgBridge.rng_RNG_W; [lia | lia | intros a Ha; apply Hvis_win; lia]. }
  { exact (A.ProgBridge.fp_avoids_RNG_W _). }
  intros ms' md' Hms Hsbm. cbv beta in Hms. subst ms'.
  (* ---- G5: the callee entry 0x83f8c; a Theorem Labs lane's spec ---- *)
  match goal with |- context [lib.Lib.MState.MS ?R _ _ _ _ _ _] => set (R' := R) end.
  set (pn := bv_unsigned (lib.Reusable.YK11.getr regs3 20)).
  set (g := repeat (Z_to_bv 8 0) 50).
  assert (EspR : lib.Reusable.YG0d.spZ R' = sp) by exact EspZ.
  assert (HJe : lib.Reusable.YCbq.ajournal (SK := A.AE2k.tfib_sink_head) segs B A.ACfn.LLVMF_STK (A.ACtlCut.c_sp cx) []
                  (A.ACtlCut.c_ly cx) (A.ACtlCut.c_S cx) (A.ACtlCut.c_W cx) (A.ACtlCut.c_mem cx) (A.ACtlCut.c_md cx)
                  (A.ACtlCut.own6 cx) ly3 S3 W3 mem3 md' k).
  { eapply (lib.Reusable.YCbq.ajournal_exec segs B LAWS A.ACtlG.Kit.kit_segs_low) with (Wr := fun _ : Z => False);
      [exact HJ | intros x _; reflexivity | apply lib.Reusable.YK1b.mem_grows_refl | intros x _; reflexivity
      | exact Hsbm | intros a Ha; destruct Ha]. }
  assert (EAP : A.Prog.C_reac_ctrl_identity_reply.A_reac_ctrl_identity_replyP = 0x83f8c) by reflexivity.
  pose proof (REPLY_SPEC A.ACfn.LLVMF_STK (A.ACtlCut.c_sp cx) [] (A.ACtlCut.c_ly cx) (A.ACtlCut.c_S cx)
                (A.ACtlCut.c_W cx) (A.ACtlCut.c_mem cx) (A.ACtlCut.c_md cx) (A.ACtlCut.own6 cx) ly3 S3 W3 mem3 md' k
                R' 0 0 pa pp pn g HJe) as HR.
  rewrite EAP in HR.
  change (lib.Reusable.YA0n.SRr segs W3 (lib.Reusable.YG0d.cfg_at segs 0x83f8c R' mem3 md') (POST cx)).
  eapply (lib.Reusable.YA0n.SRr_bind segs W3 _ _ (POST cx)).
  { apply HR.
    - exact (Hro_keep _ _ _ _ _ _ _ HJe).
    - reflexivity.
    - match goal with |- 4096 <= ?x => assert (Ex : x = 531448) by reflexivity; rewrite Ex; lia end.
    - exact (eq_trans R3 Hgp0).
    - exact R4.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - exact (eq_sym (stdpp.bitvector.definitions.Z_to_bv_bv_unsigned _ _)).
    - lia.
    - lia.
    - exact Hpa.
    - exact Hpp.
    - exact (bv_unsigned_in_range _ _).
    - rewrite EspR. exact Hsp16.
    - rewrite EspR. unfold A.Prog.C_reac_ctrl_identity_reply.TREPLY_STK, A.Prog.C_reac_ctrl_parse.REAC_CTRL_PARSE_STK,
        lib.Reusable.YG0d.ESTACK, A.ACfn.LLVMF_STK. lia.
    - rewrite EspR. lia.
    - rewrite HF. vm_compute. reflexivity.
    - reflexivity.
    - intros Hra. discriminate Hra.
    - intros Hra. discriminate Hra. }
  (* ---- G6: the exit cut 0x81bf8 at the callee's end state ---- *)
  intros W2 c2 _ (Hwle & ly2 & S2 & regs2 & mem2 & md2 & Ec2 & HJ2 & HAP & HFR2 & HPERM & H10 & HTK & _).
  subst c2.
  change (lib.Reusable.YA0n.SRr segs W2 (lib.Reusable.YG0d.cfg_at segs (A.ACtlCut.cut_pc C_A81bf8) regs2 mem2 md2)
            (POST cx)).
  unfold A.Prog.C_reac_ctrl_identity_reply.EV_REPLY in HJ2. rewrite Z.add_0_r in HJ2.
  pose proof HJ2 as (HAR2 & _).
  unfold A.Prog.CtrlCallerJ.tcj_kept in HTK.
  destruct HTK as (TK1 & TK2 & _ & TK4 & _ & _).
  assert (HnE : forall a, ~ (Prog.RcReply.reply_ok 0 0 pa pp pn g = true /\
                             A.Prog.C_reac_ctrl_identity_reply.treply_out pa pp pn a)).
  { intros a (Hok & _). discriminate Hok. }
  (* the registers the exit cut reads *)
  assert (K2 : lib.Reusable.YK11.getr regs2 2 = lib.Reusable.YK11.getr regs3 2)
    by exact (HAP 2 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia)).
  assert (K3 : lib.Reusable.YK11.getr regs2 3 = lib.Reusable.YK11.getr regs3 3)
    by exact (HAP 3 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia)).
  assert (K4 : lib.Reusable.YK11.getr regs2 4 = lib.Reusable.YK11.getr regs3 4)
    by exact (HAP 4 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia)).
  assert (K8 : lib.Reusable.YK11.getr regs2 8 = lib.Reusable.YK11.getr regs3 8)
    by exact (HAP 8 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia)).
  assert (K9 : lib.Reusable.YK11.getr regs2 9 = lib.Reusable.YK11.getr regs3 9)
    by exact (HAP 9 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia)).
  assert (K19 : lib.Reusable.YK11.getr regs2 19 = lib.Reusable.YK11.getr regs3 19)
    by exact (HAP 19 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia)).
  assert (K22 : lib.Reusable.YK11.getr regs2 22 = lib.Reusable.YK11.getr regs3 22)
    by exact (HAP 22 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia)).
  assert (K25 : lib.Reusable.YK11.getr regs2 25 = lib.Reusable.YK11.getr regs3 25)
    by exact (HAP 25 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia)).
  assert (K26 : lib.Reusable.YK11.getr regs2 26 = lib.Reusable.YK11.getr regs3 26)
    by exact (HAP 26 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia)).
  (* the generic memory steps *)
  assert (Hkeep : forall a, 0 <= a < 2 ^ 64 -> lib.Reusable.YA0n.w_H W3 (Z_to_bv 64 a) = false ->
            lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W2) mem2 a =
            lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W3) mem3 a ->
            lib.Lib.Mem.mrd segs mem2 (lib.Lib.Mem.wa a) = lib.Lib.Mem.mrd segs mem3 (lib.Lib.Mem.wa a)).
  { intros a Ha Hv3 Heq.
    assert (Hv2 : lib.Reusable.YA0n.w_H W2 (Z_to_bv 64 a) = false).
    { destruct (lib.Reusable.YA0n.w_H W2 (Z_to_bv 64 a)) eqn:E; [| reflexivity].
      rewrite (Hwle _ E) in Hv3. discriminate Hv3. }
    unfold lib.Reusable.YG0n.aview, lib.Reusable.YP09.mbyte, lib.Reusable.YK04.mrestrict in Heq.
    rewrite Hv3, Hv2 in Heq. unfold lib.Lib.Mem.mrd, lib.Lib.Mem.wa.
    change (lib.Lib.PropExec.seg_rom segs (Z_to_bv 64 a)) with (lib.Reusable.YK11.seg_rom segs (Z_to_bv 64 a)).
    destruct (mem2 (Z_to_bv 64 a)) as [b2|], (mem3 (Z_to_bv 64 a)) as [b3|],
      (lib.Reusable.YK11.seg_rom segs (Z_to_bv 64 a)) as [b0|]; cbn [option_map] in Heq; try reflexivity;
      try discriminate Heq; injection Heq as Heq; f_equal; apply bv_eq; exact Heq. }
  assert (Hvis_view : forall (W : lib.Reusable.YA0n.world segs) (m : word -> option byte) a,
            lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) m a <> None ->
            lib.Reusable.YA0n.w_H W (Z_to_bv 64 a) = false).
  { intros W m a Hv. destruct (lib.Reusable.YA0n.w_H W (Z_to_bv 64 a)) eqn:E; [| reflexivity]. exfalso. apply Hv.
    pose proof (lib.Reusable.YA0n.w_Hoff W _ E) as Hn0.
    unfold lib.Reusable.YG0n.aview, lib.Reusable.YP09.mbyte, lib.Reusable.YK04.mrestrict. rewrite E.
    unfold lib.Reusable.YK11.seg_rom, memory_read. cbn [Z.of_N]. rewrite Hn0. reflexivity. }
  assert (Hba : forall a l, (forall i, (i < length l)%nat ->
            lib.Lib.Mem.mrd segs mem2 (lib.Lib.Mem.wa (a + Z.of_nat i)) = lib.Lib.Mem.mrd segs mem3 (lib.Lib.Mem.wa (a + Z.of_nat i))) ->
            lib.Lib.Mem.bytes_at segs mem3 a l -> lib.Lib.Mem.bytes_at segs mem2 a l).
  { intros a l Heq (H0 & H1 & H2). split; [exact H0 |]. split; [exact H1 |]. intros i Hi.
    rewrite (Heq i Hi). exact (H2 i Hi). }
  assert (Had : forall p n, (forall i, 0 <= i < n ->
            lib.Lib.Mem.mrd A.Img0.rsegs mem2 (lib.Lib.Mem.wa (A.AsanRT.shadow_addr (p + i))) =
            lib.Lib.Mem.mrd A.Img0.rsegs mem3 (lib.Lib.Mem.wa (A.AsanRT.shadow_addr (p + i)))) ->
            A.AsanRT.addressable mem3 p n -> A.AsanRT.addressable mem2 p n).
  { intros p n Heq (H0 & H1 & H2 & H3). split; [exact H0 |]. split; [exact H1 |]. split; [exact H2 |].
    intros i Hi. destruct (H3 i Hi) as (Happ & b & Hb & Hok). split; [exact Happ |].
    exists b. split; [rewrite (Heq i Hi); exact Hb | exact Hok]. }
  (* the stack above sp: present and visible (the journal's window), kept above the ceiling *)
  assert (Hstk : forall a, sp <= a < A.ACtlCut.c_sp cx ->
            lib.Lib.Mem.mrd segs mem2 (lib.Lib.Mem.wa a) = lib.Lib.Mem.mrd segs mem3 (lib.Lib.Mem.wa a)).
  { intros a Ha. apply Hkeep; [lia | apply Hvis_win; exact Ha |].
    apply TK1; [lia | rewrite EspR; lia | apply HnE]. }
  (* the class-6 frame and its shadow: present and visible (AR's frames law), kept by the frames clause *)
  destruct (lib.Reusable.YG0d.al_frames _ _ LAWS ly3 S3 W3 mem3 md3 6 (A.ACtlCut.c_fpos cx) HAR3 Hin6)
    as (_ & Happf & Hfbytes & Hfshadow).
  rewrite Efr3 in Happf, Hfbytes, Hfshadow.
  change (lib.Reusable.YG00.fs_frame_bytes 6) with 4096 in Happf, Hfbytes, Hfshadow.
  unfold lib.Reusable.YG0f.in_app, lib.Reusable.YG0f.ASAN_CEIL, lib.Reusable.YG0f.kLowShadowBeg,
    lib.Reusable.YG0f.kHighMemBeg in Happf.
  pose proof (@lib.Reusable.YM05.alloc_ceiling_val rc) as Hceilv.
  assert (Hfrm : forall a, fr <= a < fr + 4096 ->
            lib.Lib.Mem.mrd segs mem2 (lib.Lib.Mem.wa a) = lib.Lib.Mem.mrd segs mem3 (lib.Lib.Mem.wa a)).
  { intros a Ha. apply Hkeep; [lia | exact (proj1 (proj1 (Hfbytes a Ha))) |].
    apply (TK4 6 (A.ACtlCut.c_fpos cx)); [exact Hin6 | | apply HnE].
    left. unfold lib.Reusable.YG0n.in_zr, lib.Reusable.YCbq.frame_rng. cbn [fst snd]. rewrite Efr3.
    change (lib.Reusable.YG00.fs_frame_bytes 6) with 4096. lia. }
  assert (Hfsh : forall i, 0 <= i < 512 ->
            lib.Lib.Mem.mrd segs mem2 (lib.Lib.Mem.wa (A.ACtlCutP.Sfr fr + i)) =
            lib.Lib.Mem.mrd segs mem3 (lib.Lib.Mem.wa (A.ACtlCutP.Sfr fr + i))).
  { intros i Hi.
    assert (ES : A.ACtlCutP.Sfr fr + i = lib.Reusable.YG0f.shadow_addr fr + i)
      by (unfold A.ACtlCutP.Sfr, A.AsanRT.shadow_addr, lib.Reusable.YG0f.shadow_addr, A.AsanRT.ASAN_K,
            lib.Reusable.YG0f.SHADOW_OFF; lia).
    rewrite ES. apply Hkeep; [unfold lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF;
      Z.div_mod_to_equations; lia | exact (proj1 (proj1 (Hfshadow i Hi))) |].
    apply (TK4 6 (A.ACtlCut.c_fpos cx)); [exact Hin6 | | apply HnE].
    right. unfold lib.Reusable.YG0n.in_zr. cbn [fst snd]. rewrite Efr3.
    change (lib.Reusable.YG00.fs_frame_bytes 6 / 8) with 512. lia. }
  assert (Hsh_of : forall x, 0 <= x < 3136 ->
            exists i, 0 <= i < 512 /\ A.AsanRT.shadow_addr (fr + x) = A.ACtlCutP.Sfr fr + i).
  { intros x Hx. exists (A.AsanRT.shadow_addr (fr + x) - A.ACtlCutP.Sfr fr). split; [| lia].
    unfold A.ACtlCutP.Sfr, A.AsanRT.shadow_addr. Z.div_mod_to_equations. lia. }
  assert (Hba_frm : forall off l, 0 <= off -> off + Z.of_nat (length l) <= 4096 ->
            lib.Lib.Mem.bytes_at segs mem3 (fr + off) l -> lib.Lib.Mem.bytes_at segs mem2 (fr + off) l).
  { intros off l Ho Hl. apply Hba. intros i Hi. apply Hfrm. lia. }
  assert (Had_frm : forall off n, 0 <= off -> off + n <= 3136 ->
            A.AsanRT.addressable mem3 (fr + off) n -> A.AsanRT.addressable mem2 (fr + off) n).
  { intros off n Ho Hl. apply Had. intros i Hi.
    destruct (Hsh_of (off + i) ltac:(lia)) as (j & Hj & Ej). rewrite Z.add_assoc in Ej. rewrite Ej.
    exact (Hfsh j Hj). }
  assert (Hba_stk : forall a l, sp <= a -> a + Z.of_nat (length l) <= A.ACtlCut.c_sp cx ->
            lib.Lib.Mem.bytes_at segs mem3 a l -> lib.Lib.Mem.bytes_at segs mem2 a l).
  { intros a l Ha Hl. apply Hba. intros i Hi. apply Hstk. lia. }
  assert (Hsp : forall off v, 0 <= off <= 304 ->
            A.ACtlCutP.spill regs3 mem3 off v -> A.ACtlCutP.spill regs2 mem2 off v).
  { intros off v Hoff (A' & R9' & Hq). exists A. split; [unfold A.ACtlCut.rgv; rewrite K9; exact R9 |].
    assert (EA : A' = A).
    { pose proof Hq as (Hq0 & Hq1 & _). rewrite lib.Lib.Mem.length_le8 in Hq1.
      unfold A.ACtlCut.rgv in R9, R9'. rewrite R9 in R9'.
      apply (f_equal bv_unsigned) in R9'. rewrite !Z_to_bv_unsigned in R9'. unfold bv_wrap in R9'.
      change (bv_modulus 64) with (2 ^ 64) in R9'. rewrite (Z.mod_small A) in R9' by lia.
      Z.div_mod_to_equations. lia. }
    subst A'. apply Hba_stk; [lia | rewrite lib.Lib.Mem.length_le8; lia | exact Hq]. }
  (* the input block: its bytes (blocks clause) and, for 0 < n, its shadow (AR's shadow law at both states) *)
  assert (Hin3 : 0 < A.ACtlCut.c_n cx -> In (A.ACtlCut.c_p cx, A.ACtlCut.c_n cx) (lib.Reusable.YG0d.ablocks B ly3 S3)).
  { intros Hn0. destruct Hblk0 as [(Hn1 & _) | (_ & Hin)]; [lia |].
    exact (Permutation_in _ (Permutation_sym HP) Hin). }
  assert (Hin2 : 0 < A.ACtlCut.c_n cx -> In (A.ACtlCut.c_p cx, A.ACtlCut.c_n cx) (lib.Reusable.YG0d.ablocks B ly2 S2)).
  { intros Hn0. exact (Permutation_in _ (Permutation_sym HPERM) (Hin3 Hn0)). }
  assert (Hblk : forall i, (i < length (A.ACtlCut.c_in cx))%nat ->
            lib.Lib.Mem.mrd segs mem2 (lib.Lib.Mem.wa (A.ACtlCut.c_p cx + Z.of_nat i)) =
            lib.Lib.Mem.mrd segs mem3 (lib.Lib.Mem.wa (A.ACtlCut.c_p cx + Z.of_nat i))).
  { intros i Hi. assert (Hn0 : 0 < A.ACtlCut.c_n cx) by lia.
    destruct (lib.Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 _ _ HAR3 (Hin3 Hn0))
      as (_ & _ & _ & Happb & Hpres & _ & _).
    assert (Ers : lib.Reusable.YG00.req_size (A.ACtlCut.c_n cx) = A.ACtlCut.c_n cx).
    { unfold lib.Reusable.YG00.req_size. destruct (Z.eqb_spec (A.ACtlCut.c_n cx) 0); lia. }
    rewrite Ers in Happb, Hpres.
    unfold lib.Reusable.YG0f.in_app, lib.Reusable.YG0f.ASAN_CEIL, lib.Reusable.YG0f.kLowShadowBeg,
      lib.Reusable.YG0f.kHighMemBeg in Happb.
    apply Hkeep; [lia | exact (proj1 (proj1 (Hpres (A.ACtlCut.c_p cx + Z.of_nat i) ltac:(lia)))) |].
    apply (TK2 _ _ _ (Hin3 Hn0)); [rewrite Ers; lia | apply HnE]. }
  assert (Hbsh : 0 < A.ACtlCut.c_n cx -> forall i, 0 <= i < A.ACtlCut.c_n cx ->
            lib.Lib.Mem.mrd A.Img0.rsegs mem2 (lib.Lib.Mem.wa (A.AsanRT.shadow_addr (A.ACtlCut.c_p cx + i))) =
            lib.Lib.Mem.mrd A.Img0.rsegs mem3 (lib.Lib.Mem.wa (A.AsanRT.shadow_addr (A.ACtlCut.c_p cx + i)))).
  { intros Hn0 i Hi.
    destruct (lib.Reusable.YG0d.al_shadow _ _ LAWS ly3 S3 W3 mem3 md3 _ _ HAR3 (Hin3 Hn0)) as (BS3 & _).
    destruct (lib.Reusable.YG0d.al_shadow _ _ LAWS ly2 S2 W2 mem2 md2 _ _ HAR2 (Hin2 Hn0)) as (BS2 & _).
    destruct (lib.Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 _ _ HAR3 (Hin3 Hn0))
      as (_ & _ & _ & Happb & _).
    assert (Ers : lib.Reusable.YG00.req_size (A.ACtlCut.c_n cx) = A.ACtlCut.c_n cx).
    { unfold lib.Reusable.YG00.req_size. destruct (Z.eqb_spec (A.ACtlCut.c_n cx) 0); lia. }
    rewrite Ers in BS3, BS2, Happb.
    unfold lib.Reusable.YG0f.in_app, lib.Reusable.YG0f.ASAN_CEIL, lib.Reusable.YG0f.kLowShadowBeg,
      lib.Reusable.YG0f.kHighMemBeg in Happb.
    destruct BS3 as (Hp8 & _ & BS3). destruct BS2 as (_ & _ & BS2).
    set (j := i / 8).
    assert (Hj : 0 <= j < (A.ACtlCut.c_n cx + 7) / 8) by (subst j; Z.div_mod_to_equations; lia).
    assert (ES : A.AsanRT.shadow_addr (A.ACtlCut.c_p cx + i) =
                 lib.Reusable.YG0v.shadow_of_addr lib.Reusable.YG0f.SHADOW_OFF (A.ACtlCut.c_p cx) + j).
    { subst j. unfold A.AsanRT.shadow_addr, lib.Reusable.YG0v.shadow_of_addr, A.AsanRT.ASAN_K,
        lib.Reusable.YG0f.SHADOW_OFF. Z.div_mod_to_equations. lia. }
    rewrite ES. pose proof (BS3 j Hj) as V3. pose proof (BS2 j Hj) as V2.
    apply Hkeep.
    - unfold lib.Reusable.YG0v.shadow_of_addr, lib.Reusable.YG0f.SHADOW_OFF. subst j. Z.div_mod_to_equations. lia.
    - apply (Hvis_view W3 mem3). rewrite V3. discriminate.
    - rewrite V2, V3. reflexivity. }
  (* the read-only view at the exit, for ctl_rt *)
  assert (HRO2 : lib.Reusable.APostBase.arodata_okP segs RLO RHI B
                   (lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W2) mem2))
    by exact (Hro_keep _ _ _ _ _ _ _ HJ2).
  (* ---- the exit cut's six premises ---- *)
  apply (HX cx idx fr k ly2 S2 W2 regs2 mem2 md2 HB).
  - exact HJ2.
  - rewrite HFR2. exact HF.
  - exact HL.
  - exact Hk.
  - cbv beta iota zeta delta [A.ACtlCut.cut_body A.ACtlCutP.C_A81bf8].
    destruct HCUR as (Hc & C22 & C25).
    destruct HPRO as (P40 & P120 & P136 & P160 & P168 & P176 & P208 & P248 & Pad & Pin & Pg &
      P184 & P256 & P264 & P272 & P32).
    destruct HXC as (HXq & HXa).
    split; [exact (Permutation_trans HPERM HP) |].
    split.
    { exists A, sp.
      split; [rewrite K2; exact R2 |]. split; [exact Hsp16 |].
      split; [unfold lib.Reusable.YG0d.spZ in *; rewrite K2; exact EspZ |].
      split; [rewrite K4; exact R4 |]. split; [unfold A.ACtlCut.rgv in *; rewrite K8; exact R8 |].
      split; [unfold A.ACtlCut.rgv in *; rewrite K9; exact R9 |]. split; [rewrite K3; exact R3 |].
      split; [unfold A.ACtlCut.rgv in *; rewrite K19; exact R19 |].
      split; [unfold A.ACtlCut.rgv in *; rewrite K26; exact R26 |].
      split; [exact Hfr32 |]. split; [exact HA32 |]. split; [exact HAc |]. split; [exact HspA |].
      split; [unfold A.ACtlCutP.FRAME_BYTES; exact HfrA |]. split; [exact HA416 |]. split; [exact Hsp4096 |].
      split; [unfold A.AsanRT.APPMEM_END; exact HcAPP |].
      split; [apply Hba_stk; [lia | rewrite lib.Lib.Mem.length_le8; lia | exact Q304] |].
      split; [apply Hba_stk; [lia | rewrite lib.Lib.Mem.length_le8; lia | exact Q24] |].
      split; [apply Hba_stk; [lia | rewrite lib.Lib.Mem.length_le8; lia | exact Q16] |].
      split; [rewrite <- (Z.add_0_r fr); apply Hba_frm; [lia | rewrite lib.Lib.Mem.length_le8; lia |];
              rewrite Z.add_0_r; exact QH0 |].
      split; [apply Hba_frm; [lia | rewrite lib.Lib.Mem.length_le8; lia | exact QH16] |].
      split.
      { exists sh. split; [| exact Hshlen]. apply Hba; [| exact Hsh]. intros i Hi.
        rewrite Hshlen in Hi. change (Z.to_nat A.ACtlCutP.FRAME_SHADOW) with 392%nat in Hi.
        apply (Hfsh (Z.of_nat i)). lia. }
      split.
      { apply Hba_stk; [lia | | exact HSAVED].
        unfold A.ACtlCutP.saved_bytes. rewrite !length_app, !lib.Lib.Mem.length_le8. lia. }
      { apply Hba_frm; [lia | rewrite lib.Lib.Mem.length_le8; lia | exact HTRL]. } }
    split; [exact Hn |].
    split; [apply Hba_frm; [lia | unfold A.ACtlCutP.OURb; cbn; lia | exact HOUR] |].
    split; [split; [exact Hc |]; unfold A.ACtlCut.rgv in *; rewrite K22, K25; split; assumption |].
    split.
    { split; [eapply Hsp; [lia | exact P40] |]. split; [eapply Hsp; [lia | exact P120] |].
      split; [eapply Hsp; [lia | exact P136] |]. split; [eapply Hsp; [lia | exact P160] |].
      split; [eapply Hsp; [lia | exact P168] |]. split; [eapply Hsp; [lia | exact P176] |].
      split; [eapply Hsp; [lia | exact P208] |]. split; [eapply Hsp; [lia | exact P248] |].
      split; [eapply Had_frm; [lia | lia | exact Pad] |].
      split; [exact (Hba _ _ Hblk Pin) |].
      split; [intros Hn0; exact (Had _ _ (Hbsh Hn0) (Pg Hn0)) |].
      split; [eapply Hsp; [lia | exact P184] |]. split; [eapply Hsp; [lia | exact P256] |].
      split; [eapply Hsp; [lia | exact P264] |]. split; [eapply Hsp; [lia | exact P272] |].
      eapply Hsp; [lia | exact P32]. }
    split; [eapply Hsp; [lia | exact S144] |].
    split; [eapply Had_frm; [lia | lia | exact A2691] |].
    split; [eapply Hsp; [lia | exact S192] |].
    split; [unfold A.ACtlCutP.fragb in *; eapply Had_frm; [lia | lia | exact AFR72] |].
    split; [eapply Had_frm; [lia | lia | exact A2688] |].
    split; [apply Hba_frm; [lia | unfold Prog.RcIdentModel.ID0, Prog.RcIdentModel.ID_SIZE; rewrite repeat_length; lia
                            | exact HIDB] |].
    split; [apply Hba_frm; [lia | unfold A.Prog.SlotModel.z72; rewrite repeat_length; cbn; lia | exact HFGB] |].
    split; [unfold A.ACtlCut.a0v, A.ACtlCut.rgv; rewrite H10; reflexivity |].
    split; [exists f; eapply Hsp; [lia | exists A; split; [exact R9 | exact Q192]] |].
    split.
    { split.
      - intros A'' R9'' HA''. assert (EA : A'' = A).
        { apply Hinj; [exact HA'' | lia |]. unfold A.ACtlCut.rgv in R9'', R9. rewrite <- R9'', K9, R9. reflexivity. }
        subst A''. apply Hba_stk; [lia | rewrite lib.Lib.Mem.length_le8; lia |].
        exact (HXq A R9 ltac:(lia)).
      - eapply Had_frm; [lia | lia | exact HXa]. }
    eapply Had_frm; [lia | lia | exact A2880].
  - exact (A.ProgWorldCtlRtC.ctl_rt_C_of_AR B TFIB_SYMS LAWS RLO RHI ly2 S2 W2 mem2 md2 HAR2 HRO2).
Qed.

End GlueP6.
