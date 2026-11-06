(* lib/A/ACtlAll.v -- the CLOSED TOP of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput (libreac v1.9.0, ASan build)
   in route (C): A.ACtl.ctl_lib_x_CtrlB applied to a proof of every premise that has one on the integrated tree
   a working branch.  proves no function (kind: merge; rule 24: no function proved here, a composition of
   proved stage glues and callee glues).  Writer: a Theorem Labs lane (brief integ.md (a working note, not in this delivery));
   shape: image B's twin lib/B/ACtlAll.v at a working branch 51de8d2c1ff.

   ctl_lib_x_CtrlB (lib/A/ACtl.v section 9, Section CtlTop) is ctl_lib_x at the core's bundle A.AD2l.CtrlB, the
   trivial meter, XM_LIB = XN_LIB := XL0 and the read-only span [0x9e380, 0xa07c8).  Its arguments are CtlTop's two
   allocator hypotheses (CtrlB_afree, CtrlB_amalloc; CtlTop binds CtrlB_asm6 to a Theorem Labs lane's disco_stack_malloc6), then Section Ctl's TPARSE TREPLY GLOBS_A
   GLOBS_A_MARKED NAME_GLOB TBUILD CLS CM_SPEC AMEMCHR_SITE H_strcmp LS_LEAF CHAIN_OF_CUT and the 94 stage hypotheses
   seg_*, in that order.  ctl_lib_x_CtrlB_all applies it at LS := fuzz_ctrl's agreement shape (A/CtrlTFIB.v:24, the
   shape a Theorem Labs lane's ctrl_LS_LEAF is proved at) to:
   - each stage: the stage glue A.ACtlG.<S>.glue_seg_<S> of the integrated tree, applied to its Section arguments at
     the top's instantiation (B := CtrlB, MT := ameter_triv, XM_LIB = XN_LIB := XL0, RLO / RHI := 0x9e380 / 0xa07c8,
     the callee constants 9072 / 0x21200 with KREPLY / KPARSE := eq_refl), each Section hypothesis by the term of
     the same name below (section DISCHARGES), so the application checks every glue against ACtl.v's hypothesis;
   - each callee spec and allocator / runtime fact: the proved lemma named at its binding below (DISCHARGES), with
     the owner, branch and blob of record in the comment;
   - everything else is a NAMED Section hypothesis (section OPEN): TMB and TMB_LAY, typed by the named statements
     TMB_stmt / TMB_LAY_stmt (the callee glues' binder text at the top's instantiation), with owner and reason.  Each
     becomes an argument of ctl_lib_x_CtrlB_all when the Section closes; About / Print Assumptions list them.
   No Axiom, no Parameter, no Admitted, no admit. *)

From Coq Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI16.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YG00 YG0f YG0d YC5d YCbq YCbp YG0q YG05 YG0t APostBase.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.ZTraceSpec OSSVerify.Proofs.libreac.fuzz_ctrl.lib.AgreeShape.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require AB1v AE2k ACfn ACeh AF0m AD2l AD1u AF0q AF0w ACtlCutC ACtlBCode Img0.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require ACtl ACtlTopFacts ACtlGlobs AFrameFlagLaw CtrlClose ACtlTopLink.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Rt Require StackMalloc1 StackMalloc2 StackMalloc6 Memchr Strcmp.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require C_reac_ctrl_parse C_reac_ctrl_identity_reply C_reac_ctrl_build_as.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require C_reac_ctrl_classify_box_frame C_reac_box_catalogue_match CtrlRo.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require reac_ctrl_classify_box_frame_glue reac_box_catalogue_match_glue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require reac_ctrl_build_asTop C_reac_ctrl_parseP C_ctrl_emit_as G_ctrl_emit_as_on.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require asan_memsetF_on memset asan_memcpyF_on reac_braid_encode_ns0F ctrl_finishF_on BuildAsImg.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require C_ctrl_lay_block_glue CtrlImg C_reac_box_model_block.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require ProgWorld ACtlLayImg.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Rt Require StackMalloc0.
(* The 94 stage glues. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlG Require A1 A2 A3 A4 A5 R1_turn R2 R3 R4 R5 R6 R7.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlG Require R8 R9 R10 R11 R12 R13 R14 R15 R16 R17 R18 R19.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlG Require R20 R21 P1 P1_70 P2 P3 P4 P5 P6 P7 P8 P9.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlG Require P10 P11 P12 F1 F2 F3 F4 F5 F5_df0 F5_e0c F5_e10 F6_e28.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlG Require F6_ebc F7 F8 F9 F10 F11_fd4 F11_014 F12 F13 F14 F15 F15b.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlG Require F16 F17 F17b F18 F19 F20 F21 F22 F23 F24 F25 F26.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlG Require F27 F28a F28b F29 F30 F31 F32 F33 F34 F35 F36_827f0 F36_827f4.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlG Require F36_82810 F36_8281c F36_828b8 F37 F38 X1 X2 Jrel Y1 Y3.
(* a Theorem Labs lane's proof of A5.v's Section hypothesis seg_A5_run_F. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlG Require A5Run.
Import ListNotations.
Local Open Scope Z_scope.

Local Notation segs := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AB1v.tfibsegs.
Local Notation CtrlB := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AD2l.CtrlB.
Local Notation MT0 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YCbp.ameter_triv.
Local Notation XL0 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtl.XL0.
Local Notation RLO := 0x9e380.
Local Notation RHI := 0xa07c8.
Local Notation SK0 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AE2k.tfib_sink_head.
(* fuzz_ctrl's agreement shape (A/CtrlTFIB.v:23; A/CtrlClose.v's LS), the shape ctrl_LS_LEAF holds at. *)
Local Notation LSc :=
  (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.AgreeShape.ag_shape OSSVerify.Proofs.libreac.fuzz_ctrl.lib.ZTraceSpec.checksum_shape).
(* ACtl.v section 1c's registered-globals list of the catalogue (its Let GLOBS) and the image's list (a1). *)
Local Notation GLOBS_CM :=
  [(OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.C_reac_box_catalogue_match.A_CM_TBL,
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.C_reac_box_catalogue_match.CM_ROWS)].
Local Notation GLOBS_A := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlGlobs.ctrl_globs_A.

(* The two premises this file leaves open, as NAMED statements (a Theorem Labs lane's review, 22:55Z), so that ACtlAsanFinalPre.v binds
   them by name: a Theorem Labs lane's reac_box_model_block spec (C_reac_box_model_block.v:136) at CtrlB, the read-only span and
   the callee's address A_reac_box_model_blockP (= BASE + AF_reac_box_model_block, C_reac_box_model_block.v:80), at the
   catalogue singleton (TMB_stmt: a Theorem Labs lane's catalogue glue's binder TMB) and at the image's globals list (TMB_LAY_stmt:
   a Theorem Labs lane's lay glue's binder TMB). *)
Definition TMB_stmt (fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.FPState)
  (rc : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.RunCeil) : Prop :=
  A.Prog.C_reac_box_model_block.treac_box_model_block_spec (fx := fx) (rc := rc) (SK := SK0) CtrlB GLOBS_CM
    A.Prog.C_reac_box_model_block.A_reac_box_model_blockP RLO RHI.
Definition TMB_LAY_stmt (fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.FPState)
  (rc : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.RunCeil) : Prop :=
  A.Prog.C_reac_box_model_block.treac_box_model_block_spec (fx := fx) (rc := rc) (SK := SK0) CtrlB GLOBS_A
    A.Prog.C_reac_box_model_block.A_reac_box_model_blockP RLO RHI.

Section CtlAll.
Context {fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.FPState}
  {rc : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.RunCeil}.

(* ---------------------------------------------------------------------------------------------------------
   DISCHARGES I: the core's facts at CtrlB and ACtl.v section 9's closed facts. *)
(* the core: A.AD2l.CtrlB_syms (AD2l.v:72) *)
Let TFIB_SYMS : A.AF0m.CtrlTSyms CtrlB := A.AD2l.CtrlB_syms.
(* the core: Reusable.YG0q.AR_laws_ok (YG0q.v:803) *)
Let LAWS : Reusable.YG0d.AR_laws segs CtrlB := Reusable.YG0q.AR_laws_ok segs CtrlB.
(* a Theorem Labs lane: A.ACtlBCode.actlb_libS (as ACtl.v section 9's CtrlB_libS) *)
Let TFIB_LIB : A.ACeh.TfibLib CtrlB := A.ACtlBCode.actlb_libS.
(* ACtl.v section 9: relro_img_ctrl / relro_kind_name_ctrl / relro_cat_ctrl / relro_frames_ctrl / mo_le_triv / qmark_row_ctrl *)
Let RELRO_IMG : forall a, RLO <= a < RHI -> Reusable.YG0d.in_img segs a := A.ACtl.relro_img_ctrl.
Let RELRO_KIND_NAME : RLO <= 0x9e760 /\ 0x9e760 + 112 <= RHI := A.ACtl.relro_kind_name_ctrl.
Let RELRO_CAT : RLO <= A.Prog.SlotModel.CAT /\ A.Prog.SlotModel.CAT + A.Prog.SlotModel.CAT_N * A.Prog.SlotModel.CAT_ROW <= RHI :=
  A.ACtl.relro_cat_ctrl.
Let RELRO_FRAMES : RLO <= 0x9f7e0 /\ 0x9f7e0 + 264 <= RHI := A.ACtl.relro_frames_ctrl.
Let MO_LE : forall (S S' : Reusable.YG00.astate) (m : Z), Reusable.YC5d.mo_le MT0 S S' m := A.ACtl.mo_le_triv.
Let QMARK_ROW := A.ACtl.qmark_row_ctrl.
(* the core: Reusable.YG05.model_laws_ok at CtrlTSyms' universe (ACtl.v section 9's ctrlB_ml) *)
Let ML : Reusable.YG0d.model_laws (Reusable.YG0f.as_universe CtrlB) :=
  Reusable.YG05.model_laws_ok (Reusable.YG0f.as_universe CtrlB) (A.AF0m.ts_universe CtrlB TFIB_SYMS).
(* the core's allocator realizes facts at CtrlB (ACtl.v CtlTop's CtrlB_afree / CtrlB_amalloc): A.AF0q.afree_realizes_closed
   (AF0q.v:13) / A.AF0w.tfib_amalloc_realizes (AF0w.v:45); as_dhash CtrlB = tfib_dhash by definition *)
Let AFREE : Reusable.YG0d.afree_realizes segs CtrlB := A.AF0q.afree_realizes_closed CtrlB TFIB_SYMS (fun _ => eq_refl).
Let AMALLOC : Reusable.YG0d.amalloc_realizes segs CtrlB := A.AF0w.tfib_amalloc_realizes CtrlB TFIB_SYMS (fun _ => eq_refl).
(* ACtl.v section 9's terms for batch 4's rules at ameter_triv *)
Let AFREE4 := Reusable.YCbp.afree04_rule_triv (SK := SK0) segs CtrlB A.ACeh.tfib_segs_low (A.ACeh.tl_env CtrlB TFIB_LIB) LAWS ML AFREE.
Let AMALLOC4 := Reusable.YCbp.amalloc04_rule_triv (SK := SK0) segs CtrlB A.ACeh.tfib_segs_low (A.ACeh.tl_env CtrlB TFIB_LIB) LAWS ML AMALLOC.
Let MT_FREE : forall S m, Reusable.YC5d.mo_ok MT0 S m := fun _ _ => I.
Let MO_MALLOC_OK : forall (S : Reusable.YG00.astate) (n : Z), Reusable.YC5d.mo_ok MT0 S (Reusable.YC5d.mo_malloc MT0 n) := fun _ _ => I.
(* the core: A.AD1u.tfib_AIL (ACtl.v section 9's AIL) *)
Let AIL := A.AD1u.tfib_AIL CtrlB TFIB_SYMS.
(* a Theorem Labs lane: A.ACtlCutC.ctrl_img_shadow_vis (ACtl.v section 1c's Let IMG_SHADOW_VIS) *)
Let IMG_SHADOW_VIS : A.Prog.CtrlRo.img_shadow_vis segs CtrlB := A.ACtlCutC.ctrl_img_shadow_vis CtrlB TFIB_SYMS LAWS.
(* the core's stack-malloc progress (A/ACtlG/A1.v:358's proof, by Reusable.YG05.stack_malloc_progress) *)
Let SMP : Reusable.YCbq.stack_malloc_progressP CtrlB := fun s cid HW Hc Hn0 => Reusable.YG05.stack_malloc_progress _ s cid HW Hc Hn0.
(* the core: Reusable.YG0t.astack_free_law_ok (YG0t.v:473) *)
Let ASF := Reusable.YG0t.astack_free_law_ok segs CtrlB.

(* ---------------------------------------------------------------------------------------------------------
   DISCHARGES II: the runtime and allocator lemmas of their owners (taken BY PATH; see the integration log
   takes.tsv (a working note, not in this delivery)). *)
(* a Theorem Labs lane: A.Rt.StackMalloc6.disco_stack_malloc6 (lib/A/Rt/StackMalloc6.v (an earlier version, blob 011e76fce0c, not in this delivery), a working branch 055c2ebca7f) *)
Let ASM6 := A.Rt.StackMalloc6.disco_stack_malloc6 fx CtrlB LAWS TFIB_SYMS.
(* a Theorem Labs lane: A.Rt.StackMalloc1.ctrl_stack_malloc1 (a working branch 1cf78f2ca9d) *)
Let ASM1 := A.Rt.StackMalloc1.ctrl_stack_malloc1 fx CtrlB LAWS TFIB_SYMS.
(* a Theorem Labs lane: A.Rt.StackMalloc2.ctrl_stack_malloc2 (a working branch 03746eea99b) *)
Let ASM2 := A.Rt.StackMalloc2.ctrl_stack_malloc2 fx CtrlB LAWS TFIB_SYMS.
(* a Theorem Labs lane: A.AFrameFlagLaw.frame_flag_law_ok (a working branch dddf4fa8e61) *)
Let FFL := A.AFrameFlagLaw.frame_flag_law_ok CtrlB.
(* a Theorem Labs lane: PALib / PALibF at CtrlB (a working branch 204fa48d73b); its instance A.ACtlTopLink.actl_RO
   (ro_below_ofl tfibsegs 0x9e380 0xa07c8) is found by instance search where the catalogue glue needs it *)
Let TL := A.ACtlTopLink.actl_PALib.
Let TLF := A.ACtlTopLink.actl_PALibF.
(* a Theorem Labs lane: A.ACtlGlobs (a working branch 86f27fff835) *)
Let GLOBS_A_MARKED : A.Prog.CtrlRo.globs_marked segs CtrlB GLOBS_A := A.ACtlGlobs.ctrl_globs_A_marked.
Let NAME_GLOB := A.ACtlGlobs.ctrl_name_glob_A.
(* a Theorem Labs lane: A.ACtlTopFacts.chain_of_cut (a working branch 05ede49c521) *)
Local Notation CHAIN_OF_CUT := (A.ACtlTopFacts.chain_of_cut CtrlB MT0 XL0 RLO RHI TFIB_LIB).

(* lib/A/ACtlG/A5.v's Section hypothesis seg_A5_run_F (the _F run of segment A5, A5.v:129): a Theorem Labs lane's
   A.ACtlG.A5Run.seg_A5_run_F_ok (lib/A/ACtlG/A5Run.v, a working branch ad4b0b8b346, blob c72e5a2f281; its statement is
   script-equal to A5.v:130-152) *)
Let seg_A5_run_F := @A.ACtlG.A5Run.seg_A5_run_F_ok fx.

(* ---------------------------------------------------------------------------------------------------------
   DISCHARGES III: the callee specs, each typed by ACtl.v section 1c's text at the top's instantiation.  The Section's
   only Hypotheses (OPEN) are, stated at the binder of the glue that needs them, TMB and TMB_LAY (owner a Theorem Labs lane: the
   reac_box_model_block spec at the catalogue list and at the image's list). *)
(* the core's api_env at CtrlB (ACtl.v section 9's tl_env term); A.Img0.rsegs is tfibsegs by definition
   (A.ProgBridge.tfibsegs_rsegs, proved by reflexivity) *)
Let errno_low : Reusable.YCbq.api_env A.Img0.rsegs CtrlB := A.ACeh.tl_env CtrlB TFIB_LIB.
(* two Theorem Labs lanes: A.Prog.C_reac_ctrl_parseP.pb_reac_ctrl_parse (a working branch 82af66506685; C_reac_ctrl_parseP.v
   7104412cbc2, C_reac_ctrl_parsePN.v a3d072bf4a2, the other eleven pieces and three chain files by path from a Theorem Labs lane's final pushes;
   reac_ctrl_parseF_rbody.v 70b963c3165 / reac_ctrl_parseF_rpost.v 8e949442472 from a Theorem Labs lane's fix,
   a working branch 2d60d34eb75b, which builds on bcmp_wrap_c.v 64293314ee8 (the blob this tree had at release c5e779efe8c)) *)
Let TPARSE : A.Prog.C_reac_ctrl_parse.treac_ctrl_parse_spec (SK := SK0) CtrlB RLO RHI :=
  A.Prog.C_reac_ctrl_parseP.pb_reac_ctrl_parse CtrlB RLO RHI errno_low ML SMP ASM1 TFIB_SYMS.
(* a Theorem Labs lane's instance ro_below_ofl tfibsegs 0x9e380 0xa07c8 (A.ACtlTopLink.actl_RO), for the catalogue glue's implicit RO. *)
#[local] Existing Instance A.ACtlTopLink.actl_RO.
(* the catalogue singleton's rows are marked: a Theorem Labs lane's ctrl_globs_A_marked at the row (0x9e800, 3256) = ctrl_globs_A_cat
   (A_CM_TBL = VAL (A_OBJ 17) = 0x9e800, CM_ROWS = 3256, C_reac_box_catalogue_match.v:72-73) *)
Let GLOBS_CM_MARKED : A.Prog.CtrlRo.globs_marked segs CtrlB GLOBS_CM.
Proof.
  intros ly S W mem md q sz Hin HAR. apply (GLOBS_A_MARKED ly S W mem md q sz); [|exact HAR].
  destruct Hin as [E|[]]. rewrite <- E. exact A.ACtlGlobs.ctrl_globs_A_cat.
Qed.
(* a Theorem Labs lane's reac_box_model_block spec at the catalogue list, TMB_stmt: the binder TMB of a Theorem Labs lane's
   pb_reac_box_catalogue_match (lib/A/Prog/reac_box_catalogue_match_glue.v:143: `Hypothesis TMB :
   C_reac_box_model_block.treac_box_model_block_spec (SK := SK) B GLOBS (BASE + AF_reac_box_model_block) RLO RHI`).
   OWNER a Theorem Labs lane: its walk theorem pb_reac_box_model_block on the strict C_reac_box_model_block.v 4631d95bcf7 (the blob
   this tree had at release c5e779efe8c) is proved (lib/A/Prog/reac_box_model_block_thm.v:126); its premises are ready here (a Theorem Labs lane's ACtlTmbFacts, a Theorem Labs lane's IntrinCpySetA). *)
Hypothesis TMB : TMB_stmt fx rc.
(* The four runtime contracts ctrl_emit_as's glue takes (a Theorem Labs lane's pb_ctrl_emit_as_stmt_on binders HMSF HMCF HBRF HFNF). *)
(* a Theorem Labs lane: A.Prog.asan_memsetF_on.asan_memset_holds_F_on at A.Prog.memset.memset_holds (as A/ACtlG/P3.v:342 passes it) *)
Let HMSF := A.Prog.asan_memsetF_on.asan_memset_holds_F_on A.Prog.memset.memset_holds.
(* a Theorem Labs lane: A.Prog.asan_memcpyF_on.asan_memcpy_holds_F_on *)
Let HMCF := A.Prog.asan_memcpyF_on.asan_memcpy_holds_F_on.
(* a Theorem Labs lane: A.Prog.reac_braid_encode_ns0F.reac_braid_encode_ns0_F_holds *)
Let HBRF := A.Prog.reac_braid_encode_ns0F.reac_braid_encode_ns0_F_holds.
(* a Theorem Labs lane: A.Prog.ctrl_finishF_on.ctrl_finish_F_holds_on *)
Let HFNF := A.Prog.ctrl_finishF_on.ctrl_finish_F_holds_on.
(* The fake-stack classes ctrl_lay_block calls (A.ProgWorld.stack_malloc_classes, ProgWorld.v:418: classes 0 / 1 / 2 / 6):
   a Theorem Labs lane's A.Rt.StackMalloc0.ctrl_stack_malloc0 (a working branch 46693b3c04c) and ASM1 / ASM2 / ASM6 above. *)
Let SMC : A.ProgWorld.stack_malloc_classes CtrlB.
Proof.
  intros cid [E|[E|[E|E]]]; subst cid.
  - exact (A.Rt.StackMalloc0.ctrl_stack_malloc0 fx CtrlB LAWS TFIB_SYMS).
  - exact ASM1.
  - exact ASM2.
  - exact ASM6.
Qed.
(* a Theorem Labs lane's reac_box_model_block spec at the IMAGE's globals list, TMB_LAY_stmt: the binder TMB of a Theorem Labs lane's
   pb_ctrl_lay_block (lib/A/Prog/C_ctrl_lay_block_glue.v:422, at GLOBS := ctrl_globs_A).  OWNER a Theorem Labs lane (as TMB above,
   at the other globals list). *)
Hypothesis TMB_LAY : TMB_LAY_stmt fx rc.
(* ctrl_lay_block's spec, the binder TLAY of a Theorem Labs lane's pb_ctrl_emit_as_stmt_on (G_ctrl_emit_as_on.v:82): a Theorem Labs lane's
   A.Prog.C_ctrl_lay_block_glue.pb_ctrl_lay_block (a working branch 695bdb7fc8c + 43e169975d6's seven pieces) at the image's
   globals list and RLO / RHI = PI_ctrl's bounds; its frame / catalogue image facts are a Theorem Labs lane's A.ACtlLayImg (a working branch
   55cdde245e8) and a Theorem Labs lane's BuildAsImg, with registration, alignment and range decided by computation; open only through
   TMB_LAY *)
Let TLAY : ltac:(let T := type of (A.Prog.G_ctrl_emit_as_on.pb_ctrl_emit_as_on (SK := SK0) CtrlB GLOBS_A RLO RHI TFIB_SYMS
  eq_refl eq_refl TL LAWS ML HMSF HMCF HBRF HFNF) in let T := eval hnf in T in lazymatch T with forall _ : ?A, _ => exact A end) :=
  A.Prog.C_ctrl_lay_block_glue.pb_ctrl_lay_block CtrlB GLOBS_A RLO RHI RELRO_IMG TL LAWS ML SMP ASF TLF TFIB_SYMS
    A.Prog.CtrlImg.ctrl_wx SMC TMB_LAY HMSF HMCF GLOBS_A_MARKED
    ltac:(vm_compute; repeat (first [left; reflexivity | right]))
    ltac:(vm_compute; repeat (first [left; reflexivity | right]))
    ltac:(split; [|split]; [apply Z.leb_le; vm_compute; reflexivity | apply Z.leb_le; vm_compute; reflexivity | vm_compute; reflexivity])
    ltac:(split; [|split]; [apply Z.leb_le; vm_compute; reflexivity | apply Z.leb_le; vm_compute; reflexivity | vm_compute; reflexivity])
    (A.ACtlLayImg.lay_img_fr_ro_CtrlB RLO RHI eq_refl eq_refl) (A.ACtlLayImg.lay_img_cat_ro_CtrlB RLO RHI eq_refl eq_refl)
    A.ACtlLayImg.lay_img_fr_rom.
(* The frame table's rows 3..9 are its read-only bytes (the binder HROWS of pb_ctrl_emit_as_stmt_on, G_ctrl_emit_as_on.v:90-92):
   a Theorem Labs lane's A.Prog.BuildAsImg.ba_img_rows (a working branch f1ae402bb2c, cbrec v12 ok) at RLO / RHI = PI_ctrl's bounds
   (eq_refl, as pb_ctrl_emit_as_on's HRLO / HRHI) *)
Let HROWS := A.Prog.BuildAsImg.ba_img_rows CtrlB TFIB_SYMS RLO RHI eq_refl eq_refl.
(* a Theorem Labs lane: A.Prog.G_ctrl_emit_as_on.pb_ctrl_emit_as_on (a working branch 98ea0cb7009) at the image's globals list; RLO / RHI are
   PI_ctrl's read-only bounds (eq_refl); the catalogue's three image facts are a Theorem Labs lane's (lib/A/Prog/BuildAsImg.v); the frame
   table's rows are a Theorem Labs lane's HROWS above, and its and the box's registration, alignment and range are decided by computation here: (0x9f7e0, 264) and (0x21140, 6) are rows 56 and 0 of ctrl_globs_A,
   0x9f7e0 mod 8 = 0, and both lie in [IMG_LO + 64, IMG_HI - 64) *)
Let TEMIT : ltac:(let T := type of (A.Prog.reac_ctrl_build_asTop.pb_reac_ctrl_build_as_top (SK := SK0) CtrlB TFIB_SYMS RLO RHI
  TL LAWS ML RELRO_IMG) in lazymatch T with forall _ : ?A, _ => exact A end) :=
  A.Prog.G_ctrl_emit_as_on.pb_ctrl_emit_as_on CtrlB GLOBS_A RLO RHI TFIB_SYMS eq_refl eq_refl TL LAWS ML HMSF HMCF HBRF HFNF TLAY
    IMG_SHADOW_VIS GLOBS_A_MARKED
    ltac:(vm_compute; repeat (first [left; reflexivity | right])) ltac:(vm_compute; reflexivity)
    A.Prog.BuildAsImg.ba_img_cat_glob A.Prog.BuildAsImg.ba_img_cat_al
    ltac:(vm_compute; repeat (first [left; reflexivity | right])) HROWS
    ltac:(split; apply Z.leb_le; vm_compute; reflexivity) A.Prog.BuildAsImg.ba_img_cat_rng
    ltac:(split; apply Z.leb_le; vm_compute; reflexivity) RELRO_IMG.

(* The callee specs of ACtl.v section 1c. *)
(* a Theorem Labs lane / a Theorem Labs lane: A.Prog.C_reac_ctrl_identity_reply.pb_reac_ctrl_identity_reply (C_reac_ctrl_identity_reply.v (at head lib/A/Prog/C_reac_ctrl_identity_reply.v:6527; from a working branch fe9a3b3c395))
   *)
Let TREPLY : A.Prog.C_reac_ctrl_identity_reply.treac_ctrl_identity_reply_spec (SK := SK0) CtrlB RLO RHI :=
  A.Prog.C_reac_ctrl_identity_reply.pb_reac_ctrl_identity_reply CtrlB RLO RHI RELRO_IMG LAWS TL TLF ML ASM1 SMP ASF FFL TPARSE.
(* a Theorem Labs lane: A.Prog.reac_ctrl_classify_box_frame_glue.pb_reac_ctrl_classify_box_frame (a working branch b41557cce10) *)
Let CLS : A.Prog.C_reac_ctrl_classify_box_frame.treac_ctrl_classify_box_frame_spec (SK := SK0) CtrlB RLO RHI :=
  A.Prog.reac_ctrl_classify_box_frame_glue.pb_reac_ctrl_classify_box_frame CtrlB RLO RHI RELRO_IMG LAWS TPARSE TFIB_SYMS.
(* a Theorem Labs lane: A.Prog.reac_box_catalogue_match_glue.pb_reac_box_catalogue_match (a working branch e0d89a7fb6d; its RO premise is
   a Theorem Labs lane's instance actl_RO) *)
Let CM_SPEC : A.Prog.C_reac_box_catalogue_match.treac_box_catalogue_match_spec (SK := SK0) CtrlB RLO RHI GLOBS_CM :=
  A.Prog.reac_box_catalogue_match_glue.pb_reac_box_catalogue_match CtrlB RLO RHI RELRO_IMG GLOBS_CM LAWS ML ASM2 SMP ASF TL TLF
    GLOBS_CM_MARKED TPARSE TMB TFIB_SYMS.
(* a Theorem Labs lane: A.Prog.reac_ctrl_build_asTop.pb_reac_ctrl_build_as_top (a working branch 8a72bf2e2fd; its seven image facts from
   lib/A/Prog/BuildAsImg.v, a working branch b23a4977599, and its globals certificate a Theorem Labs lane's ctrl_globs_A_marked_B, inside);
   BASE + AF_reac_ctrl_build_as = 0x848ac by computation *)
Let TBUILD : A.Prog.C_reac_ctrl_build_as.treac_ctrl_build_as_spec (SK := SK0) CtrlB GLOBS_A 0x848ac RLO RHI :=
  A.Prog.reac_ctrl_build_asTop.pb_reac_ctrl_build_as_top CtrlB TFIB_SYMS RLO RHI TL LAWS ML RELRO_IMG TEMIT IMG_SHADOW_VIS.
(* a Theorem Labs lane: A.Rt.Memchr.memchr_site_0_17 (a working branch a215ef7803b) *)
Let AMEMCHR_SITE := A.Rt.Memchr.memchr_site_0_17 CtrlB LAWS TFIB_SYMS.
(* two Theorem Labs lanes: A.Rt.Strcmp.ctrl_strcmp_tramp (STRCMP_TRAMP = 0x42964 = ACtl.v's strcmp entry) *)
Let H_strcmp := A.Rt.Strcmp.ctrl_strcmp_tramp CtrlB LAWS TFIB_SYMS.
(* a Theorem Labs lane: A.CtrlClose.ctrl_LS_LEAF (a working branch ea55b4292e7), at fuzz_ctrl's shape LSc *)
Let LS_LEAF := A.CtrlClose.ctrl_LS_LEAF.

(* ---------------------------------------------------------------------------------------------------------
   THE TOP. *)
Theorem ctl_lib_x_CtrlB_all : A.ACfn.tfib_lib_contract_x (LS := LSc) CtrlB MT0 XL0 XL0 RLO RHI.
Proof.
  exact (A.ACtl.ctl_lib_x_CtrlB (LS := LSc) AFREE AMALLOC
    TPARSE TREPLY GLOBS_A GLOBS_A_MARKED NAME_GLOB TBUILD CLS CM_SPEC AMEMCHR_SITE H_strcmp LS_LEAF CHAIN_OF_CUT
    (* seg_A1 *) (A.ACtlG.A1.glue_seg_A1 CtrlB MT0 XL0 RLO RHI LAWS TFIB_SYMS TFIB_LIB)
    (* seg_A2 *) (A.ACtlG.A2.glue_seg_A2 CtrlB MT0 XL0 RLO RHI LAWS)
    (* seg_A3 *) (A.ACtlG.A3.glue_seg_A3 CtrlB MT0 XL0 RLO RHI RELRO_IMG LAWS TFIB_SYMS)
    (* seg_A4 *) (A.ACtlG.A4.glue_seg_A4 CtrlB MT0 XL0 RLO RHI RELRO_IMG LAWS TFIB_SYMS)
    (* seg_A5 *) (A.ACtlG.A5.glue_seg_A5 CtrlB MT0 XL0 RLO RHI seg_A5_run_F LAWS)
    (* seg_R1_turn *) (A.ACtlG.R1_turn.glue_seg_R1_turn CtrlB MT0 XL0 RLO RHI LAWS)
    (* seg_R2 *) (A.ACtlG.R2.glue_seg_R2 CtrlB MT0 XL0 RLO RHI RELRO_IMG LAWS TFIB_SYMS)
    (* seg_R3 *) (A.ACtlG.R3.glue_seg_R3 CtrlB MT0 XL0 RLO RHI LAWS)
    (* seg_R4 *) (A.ACtlG.R4.glue_seg_R4 CtrlB MT0 XL0 RLO RHI RELRO_IMG LAWS TFIB_SYMS)
    (* seg_R5 *) (A.ACtlG.R5.glue_seg_R5 CtrlB MT0 XL0 RLO RHI RELRO_IMG LAWS TFIB_SYMS)
    (* seg_R6 *) (A.ACtlG.R6.glue_seg_R6 CtrlB MT0 XL0 RLO RHI RELRO_IMG LAWS TFIB_SYMS RELRO_CAT GLOBS_A NAME_GLOB TBUILD)
    (* seg_R7 *) (A.ACtlG.R7.glue_seg_R7 CtrlB MT0 XL0 RLO RHI LAWS TFIB_SYMS CHAIN_OF_CUT AMALLOC4 MO_MALLOC_OK RELRO_IMG RELRO_CAT)
    (* seg_R8 *) (A.ACtlG.R8.glue_seg_R8 CtrlB MT0 XL0 RLO RHI LAWS)
    (* seg_R9 *) (A.ACtlG.R9.glue_seg_R9 CtrlB MT0 XL0 RLO RHI RELRO_IMG LAWS TFIB_SYMS TPARSE)
    (* seg_R10 *) (A.ACtlG.R10.glue_seg_R10 CtrlB MT0 XL0 RLO RHI RELRO_IMG LAWS TFIB_SYMS TREPLY)
    (* seg_R11 *) (A.ACtlG.R11.glue_seg_R11 CtrlB MT0 XL0 RLO RHI LAWS)
    (* seg_R12 *) (A.ACtlG.R12.glue_seg_R12 CtrlB MT0 XL0 RLO RHI LAWS)
    (* seg_R13 *) (A.ACtlG.R13.glue_seg_R13 CtrlB MT0 XL0 RLO RHI LAWS TFIB_SYMS AFREE4 MT_FREE CHAIN_OF_CUT)
    (* seg_R14 *) (A.ACtlG.R14.glue_seg_R14 CtrlB MT0 XL0 RLO RHI RELRO_IMG RELRO_CAT LAWS TFIB_SYMS CM_SPEC)
    (* seg_R15 *) (A.ACtlG.R15.glue_seg_R15 CtrlB MT0 XL0 RLO RHI LAWS TFIB_SYMS AFREE4 MT_FREE CHAIN_OF_CUT)
    (* seg_R16 *) (A.ACtlG.R16.glue_seg_R16 CtrlB MT0 XL0 RLO RHI LAWS TFIB_SYMS AFREE4 MT_FREE CHAIN_OF_CUT)
    (* seg_R17 *) (A.ACtlG.R17.glue_seg_R17 CtrlB MT0 XL0 RLO RHI LAWS)
    (* seg_R18 *) (A.ACtlG.R18.glue_seg_R18 CtrlB MT0 XL0 RLO RHI LAWS TFIB_SYMS RELRO_CAT)
    (* seg_R19 *) (A.ACtlG.R19.glue_seg_R19 CtrlB MT0 XL0 RLO RHI TFIB_SYMS LAWS)
    (* seg_R20 *) (A.ACtlG.R20.glue_seg_R20 CtrlB MT0 XL0 RLO RHI LAWS TFIB_SYMS AFREE4 MT_FREE CHAIN_OF_CUT)
    (* seg_R21 *) (A.ACtlG.R21.glue_seg_R21 CtrlB MT0 XL0 RLO RHI LAWS TFIB_SYMS RELRO_CAT)
    (* seg_P1 *) (A.ACtlG.P1.glue_seg_P1 CtrlB MT0 XL0 RLO RHI LAWS)
    (* seg_P1_70 *) (A.ACtlG.P1_70.glue_seg_P1_70 CtrlB MT0 XL0 RLO RHI LAWS)
    (* seg_P2 *) (A.ACtlG.P2.glue_seg_P2 CtrlB MT0 XL0 RLO RHI LAWS)
    (* seg_P3 *) (A.ACtlG.P3.glue_seg_P3 CtrlB MT0 XL0 RLO RHI LAWS)
    (* seg_P4 *) (A.ACtlG.P4.glue_seg_P4 CtrlB MT0 XL0 RLO RHI LAWS)
    (* seg_P5 *) (A.ACtlG.P5.glue_seg_P5 CtrlB MT0 XL0 RLO RHI 9072 0x21200 LAWS TFIB_SYMS eq_refl eq_refl)
    (* seg_P6 *) (A.ACtlG.P6.glue_seg_P6 CtrlB MT0 XL0 RLO RHI 9072 0x21200 RELRO_IMG LAWS TFIB_SYMS TREPLY)
    (* seg_P7 *) (A.ACtlG.P7.glue_seg_P7 CtrlB MT0 XL0 RLO RHI LAWS TFIB_SYMS)
    (* seg_P8 *) (A.ACtlG.P8.glue_seg_P8 CtrlB MT0 XL0 RLO RHI LAWS)
    (* seg_P9 *) (A.ACtlG.P9.glue_seg_P9 CtrlB MT0 XL0 RLO RHI LAWS)
    (* seg_P10 *) (A.ACtlG.P10.glue_seg_P10 CtrlB MT0 XL0 RLO RHI LAWS)
    (* seg_P11 *) (A.ACtlG.P11.glue_seg_P11 CtrlB MT0 XL0 RLO RHI LAWS TFIB_SYMS RELRO_KIND_NAME)
    (* seg_P12 *) (A.ACtlG.P12.glue_seg_P12 CtrlB MT0 XL0 RLO RHI RELRO_IMG LAWS TFIB_SYMS QMARK_ROW)
    (* seg_F1 *) (A.ACtlG.F1.glue_seg_F1 CtrlB MT0 XL0 RLO RHI LAWS TFIB_SYMS CHAIN_OF_CUT AMALLOC4 MO_MALLOC_OK)
    (* seg_F2 *) (A.ACtlG.F2.glue_seg_F2 CtrlB MT0 XL0 RLO RHI LAWS RELRO_IMG TFIB_SYMS RELRO_KIND_NAME)
    (* seg_F3 *) (A.ACtlG.F3.glue_seg_F3 CtrlB MT0 XL0 RLO RHI RELRO_IMG LAWS TFIB_SYMS TPARSE)
    (* seg_F4 *) (A.ACtlG.F4.glue_seg_F4 CtrlB MT0 XL0 RLO RHI RELRO_IMG LAWS TFIB_SYMS TPARSE)
    (* seg_F5 *) (A.ACtlG.F5.glue_seg_F5 CtrlB MT0 XL0 RLO RHI LAWS)
    (* seg_F5_df0 *) (A.ACtlG.F5_df0.glue_seg_F5_df0 CtrlB MT0 XL0 RLO RHI LAWS)
    (* seg_F5_e0c *) (A.ACtlG.F5_e0c.glue_seg_F5_e0c CtrlB MT0 XL0 RLO RHI LAWS)
    (* seg_F5_e10 *) (A.ACtlG.F5_e10.glue_seg_F5_e10 CtrlB MT0 XL0 RLO RHI LAWS)
    (* seg_F6_e28 *) (A.ACtlG.F6_e28.glue_seg_F6_e28 CtrlB MT0 XL0 RLO RHI LAWS)
    (* seg_F6_ebc *) (A.ACtlG.F6_ebc.glue_seg_F6_ebc CtrlB MT0 XL0 RLO RHI RELRO_IMG LAWS TFIB_SYMS TPARSE)
    (* seg_F7 *) (A.ACtlG.F7.glue_seg_F7 CtrlB MT0 XL0 RLO RHI LAWS TFIB_SYMS)
    (* seg_F8 *) (A.ACtlG.F8.glue_seg_F8 CtrlB MT0 XL0 RLO RHI LAWS TFIB_SYMS)
    (* seg_F9 *) (A.ACtlG.F9.glue_seg_F9 CtrlB MT0 XL0 RLO RHI LAWS RELRO_IMG TFIB_SYMS TREPLY)
    (* seg_F10 *) (A.ACtlG.F10.glue_seg_F10 CtrlB MT0 XL0 RLO RHI LAWS)
    (* seg_F11_fd4 *) (A.ACtlG.F11_fd4.glue_seg_F11_fd4 CtrlB MT0 XL0 RLO RHI LAWS)
    (* seg_F11_014 *) (A.ACtlG.F11_014.glue_seg_F11_014 CtrlB MT0 XL0 RLO RHI LAWS)
    (* seg_F12 *) (A.ACtlG.F12.glue_seg_F12 CtrlB MT0 XL0 RLO RHI LAWS TFIB_SYMS)
    (* seg_F13 *) (A.ACtlG.F13.glue_seg_F13 CtrlB MT0 XL0 RLO RHI LAWS)
    (* seg_F14 *) (A.ACtlG.F14.glue_seg_F14 CtrlB MT0 XL0 RLO RHI LAWS)
    (* seg_F15 *) (A.ACtlG.F15.glue_seg_F15 CtrlB MT0 XL0 RLO RHI LAWS)
    (* seg_F15b *) (A.ACtlG.F15b.glue_seg_F15b CtrlB MT0 XL0 RLO RHI LAWS)
    (* seg_F16 *) (A.ACtlG.F16.glue_seg_F16 CtrlB MT0 XL0 RLO RHI LAWS)
    (* seg_F17 *) (A.ACtlG.F17.glue_seg_F17 CtrlB MT0 XL0 RLO RHI LAWS)
    (* seg_F17b *) (A.ACtlG.F17b.glue_seg_F17b CtrlB MT0 XL0 RLO RHI LAWS)
    (* seg_F18 *) (A.ACtlG.F18.glue_seg_F18 CtrlB MT0 XL0 RLO RHI LAWS TFIB_SYMS)
    (* seg_F19 *) (A.ACtlG.F19.glue_seg_F19 CtrlB MT0 XL0 RLO RHI LAWS TFIB_SYMS)
    (* seg_F20 *) (A.ACtlG.F20.glue_seg_F20 CtrlB MT0 XL0 RLO RHI LAWS)
    (* seg_F21 *) (A.ACtlG.F21.glue_seg_F21 CtrlB MT0 XL0 RLO RHI LAWS)
    (* seg_F22 *) (A.ACtlG.F22.glue_seg_F22 CtrlB MT0 XL0 RLO RHI LAWS)
    (* seg_F23 *) (A.ACtlG.F23.glue_seg_F23 CtrlB MT0 XL0 RLO RHI LAWS TFIB_SYMS)
    (* seg_F24 *) (A.ACtlG.F24.glue_seg_F24 CtrlB MT0 XL0 RLO RHI LAWS)
    (* seg_F25 *) (A.ACtlG.F25.glue_seg_F25 CtrlB MT0 XL0 RLO RHI LAWS)
    (* seg_F26 *) (A.ACtlG.F26.glue_seg_F26 CtrlB MT0 XL0 RLO RHI LAWS)
    (* seg_F27 *) (A.ACtlG.F27.glue_seg_F27 CtrlB MT0 XL0 RLO RHI LAWS)
    (* seg_F28a *) (A.ACtlG.F28a.glue_seg_F28a CtrlB MT0 XL0 RLO RHI LAWS)
    (* seg_F28b *) (A.ACtlG.F28b.glue_seg_F28b CtrlB MT0 XL0 RLO RHI LAWS)
    (* seg_F29 *) (A.ACtlG.F29.glue_seg_F29 CtrlB MT0 XL0 RLO RHI LAWS)
    (* seg_F30 *) (A.ACtlG.F30.glue_seg_F30 CtrlB MT0 XL0 RLO RHI RELRO_IMG LAWS TFIB_SYMS CLS)
    (* seg_F31 *) (A.ACtlG.F31.glue_seg_F31 CtrlB MT0 XL0 RLO RHI LAWS TFIB_SYMS)
    (* seg_F32 *) (A.ACtlG.F32.glue_seg_F32 CtrlB MT0 XL0 RLO RHI LAWS)
    (* seg_F33 *) (A.ACtlG.F33.glue_seg_F33 CtrlB MT0 XL0 RLO RHI LAWS)
    (* seg_F34 *) (A.ACtlG.F34.glue_seg_F34 CtrlB MT0 XL0 RLO RHI RELRO_CAT LAWS TFIB_SYMS IMG_SHADOW_VIS)
    (* seg_F35 *) (A.ACtlG.F35.glue_seg_F35 CtrlB MT0 XL0 RLO RHI LAWS TFIB_SYMS)
    (* seg_F36_827f0 *) (A.ACtlG.F36_827f0.glue_seg_F36_827f0 CtrlB MT0 XL0 RLO RHI RELRO_IMG RELRO_CAT LAWS TFIB_SYMS CM_SPEC)
    (* seg_F36_827f4 *) (A.ACtlG.F36_827f4.glue_seg_F36_827f4 CtrlB MT0 XL0 RLO RHI RELRO_IMG RELRO_CAT LAWS TFIB_SYMS CM_SPEC)
    (* seg_F36_82810 *) (A.ACtlG.F36_82810.glue_seg_F36_82810 CtrlB MT0 XL0 RLO RHI RELRO_IMG RELRO_CAT LAWS TFIB_SYMS CM_SPEC)
    (* seg_F36_8281c *) (A.ACtlG.F36_8281c.glue_seg_F36_8281c CtrlB MT0 XL0 RLO RHI RELRO_IMG RELRO_CAT LAWS TFIB_SYMS CM_SPEC)
    (* seg_F36_828b8 *) (A.ACtlG.F36_828b8.glue_seg_F36_828b8 CtrlB MT0 XL0 RLO RHI RELRO_IMG RELRO_CAT LAWS TFIB_SYMS CM_SPEC)
    (* seg_F37 *) (A.ACtlG.F37.glue_seg_F37 CtrlB MT0 XL0 RLO RHI LAWS TFIB_SYMS TFIB_LIB CHAIN_OF_CUT AFREE4 MT_FREE)
    (* seg_F38 *) (A.ACtlG.F38.glue_seg_F38 CtrlB MT0 XL0 RLO RHI LAWS)
    (* seg_X1 *) (A.ACtlG.X1.glue_seg_X1 CtrlB MT0 XL0 RLO RHI RELRO_IMG LAWS TFIB_SYMS AMEMCHR_SITE)
    (* seg_X2 *) (A.ACtlG.X2.glue_seg_X2 CtrlB MT0 XL0 RLO RHI LAWS)
    (* seg_Jrel *) (A.ACtlG.Jrel.glue_seg_Jrel CtrlB MT0 XL0 RLO RHI LAWS)
    (* seg_Y1 *) (A.ACtlG.Y1.glue_seg_Y1 CtrlB MT0 XL0 RLO RHI LAWS)
    (* seg_Y3 *) (A.ACtlG.Y3.glue_seg_Y3 CtrlB MT0 XL0 XL0 RLO RHI LAWS MO_LE AIL)).
Qed.

End CtlAll.
