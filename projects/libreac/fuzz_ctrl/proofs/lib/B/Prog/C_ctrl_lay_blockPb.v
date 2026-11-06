(* pb_ctrl_lay_block: the proof of tctrl_lay_block_spec (lib/B/Prog/C_ctrl_lay_block.v) for ctrl_lay_block (0x86104)
   of fuzz_ctrl's ASan+UBSan build (image B, libreac v1.9.0), in cgif's caller-journal form.  A Theorem Labs lane.
   rule 24: no function proved here (glue of the route (C) footprint run lib/B/Prog/ctrl_lay_blockF_on.v, the _on
   copy of the proved lib/B/Prog/ctrl_lay_blockF.v (not in this delivery), through the cut lemmas of lib/B/Prog/ctrl_lay_block_cutsF.v).

   Plan of record: analyses/libreac/fuzz_ctrl/glue-B/ctrl_lay_block-B-glue-plan.md (regions R1..R4).  This file only
   chains the region lemmas:
     R1   lay_to_ret        (ctrl_lay_block_gR1.v):   entry 0x86104 -> the class-1 request -> lay_D1 at 0x8617c
     R2   lay_R23           (ctrl_lay_block_gR23.v):  lay_D1 -> lay_D4 at the flag store 0x86440 (k <> 3..9),
                                                      or lay_Dbox at the box call 0x865d8 (k = 3..9)
     box  lay_box_arm       (ctrl_lay_block_gbox.v):  lay_Dbox -> reac_box_model_block (TMB) -> lay_D3 at 0x86370
     R3   lay_R3            (ctrl_lay_block_gR3.v):   lay_D3 -> lay_D4
     R4   lay_R4            (ctrl_lay_block_gR4.v):   lay_D4 -> the class-1 release -> tctrl_lay_block_post
   Route (C): the cut lemmas take SR0 : shadow_rw_on (ctrl_lay_block_shadow_R ...) m, which each region proves at its
   cut from the cut's own shadow regions (gctx lay_RR_cover over a Theorem Labs lane's cut_shadow / img_shadow; no
   AR_states_vis0_shadow, no ctlrt_of_AR_stmt).  The runtime callees' footprint _on contracts (MEMS, MEMC) are
   discharged by a Theorem Labs lane's proofs (asan_memset_holds_F_on, asan_memcpy_holds_F_on); wx_segs_nowrap by computation (lay_R4_wx); the
   image shadow by its proof (ACtlCutC.ctrl_img_shadow_vis).  Every B ProgWorld statement the regions read is PROVED
   (a Theorem Labs lane) and cited by its lemma in the region files, so none is a premise here.  The remaining Section
   hypotheses are core / runtime / callee / image facts (decisions.md item 15 (a working note, not in this delivery): no frame-route identifier in them).

   CLOSURE: the _F files and the region files are Required QUALIFIED; the statement is C_ctrl_lay_block's. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import
YK04 YA0n YG00 YG0a YG01 YG0f YG0n YG0d YCbq YE01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YB1v YF0m.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require ProgWorld ACtlCutC.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require CtrlRo asan_stack_malloc_c asan_memset_cF_on
  asan_memcpy_cF_on asan_memsetF_on asan_memcpyF_on memset C_reac_box_model_block.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import C_ctrl_lay_block.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require ctrl_lay_block_gbase ctrl_lay_block_gD3
  ctrl_lay_block_gD4 ctrl_lay_block_gR1 ctrl_lay_block_gR23 ctrl_lay_block_gbox ctrl_lay_block_gR3 ctrl_lay_block_gR4.
Import ListNotations.
Open Scope Z_scope.

Section pb.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {SK : lib.Reusable.YI16.sink_head}.
#[local] Notation SEGS := lib.Reusable.YB1v.tfibsegs.
Variables RLO RHI : Z.
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> in_img SEGS a.
Variable B : asyms.                  (* := lib.Reusable.YF0m.CtrlB at the top *)
Variable GLOBS : list (Z * Z).       (* := B.ProgBridgeData.ctrl_ro_globs at the top *)

(* core and the class-1 / class-0 fake-stack rules *)
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis errno_low : api_env SEGS B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASM1 : astack_malloc_realizes SEGS B 1.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis PC1 : pc_stack_malloc (as_code B) 1 = B.Prog.asan_stack_malloc_c.ASAN_STACK_MALLOC_1.
Hypothesis CTS : lib.Reusable.YF0m.CtrlTSyms B.
(* image facts (the top: B.ProgBridgeData.ctrl_ro_globs_marked); the image shadow is PROVED (ACtlCutC) *)
Hypothesis HGM : B.Prog.CtrlRo.globs_marked SEGS B GLOBS.
Let HIMGSH : B.Prog.CtrlRo.img_shadow_vis SEGS B := B.ACtlCutC.ctrl_img_shadow_vis B CTS LAWS.
(* the callee reac_box_model_block (a Theorem Labs lane's statement) *)
Hypothesis TMB : B.Prog.C_reac_box_model_block.treac_box_model_block_spec RLO RHI B GLOBS.
(* the runtime callees in their route (C) footprint _on forms, discharged by a Theorem Labs lane's proofs (a Theorem Labs lane's base of
   record a working branch 3b8fa882b0e, files by path: asan_memsetF_on.v / asan_memcpyF_on.v) *)
Let MEMS : B.Prog.asan_memset_cF_on.asan_memset_contract_F_on :=
  B.Prog.asan_memsetF_on.asan_memset_holds_F_on B.Prog.memset.memset_holds.
Let MEMC : B.Prog.asan_memcpy_cF_on.asan_memcpy_contract_F_on := B.Prog.asan_memcpyF_on.asan_memcpy_holds_F_on.

Let HWX : lib.Reusable.YK04.wx_segs_nowrap SEGS := B.Prog.ctrl_lay_block_gR4.lay_R4_wx.

Theorem pb_ctrl_lay_block : tctrl_lay_block_spec RLO RHI B GLOBS.
Proof.
  unfold tctrl_lay_block_spec. intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p f md g fr tb mb nb gb.
  repeat lazymatch goal with |- _ -> _ => intro end.
  (* the spec premises region R2 (and the box arm) read, in the spec's text *)
  assert (HA : B.Prog.ctrl_lay_block_gR23.lay_args RLO RHI B GLOBS STK sp0 FP ly S own lyc Sc W memc regs
                 p f md g fr tb mb nb gb)
    by (unfold B.Prog.ctrl_lay_block_gR23.lay_args; repeat (first [assumption | split])).
  (* R1: entry -> the class-1 request -> lay_D1 *)
  eapply (B.Prog.ctrl_lay_block_gR1.lay_to_ret (SK := SK)).
  all: try eassumption.
  intros S2 regs2 mem2 md2 pos HD1.
  (* R2: lay_D1 -> lay_D4 (k <> 3..9) or lay_Dbox (k = 3..9) *)
  eapply (B.Prog.ctrl_lay_block_gR23.lay_R23 (SK := SK)).
  all: try exact HA. all: try exact HD1. all: try eassumption.
  - (* R4 *)
    intros ly3 S3 W3 regs3 mem3 md3 HD4.
    eapply (B.Prog.ctrl_lay_block_gR4.lay_R4 (SK := SK)).
    all: try exact HD4. all: try eassumption.
  - (* the box arm, then R3, then R4 *)
    intros regsB mem3 md3 HDbox.
    eapply (B.Prog.ctrl_lay_block_gbox.lay_box_arm (SK := SK)).
    all: try exact HA. all: try exact HDbox. all: try eassumption.
    intros ly4 S4 W4 regs4 mem4 md4 HD3.
    eapply (B.Prog.ctrl_lay_block_gR3.lay_R3 (SK := SK)).
    all: try exact HD3. all: try eassumption.
    intros ly3 S3 W3 regs3 mem3' md3' HD4.
    eapply (B.Prog.ctrl_lay_block_gR4.lay_R4 (SK := SK)).
    all: try exact HD4. all: try eassumption.
Qed.

End pb.

Print Assumptions pb_ctrl_lay_block.
About pb_ctrl_lay_block.
