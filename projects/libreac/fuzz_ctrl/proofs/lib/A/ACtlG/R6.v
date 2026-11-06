(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/bignum/lib/BnP/BnKit2.v, with its module paths and module names changed; 1014 of its 1028 lines of code are new or changed and 33 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/tx_put.v, with its module paths and module names changed; 2422 of its 2466 lines of code are new or changed and 984 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtlW3a.v, with its module names changed; 4006 of its 4152 lines of code are new or changed and 2320 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtlW4b.v, with its module paths and module names changed; 782 of its 845 lines of code are new or changed and 4089 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/ACtlG/F12.v; 871 of its 911 lines of code are new or changed and 805 lines of the source are left out. *)
(* lib/A/ACtlG/R6.v -- GLUE for stage seg_R6 of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput
   (lib/A/ACtl.v:672).  Written by a Theorem Labs lane (piece W2a); single writer.
   rule 24: no function proved (stage glue of a walk; proves no function, kind: segment lemma).
   Pattern: glue-pattern.md sections 3, 4, 8 (a working note, not in this delivery); pilot ACtlG/A5.v.

   WHAT IT PROVES
     glue_seg_R6 : forall POST (b : nat),
       CF POST (ix_cut C_A815ec_at [Z.of_nat b]) -> CF POST (ix_cut C_A815cc_at [Z.of_nat b])
   with ACtl.v's own CF notation (SK := A.AE2k.tfib_sink_head, FP := []), i.e. exactly ACtl.v's Section hypothesis
   seg_R6.  Segment R6 is 0x815cc -> 0x815ec, turn b of the round trip: the four build_as argument spill loads
   ([A+112] the catalogue row, [A+168] our[] = fr+2624, [A+104] round_trip.box, [A+96] 0x1234), a2 = s7 = b,
   a6 = a7 = 0, and `jal reac_ctrl_build_as` (0x815e8, entry 0x848ac), which returns to 0x815ec = the exit cut.

   SPLIT RULE (a) (a Theorem Labs lane 04:01Z): reac_ctrl_build_as is a cgif-form fake-stack callee, so the run is split
   AT the call: the stretch before it is lib/A/Prog/Seg/R6Fs.v's r6_evt_pre_Fs (this lane's file, narrowed-stretch
   rule), the call is consumed through a Theorem Labs lane's treac_ctrl_build_as_spec (lib/A/Prog/C_reac_ctrl_build_as.v,
   the named Section hypothesis TBUILD), and there is no stretch after it.

   THE PROOF
   G1  the entry cut at index [Z.of_nat b]: C_A815cc_at's 25 conjuncts (ACtlCutP.v:1274-1294), FRAC, RS.
   G2  the stretch's premises: the spill base A = s1 (FRAC), the four spill cells (spills 96 / 104 / 112, PRO's
       spill 168), their visibility (the journal's stack clause: they lie in [sp, c_sp)).
   G3  the walk moved from regs3 to mkR_of regs3 (YA0nR.SRr_xregs_eqv), the binders instantiated with
       reg_get regs3 r, so the stretch's end map R is an explicit mkR.
   G4  r6_evt_pre_Fs at RNG_W (w_H W3), lifted with YA0nR.SRr_fevt (the stretch writes nothing).
   G5  at the callee entry 0x848ac (= BASE + AF_reac_ctrl_build_as): the journal crosses the model
       materialization by YCbq.ajournal_exec (empty write set), and TBUILD applies with o = fr + 544,
       md = SM.mrow (c_in cx), d = fr + 2624, kind = b, c16 = 0x1234, ns = 0, mb = the catalogue row,
       nb = its name, db = SM.OUR (c_in cx), sb = SM.box6; its 46 caller premises from the cut, the journal's
       AR (frames_bounds, al_frames, al_blocks, al_client_img) and the image (vm_compute checks).
   G6  TBUILD's post (tctrl_emit_as_post): the return configuration at ra = 0x815ec IS the exit cut; the journal at
       k + 0 (EV_EMIT = EV_LAY = EV_BMB = 0); aregs_preserved carries every callee-saved pin; a0 = R, which is
       SM.rt_n (c_in cx) b (the emitter's E / len are build_as's ba_E / 52 + 36 n row by row, r6_E_eq /
       r6_len_eq); the emitted frame is SM.rt_F (c_in cx) b (r6_blk_eq) and becomes raw bytes by
       ProgWorld.ctl_out_bytes; every other memory conjunct is kept by tcj_kept through r6_keep_mem (stack
       clause for the spill area and the saved registers, frame clause for the class-6 frame outside the written
       [fr + 544, fr + 544 + R), frame-shadow clause, live-block clause for the input block); the input block's
       shadow from the post's AR (BLOCK_SHADOW); ctl_rt_C (route C: the next cut's ctl_from premise) from
       ProgWorldCtlRtC.ctl_rt_C_of_AR at the post's AR and the read-only view carried by the journal
       (KitMem.kitmem_arodataS_journal).

   SECTION HYPOTHESES (exact text at the declarations below)
   - RELRO_IMG, LAWS, TFIB_SYMS: ACtl.v's own Section hypotheses (ACtl.v:179, :183, :191), same text.
   - RELRO_CAT: ACtl.v's own Section hypothesis (Batch3, glue base d36efc6152d; ACtl.v:205), same text:
     RLO <= SlotModel.CAT /\ SlotModel.CAT + SlotModel.CAT_N * SlotModel.CAT_ROW <= RHI.  The pointwise form this
     stage reads (every catalogue byte in [RLO, RHI)) is the local lemma r6_relro_cat (CAT_N * CAT_ROW = 3256).
   - GLOBS_A (Variable) and NAME_GLOB: the registered-globals list the build_as spec takes (ACtl.v:319, same text;
     CtrlRo.v: the composition fixes the list and discharges globs_marked) and the fact that each catalogue row's
     name string lies in one of its globals (the spec's names premise, C_reac_ctrl_build_as.v:115); NAME_GLOB is
     added to ACtl.v's Section with this text by a Theorem Labs lane under another Theorem Labs lane, so the top supplies it.
   - TBUILD: ACtl.v's own (ACtl.v:325, same text): a Theorem Labs lane's treac_ctrl_build_as_spec at 0x848ac (= BASE +
     AF_reac_ctrl_build_as).
   - BLOCK_SHADOW (the input block's shadow at the exit) is a Theorem Labs lane's PROVED
     A.ProgWorldShadow.ctl_block_shadow_of_AR, named locally by a Let.  Route (C): VIS0 / OWNED_RO are gone (the exit's
     ctl_rt_C comes from A.ProgWorldCtlRtC.ctl_rt_C_of_AR, which takes neither).
   Required, not assumed: Seg/R6Fs.v r6_evt_pre_Fs (this lane's split), KitMem (kitmem_own6, kitmem_rng_win,
   kitmem_arodataS_journal, kitmem_bytes_at_mrd, kitmem_addressable_mrd, kitmem_rw_cells_mrd, kitmem_saved_len),
   Kit (kit_wx, kit_segs_low), ProgWorld (rw_cells_CB_of_present, ctl_out_bytes, arodata_okP_of_S),
   ProgWorldCtlRt (seg_rom_none_high), ProgWorldCtlRtC (ctl_rt_C_of_AR), Seg/R6.v's Qed facts (r6_rtn, r6_row_len, r6_name_facts,
   r6_emfr_len, r6_baX_len).
   LOCAL Qed HELPERS that KitMem lacks (statements sent to a Theorem Labs lane): r6_keep_mem (a byte the callee's tcj_kept
   keeps in VIEW, present and off the rom, is the same raw byte), r6_frac_keep (FRAC at a new map / memory equal on
   FRAC's regions in mrd form, BY SHAPE, so it RE-ESTABLISHES FRAC including the announced fr + 4088 trailer),
   r6_spill_keep, r6_range_addr (raw addressable + visible shadow -> range_addressable over the view),
   r6_garr8_of_mbyte, r6_garr8_ro (+ the vm_compute image checks r6_box_chk / r6_cat_chk / r6_name_chk),
   r6_E_eq / r6_len_eq / r6_blk_eq (the emitter's row functions are build_as's), r6_rst_len (RID 38 / RFG 72;
   with Seg/F20.v's four length lemmas restated over the pure models, so Seg/F20.v is not loaded).
   CLOSURE: every project module is Required by its absolute name and named through a Module alias of that name
   (the six Reusable twins and the lib/Lib twins of lib/A/Bz); no Import / Export of a project module; no
   statement names a frame-route identifier.
   START-UP TABLE VALUES READ: AF0m's Tfib_owned_static and TFIB_ERRNO (TFIB_SYMS ts_owned / ts_errno) for the
   box / catalogue / name byte reads; checked against the record AF0m (e56483f863b): no overlap, errno the same.
   CAVEAT (zero-shadow row, a Theorem Labs lane 05:4xZ): NOT applicable: this stage reads no image byte's shadow (the
   spec's image premises are byte values only: round_trip.box, the catalogue row, the row name). *)

From Coq Require Import ZArith List Lia Permutation Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI04.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI16.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YA0n.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YA0nR.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG00.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG01.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0f.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0n.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0d.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0v.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YC5d.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YCbq.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YE01.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI00.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK04.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK06.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK0s.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YP09.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.APostBase.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AB1v.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AE2k.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACfn.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AF0m.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AsanRT.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlK.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCut.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCutP.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgBridge.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgWorld.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgWorldCtlRt.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgWorldCtlRtC.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgWorldShadow.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlG.Kit.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlG.KitMem.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.PaTable.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.CtrlList.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.CtrlPa.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.CtrlImg.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.CtrlBase.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.CtrlCallerJ.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.C_ctrl_lay_block.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.C_reac_box_model_block.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.C_ctrl_emit_as.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.C_reac_ctrl_build_as.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.SlotModel.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.R6.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.R6Fs.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Img0.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Step.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.reac_ctrl_build_as_c.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcEmit.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcLay.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcFin.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcPorts.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcSynth.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcBox.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcIdentModel.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcFrag.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcFragLib.
Import ListNotations.
Local Open Scope Z_scope.

(* Full-path aliases: every project module this file names. *)
Module CK11 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
Module CK1b := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.
Module CI04 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI04.
Module CI16 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI16.
Module CM05 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.
Module CO09 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.
Module YA0n := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YA0n.
Module YA0nR := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YA0nR.
Module YG00 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG00.
Module YG01 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG01.
Module YG0f := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0f.
Module YG0n := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0n.
Module YG0d := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0d.
Module YG0v := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0v.
Module YC5d := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YC5d.
Module YCbq := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YCbq.
Module YE01 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YE01.
Module YI00 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI00.
Module YK04 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK04.
Module YK06 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK06.
Module YK0s := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK0s.
Module YP09 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YP09.
Module APB := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.APostBase.
Module AB1v := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AB1v.
Module AE2k := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AE2k.
Module ACfn := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACfn.
Module AF0m := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AF0m.
Module ART := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AsanRT.
Module ACtlK := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlK.
Module ACtlCut := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCut.
Module ACtlCutP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCutP.
Module PBr := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgBridge.
Module PW := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgWorld.
Module PWC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgWorldCtlRt.
Module PWCC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgWorldCtlRtC.
Module Kit := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlG.Kit.
Module KM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlG.KitMem.
Module CPT := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.PaTable.
Module CLS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.CtrlList.
Module CPA := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.CtrlPa.
Module CIM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.CtrlImg.
Module CBS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.CtrlBase.
Module CCJ := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.CtrlCallerJ.
Module LAY := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.C_ctrl_lay_block.
Module BMB := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.C_reac_box_model_block.
Module EMA := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.C_ctrl_emit_as.
Module BAS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.C_reac_ctrl_build_as.
Module SM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.SlotModel.
Module SR6 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.R6.
Module SR6Fs := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.R6Fs.
Module Img0 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Img0.
Module LEF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.
Module LMS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Module LR6 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.
Module LMem := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Module LCE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells.
Module LST := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Step.
Module PB := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.reac_ctrl_build_as_c.
Module RE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcEmit.
Module RL := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcLay.
Module RF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcFin.
Module RP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcPorts.
Module RS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcSynth.
Module RB := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcBox.
Module RIM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcIdentModel.
Module RFR := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcFrag.
Module RFL := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcFragLib.

(* The core's segment list, as ACtlCut.v and ACtl.v bind it. *)
Local Notation segs := AB1v.tfibsegs.
(* The PA image's values, as C_reac_ctrl_build_as.v writes them (its VAL notation). *)
Local Notation VAL := (@CPA.pa_val _ CLS.ctrl_listing CIM.PI_ctrl).

(* =========================================================================================================
   1. Closed helper lemmas (no Section argument). *)

(* ---- the emitter's row functions are build_as's, row by row (b = 0 .. 6, r = ba_row b) ---- *)
Lemma r6_E_eq : forall (b : nat) n mb, (b <= 6)%nat ->
  RE.em_E (EMA.EM_L (PB.ba_row (Z.of_nat b))) (EMA.EM_G (PB.ba_row (Z.of_nat b))) n (RE.em_hid mb) =
  PB.ba_E n mb (Z.of_nat b).
Proof.
  intros b n mb Hb.
  do 7 (destruct b as [|b]; [reflexivity|]). lia.
Qed.

Lemma r6_len_eq : forall (b : nat) n, (b <= 6)%nat ->
  RE.em_len (EMA.EM_L (PB.ba_row (Z.of_nat b))) n = 52 + 36 * n.
Proof.
  intros b n Hb.
  do 7 (destruct b as [|b]; [reflexivity|]). lia.
Qed.

Lemma r6_blk_eq : forall (b : nat) md mb nb, (b <= 6)%nat ->
  RF.fin (EMA.EM_C (PB.ba_row (Z.of_nat b))) 0 0 (RL.ly_Z md mb nb (RL.ly_bb (PB.ba_row (Z.of_nat b)))) =
  PB.ba_X md mb nb (Z.of_nat b).
Proof.
  intros b md mb nb Hb.
  do 7 (destruct b as [|b]; [reflexivity|]). lia.
Qed.

(* the turn's frame length: 0, or in [124, 1492] (Seg/R6.v r6_rtn) *)
Lemma r6_rtn_range : forall inp b, 0 <= SM.rt_n inp b <= 1492.
Proof.
  intros inp b. destruct (Z.eq_dec (SM.rt_n inp b) 0) as [E|E]; [lia|].
  pose proof (SR6.r6_rtn inp b E). lia.
Qed.

(* RID / RFG keep their lengths (38, 72) over the turns.  The four length facts are Seg/F20.v's fg_first_len /
   fg_st_len / rp_id_len / fg_id_len (:119-166), restated over the pure models (RcFrag / RcFragLib / RcIdentModel,
   already in this file's closure) so that this glue file does not load the other segment's frame-route file. *)
Lemma r6_fg_first_len : forall st g, length st = 72%nat -> length g = 50%nat -> 1 <= RFR.fg_n g <= 22 ->
  length (RFR.fg_first st g) = 72%nat.
Proof.
  intros st g HL HG Hn. unfold RFR.fg_first, RFR.fg_body.
  rewrite !length_app, length_skipn, (RFL.rf_bsl_length g 6 6),
    (RFL.rf_bsl_length g 27 (RFR.fg_n g)) by lia.
  cbn [length]. lia.
Qed.

Lemma r6_fg_st_len : forall len st g, length st = 72%nat -> length g = 50%nat ->
  length (SM.fg_st len st g) = 72%nat.
Proof.
  intros len st g HL HG. unfold SM.fg_st, SM.fcls.
  rewrite (RFL.rf_class_nn 1 1 1 1 1) by lia.
  destruct (RFR.fg_fr len g) eqn:FR; cbn [negb]; [|cbn [SM.fg_next]; exact HL].
  assert (Hn : 1 <= RFR.fg_n g <= 22).
  { unfold RFR.fg_fr in FR. rewrite !andb_true_iff in FR.
    destruct FR as (FR & _). destruct FR as (FR & Hn2). destruct FR as (_ & Hn1).
    apply Z.leb_le in Hn1. apply Z.leb_le in Hn2. lia. }
  destruct (RFR.bat g 19 =? 1); [cbn [SM.fg_next]; apply r6_fg_first_len; assumption|].
  destruct (RFR.fg_keep st g) eqn:KEEP; cbn [negb]; [|cbn [SM.fg_next]; apply RFL.rf_clear_length; exact HL].
  assert (HT : RFR.fg_T st g <= 64).
  { unfold RFR.fg_keep in KEEP. rewrite !andb_true_iff in KEEP. destruct KEEP as (_ & KEEP).
    apply Z.leb_le in KEEP. exact KEEP. }
  destruct (RFR.fg_close st g); cbn [negb SM.fg_next];
    apply RFL.rf_clear_length, RFL.rf_fg_join_length; assumption.
Qed.

Lemma r6_rp_id_len : forall idb len g, length idb = RIM.ID_SIZE -> length (SM.rp_id idb len g) = RIM.ID_SIZE.
Proof.
  intros idb len g H. unfold SM.rp_id.
  match goal with |- context [if ?c then _ else _] => destruct c end; [apply RIM.ING_length; exact H | exact H].
Qed.

Lemma r6_fg_id_len : forall idb len st g, length idb = RIM.ID_SIZE ->
  length (SM.fg_id idb len st g) = RIM.ID_SIZE.
Proof.
  intros idb len st g H. unfold SM.fg_id.
  destruct (SM.fg_rf len st g =? 1); [apply RIM.ING_length; exact H | exact H].
Qed.

Lemma r6_rst_len : forall inp (b : nat),
  length (fst (SM.rt_st inp b)) = RIM.ID_SIZE /\ length (snd (SM.rt_st inp b)) = 72%nat.
Proof.
  intros inp b. induction b as [|b IH]; [split; reflexivity|].
  destruct IH as [IH1 IH2]. cbn [SM.rt_st]. cbv zeta.
  destruct (SM.rt_n inp (Z.of_nat b) =? 0); [split; assumption|].
  destruct ((Z.of_nat b =? 3) || (Z.of_nat b =? 4)); [split; [apply r6_rp_id_len; exact IH1 | exact IH2]|].
  destruct ((Z.of_nat b =? 5) || (Z.of_nat b =? 6)); [|split; assumption].
  cbn [fst snd]. split.
  - apply r6_fg_id_len. exact IH1.
  - apply r6_fg_st_len; [exact IH2 | apply SM.fr50_length].
Qed.

(* ---- memory: the core's view against raw memory ---- *)
Section R6Help.
Context {fx : CK11.FPState} {rc : CM05.RunCeil}.

(* A byte present and visible in W, off the ROM, whose view the call keeps, is the same raw byte afterwards. *)
Lemma r6_keep_mem : forall (W W2 : YA0n.world segs) (mem mem2 : word -> option byte) (a : Z),
  CK11.seg_rom segs (Z_to_bv 64 a) = None ->
  YG0n.apresent (YA0n.w_H W) mem a ->
  YG0n.aview segs (YA0n.w_H W2) mem2 a = YG0n.aview segs (YA0n.w_H W) mem a ->
  mem2 (Z_to_bv 64 a) = mem (Z_to_bv 64 a).
Proof.
  intros W W2 mem mem2 a Hrom (Hh & bb & Hbb) Heq.
  unfold YG0n.aview, YP09.mbyte, YK04.mrestrict in Heq.
  rewrite Hh, Hbb in Heq. cbn [option_map] in Heq.
  destruct (YA0n.w_H W2 (Z_to_bv 64 a)).
  - rewrite Hrom in Heq. discriminate Heq.
  - rewrite Hbb. destruct (mem2 (Z_to_bv 64 a)) as [b2|].
    + cbn [option_map] in Heq. injection Heq as Heq. f_equal. apply bv_eq. exact Heq.
    + rewrite Hrom in Heq. discriminate Heq.
Qed.

(* A present visible byte has a view. *)
Lemma r6_vis_some : forall (H : word -> bool) (mem : word -> option byte) (a : Z) (bb : byte),
  H (Z_to_bv 64 a) = false -> mem (Z_to_bv 64 a) = Some bb ->
  YG0n.aview segs H mem a = Some (bv_unsigned bb).
Proof.
  intros H mem a bb Hh Hm. unfold YG0n.aview, YP09.mbyte, YK04.mrestrict. rewrite Hh, Hm. reflexivity.
Qed.

End R6Help.

(* the spill word at A + off, when A is the spill base of s1 *)
Lemma r6_spill_at : forall (regs : bvmap 5 word) (m : word -> option byte) off v Af,
  ACtlCutP.spill regs m off v -> ACtlCut.rgv regs 9 Af -> 0 <= Af < 2 ^ 63 -> 0 <= off <= 512 ->
  ACtlCutP.q64 m (Af + off) v.
Proof.
  intros regs m off v Af (A1 & H9 & Hq) Hr HAf Hoff.
  unfold ACtlCut.rgv in *. rewrite H9 in Hr.
  assert (E : A1 mod 2 ^ 64 = Af mod 2 ^ 64).
  { apply (f_equal bv_unsigned) in Hr. rewrite !Z_to_bv_unsigned in Hr. exact Hr. }
  pose proof Hq as (Hq0 & Hq1 & _). rewrite LMem.length_le8 in Hq1.
  change (Z.of_nat 8) with 8 in Hq1.
  rewrite (Z.mod_small Af) in E by lia.
  assert (A1 = Af).
  { destruct (Z_lt_le_dec A1 0) as [Hn|Hn].
    - exfalso. pose proof (Z.mod_pos_bound A1 (2 ^ 64) ltac:(lia)) as Hmb.
      pose proof (Z.div_mod A1 (2 ^ 64) ltac:(lia)) as Hdm. lia.
    - rewrite Z.mod_small in E by lia. exact E. }
  subst A1. exact Hq.
Qed.

(* a spill at a map that keeps s1, at a memory whose spill word is unchanged (lib/Lib mrd) *)
Lemma r6_spill_keep : forall (regs regs' : bvmap 5 word) (m m' : word -> option byte) off v Af,
  ACtlCutP.spill regs m off v -> ACtlCut.rgv regs 9 Af -> 0 <= Af < 2 ^ 63 -> 0 <= off <= 512 ->
  CK11.getr regs' 9 = CK11.getr regs 9 ->
  (forall x, Af + off <= x < Af + off + 8 ->
     LMem.mrd Img0.rsegs m' (LMem.wa x) = LMem.mrd Img0.rsegs m (LMem.wa x)) ->
  ACtlCutP.spill regs' m' off v.
Proof.
  intros regs regs' m m' off v Af Hs Hr HAf Hoff E9 K.
  exists Af. split; [unfold ACtlCut.rgv in *; rewrite E9; exact Hr|].
  pose proof (r6_spill_at regs m off v Af Hs Hr HAf Hoff) as Hq.
  apply (KM.kitmem_bytes_at_mrd m m' (Af + off) _ Hq). rewrite LMem.length_le8. change (Z.of_nat 8) with 8.
  intros i Hi. apply K. lia.
Qed.

(* a byte's signed value, when nonnegative, is its unsigned value *)
Lemma r6_signed_nonneg : forall bb : byte, 0 <= bv_signed bb -> bv_signed bb = bv_unsigned bb.
Proof.
  intros bb H. pose proof (bv_unsigned_in_range _ bb) as R.
  unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in *.
  change (2 ^ Z.of_N 8) with 256 in *. change (256 / 2) with 128 in *.
  remember (bv_unsigned bb) as u eqn:Eu. clear Eu.
  Z.div_mod_to_equations. lia.
Qed.

(* the view against raw bytes: range_addressable and garr8 *)
Section R6Help2.
Context {fx : CK11.FPState} {rc : CM05.RunCeil}.

(* raw addressability + a visible shadow = the core's range_addressable over the view *)
Lemma r6_range_addr : forall (H : word -> bool) (m : word -> option byte) p n,
  ART.addressable m p n ->
  (forall i, 0 <= i < n -> H (Z_to_bv 64 (ART.shadow_addr (p + i))) = false) ->
  YG0v.range_addressable (YG0n.aview segs H m) YG0f.SHADOW_OFF p n.
Proof.
  intros H m p n (_ & _ & _ & HA) Hv x Hx.
  destruct (HA (x - p) ltac:(lia)) as (_ & bb & Hbb & Hok).
  pose proof (Hv (x - p) ltac:(lia)) as Hh.
  replace (p + (x - p)) with x in Hbb, Hok, Hh by lia.
  exists (bv_unsigned bb).
  assert (Esh : YG0v.shadow_of_addr YG0f.SHADOW_OFF x = ART.shadow_addr x).
  { unfold YG0v.shadow_of_addr, ART.shadow_addr, ART.ASAN_K, YG0f.SHADOW_OFF. lia. }
  rewrite Esh. split.
  - unfold YG0n.aview, YP09.mbyte, YK04.mrestrict. rewrite Hh.
    unfold LMem.mrd, LMem.wa in Hbb.
    destruct (m (Z_to_bv 64 (ART.shadow_addr x))) as [b0|].
    + injection Hbb as <-. reflexivity.
    + assert (Hr : CK11.seg_rom segs (Z_to_bv 64 (ART.shadow_addr x)) = Some bb) by exact Hbb.
      rewrite Hr. reflexivity.
  - unfold ART.shadow_ok in Hok. unfold YG0v.saddr_ok.
    pose proof (bv_unsigned_in_range _ bb) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R.
    destruct Hok as [Hk|(Hk1 & Hk2)].
    + left. rewrite <- (r6_signed_nonneg bb) by lia. exact Hk.
    + right. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Hm8.
      rewrite <- (r6_signed_nonneg bb) by lia. lia.
Qed.

(* garr8 of bytes whose (restricted) bytes are known one by one *)
Lemma r6_garr8_of_mbyte : forall (m : word -> option byte) a (bs : list byte),
  (forall j, (j < length bs)%nat -> YP09.mbyte segs m (a + Z.of_nat j) = nth_error bs j) ->
  YI00.garr8 segs m a (map (fun bb : byte => bv_unsigned bb) bs).
Proof.
  intros m a bs H j Hj. rewrite length_map in Hj.
  destruct (nth_error bs j) as [bj|] eqn:En; [|apply nth_error_None in En; lia].
  assert (Hn : nth j (map (fun bb : byte => bv_unsigned bb) bs) 0 = bv_unsigned bj)
    by (apply nth_error_nth; rewrite nth_error_map, En; reflexivity).
  pose proof (bv_unsigned_in_range _ bj) as Hr. unfold bv_modulus in Hr. change (2 ^ Z.of_N 8) with 256 in Hr.
  rewrite Hn. split; [|lia].
  intros k Hk. assert (k = 0%nat) as -> by lia. cbn [Z.of_nat]. rewrite Z.add_0_r, (H j Hj), En.
  rewrite <- (Z_to_bv_bv_unsigned _ bj) at 1. f_equal.
  unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO0f.le_byte.
  change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. change (2 ^ 8) with 256.
  rewrite !(Z.mod_small (bv_unsigned bj) 256) by lia. reflexivity.
Qed.

(* ---- image bytes the build_as spec reads (round_trip.box, the catalogue rows, the row names): checked by
   vm_compute against the image's segments, the bundle's owned-static list and errno word (AF0m's Tfib_owned_static
   / TFIB_ERRNO through TFIB_SYMS ts_owned / ts_errno; the record AF0m e56483f863b's list measured: no overlap) ---- *)
Definition r6_seg_ro_b (x : Z) : bool :=
  existsb (fun s => negb (seg_writable s) && (Z.of_N (seg_base s) <=? x) &&
                    (x <? Z.of_N (seg_base s) + Z.of_N (seg_size s))) segs.
Definition r6_owned_b (x : Z) : bool :=
  existsb (fun r => (fst r <=? x) && (x <? fst r + snd r)) AF0m.Tfib_owned_static.
Definition r6_rob (ro : bool) (lo : Z) (bs : list byte) : bool :=
  forallb (fun k =>
    (negb ro || r6_seg_ro_b (lo + Z.of_nat k)) && negb (r6_owned_b (lo + Z.of_nat k)) &&
    negb ((AF0m.TFIB_ERRNO <=? lo + Z.of_nat k) && (lo + Z.of_nat k <? AF0m.TFIB_ERRNO + 4)) &&
    match CK11.seg_rom segs (Z_to_bv 64 (lo + Z.of_nat k)), nth_error bs k with
    | Some b1, Some b2 => bv_eqb b1 b2
    | _, _ => false
    end) (seq 0 (length bs)).

Lemma r6_rob_sound : forall ro lo bs, r6_rob ro lo bs = true -> forall j, (j < length bs)%nat ->
  (ro = true -> exists s, In s segs /\ seg_writable s = false /\
     Z.of_N (seg_base s) <= lo + Z.of_nat j < Z.of_N (seg_base s) + Z.of_N (seg_size s)) /\
  ~ Exists (YG0n.in_zr (lo + Z.of_nat j)) AF0m.Tfib_owned_static /\
  ~ (AF0m.TFIB_ERRNO <= lo + Z.of_nat j < AF0m.TFIB_ERRNO + 4) /\
  CK11.seg_rom segs (Z_to_bv 64 (lo + Z.of_nat j)) = nth_error bs j.
Proof.
  intros ro lo bs H j Hj. unfold r6_rob in H. rewrite forallb_forall in H.
  specialize (H j ltac:(apply in_seq; lia)).
  rewrite !andb_true_iff in H. destruct H as [[[Hro Hown] Herr] Hrom].
  split; [|split; [|split]].
  - intros ->. cbn [negb orb] in Hro. unfold r6_seg_ro_b in Hro. apply existsb_exists in Hro.
    destruct Hro as (s & Hs & Hb). rewrite !andb_true_iff in Hb. destruct Hb as [[Hw H1] H2].
    apply negb_true_iff in Hw. apply Z.leb_le in H1. apply Z.ltb_lt in H2. exists s. auto.
  - intros Hex. apply Exists_exists in Hex. destruct Hex as (r & Hr & Hz). unfold YG0n.in_zr in Hz.
    apply negb_true_iff in Hown. unfold r6_owned_b in Hown.
    assert (Ht : existsb (fun r => (fst r <=? lo + Z.of_nat j) && (lo + Z.of_nat j <? fst r + snd r))
                   AF0m.Tfib_owned_static = true).
    { apply existsb_exists. exists r. split; [exact Hr|]. apply andb_true_iff.
      split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
    rewrite Ht in Hown. discriminate Hown.
  - intros He. apply negb_true_iff in Herr. apply andb_false_iff in Herr.
    destruct Herr as [E|E]; [apply Z.leb_gt in E | apply Z.ltb_ge in E]; lia.
  - destruct (CK11.seg_rom segs (Z_to_bv 64 (lo + Z.of_nat j))) as [b1|];
      destruct (nth_error bs j) as [b2|]; try discriminate Hrom.
    unfold bv_eqb in Hrom. apply Z.eqb_eq in Hrom. apply bv_eq in Hrom. subst b2. reflexivity.
Qed.

(* the bytes of a checked range, through the read-only view the journal carries (arodata_okS) *)
Lemma r6_garr8_ro : forall (B : YG0f.asyms) RLO RHI (H : word -> bool) (m : word -> option byte) ro lo bs,
  AF0m.CtrlTSyms B ->
  YE01.arodata_okS segs B RLO RHI (YG0n.aview segs H m) ->
  r6_rob ro lo bs = true ->
  (ro = false -> forall j, (j < length bs)%nat -> RLO <= lo + Z.of_nat j < RHI) ->
  YI00.garr8 segs (YK04.mrestrict H m) lo (map (fun bb : byte => bv_unsigned bb) bs).
Proof.
  intros B RLO RHI H m ro lo bs HTS HA Hc Hrl.
  apply r6_garr8_of_mbyte. intros j Hj.
  destruct (r6_rob_sound ro lo bs Hc j Hj) as (Hseg & Hown & Herr & Hrom).
  assert (Hin : (exists s, In s segs /\ seg_writable s = false /\
                   Z.of_N (seg_base s) <= lo + Z.of_nat j < Z.of_N (seg_base s) + Z.of_N (seg_size s)) \/
                (RLO <= lo + Z.of_nat j < RHI)).
  { destruct ro; [left; apply Hseg; reflexivity | right; apply Hrl; [reflexivity | exact Hj]]. }
  assert (Hown' : ~ Exists (YG0n.in_zr (lo + Z.of_nat j)) (YG0f.as_owned_static B))
    by (rewrite (AF0m.ts_owned B HTS); exact Hown).
  assert (Herr' : ~ (YG0f.as_errno B <= lo + Z.of_nat j < YG0f.as_errno B + 4))
    by (rewrite (AF0m.ts_errno B HTS); exact Herr).
  pose proof (HA (lo + Z.of_nat j) Hin Hown' Herr') as Hv.
  rewrite Hrom in Hv.
  destruct (nth_error bs j) as [bj|] eqn:En; [|apply nth_error_None in En; lia].
  unfold YG0n.aview in Hv.
  destruct (YP09.mbyte segs (YK04.mrestrict H m) (lo + Z.of_nat j)) as [b'|]; cbn [option_map] in Hv;
    [|discriminate Hv].
  injection Hv as Hv. f_equal. apply bv_eq. exact Hv.
Qed.

Lemma r6_box_chk : r6_rob true 0x21140 SM.box6 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma r6_cat_chk : forallb (fun i => r6_rob false (SM.CAT + SM.CAT_ROW * Z.of_nat i) (SM.rowb (Z.of_nat i)))
  (seq 0 11) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma r6_name_chk : forallb (fun i =>
    (RS.has (SM.rowb (Z.of_nat i)) =? 0) || (RS.rname (SM.rowb (Z.of_nat i)) =? 0) ||
    r6_rob true (RS.rname (SM.rowb (Z.of_nat i))) (SM.img_cstr (RS.rname (SM.rowb (Z.of_nat i))) 16))
  (seq 0 11) = true.
Proof. vm_compute. reflexivity. Qed.

End R6Help2.

(* FRAC (ACtlCutP.v:982-996) along a map that keeps its seven registers, at a memory whose bytes (lib/Lib mrd) are
   unchanged on FRAC's own regions: the LLVMF stack frame [spZ regs, c_sp), the frame header [fr, fr + 24), the
   frame trailer word [fr + 4088, fr + 4096) and the frame shadow [Sfr fr, Sfr fr + FRAME_SHADOW).  BY SHAPE, as
   KitMem.kitmem_frac_munch is written (each q64 / bytes_at conjunct by KitMem.kitmem_bytes_at_mrd), so the
   announced trailer conjunct q64 m (fr + 4088) .. (a Theorem Labs lane 05:3xZ) moves with no edit.  RE-ESTABLISHES FRAC
   at the new memory.  KitMem has only the munch forms (kitmem_frac_munch / kitmem_frac_keep): a cgif-form
   callee's post keeps the VIEW of the caller's classes (CtrlCallerJ.tcj_kept), not a munch. *)
Ltac r6_frac_conj K :=
  first
  [ assumption
  | lazymatch goal with
    | |- ACtlCutP.q64 ?m' ?a ?v =>
        match goal with Hq : ACtlCutP.q64 ?m a v |- _ =>
          apply (KM.kitmem_bytes_at_mrd m m' a _ Hq); rewrite LMem.length_le8;
          change (Z.of_nat 8) with 8; intros ? ?; apply K; lia end
    | |- LMem.bytes_at _ ?m' ?a ?bs =>
        match goal with Hb : LMem.bytes_at _ ?m a bs |- _ =>
          apply (KM.kitmem_bytes_at_mrd m m' a bs Hb); intros ? ?; apply K; lia end
    | |- exists sh, LMem.bytes_at _ ?m' ?lo sh /\ length sh = ?n =>
        match goal with Hx : exists sh, LMem.bytes_at _ ?m lo sh /\ length sh = n |- _ =>
          let sh := fresh "sh" in let Hb := fresh "Hb" in let Hl := fresh "Hl" in
          destruct Hx as (sh & Hb & Hl); exists sh; split; [|exact Hl];
          apply (KM.kitmem_bytes_at_mrd m m' lo sh Hb); rewrite Hl;
          rewrite Z2Nat.id by (unfold ACtlCutP.FRAME_SHADOW, ACtlCutP.FRAME_BYTES; lia);
          intros ? ?; apply K; lia end
    end ].

Lemma r6_frac_keep : forall (B : YG0f.asyms) cx fr sel (regs regs' : bvmap 5 word) (m m' : word -> option byte),
  ACtlCutP.FRAC B cx fr sel regs m ->
  CK11.getr regs' 2 = CK11.getr regs 2 -> CK11.getr regs' 3 = CK11.getr regs 3 ->
  CK11.getr regs' 4 = CK11.getr regs 4 -> CK11.getr regs' 8 = CK11.getr regs 8 ->
  CK11.getr regs' 9 = CK11.getr regs 9 -> CK11.getr regs' 19 = CK11.getr regs 19 ->
  CK11.getr regs' 26 = CK11.getr regs 26 ->
  (forall x, (YG0d.spZ regs <= x < ACtlCut.c_sp cx) \/ (fr <= x < fr + 24) \/ (fr + 4088 <= x < fr + 4096) \/
             (ACtlCutP.Sfr fr <= x < ACtlCutP.Sfr fr + ACtlCutP.FRAME_SHADOW) ->
     LMem.mrd Img0.rsegs m' (LMem.wa x) = LMem.mrd Img0.rsegs m (LMem.wa x)) ->
  ACtlCutP.FRAC B cx fr sel regs' m'.
Proof.
  intros B cx fr sel regs regs' m m' HF E2 E3 E4 E8 E9 E19 E26 K.
  pose proof (KM.kitmem_saved_len cx) as Hlen.
  unfold ACtlCutP.FRAC, ACtlCut.rgv, YG0d.spZ in *.
  destruct HF as (A & sp & HF). exists A, sp.
  rewrite E2, E3, E4, E8, E9, E19, E26.
  repeat match type of HF with _ /\ _ => let H1 := fresh "HF" in destruct HF as [H1 HF] end.
  repeat (match goal with |- _ /\ _ => split end); r6_frac_conj K.
Qed.

(* =========================================================================================================
   2. The stage. *)
Section GlueR6.

(* ACtl.v's Section shape (ACtl.v:170-194), restricted to what this stage uses. *)
Context {fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.FPState}
  {rc : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.RunCeil}
  {LS : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.lib_shape}.
Variable B : Reusable.YG0f.asyms.
Variable MT : Reusable.YC5d.ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.

(* ACtl.v's notation block (ACtl.v:213, :217-218, :233-234), verbatim. *)
Local Notation ix_cut := ACtlCut.ix_cut.
Local Notation CF POST X :=
  (ACtlCut.ctl_from (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation C_A815cc_at := (ACtlCutP.C_A815cc_at B).
Local Notation C_A815ec_at := (ACtlCutP.C_A815ec_at B).

(* ---------------------------------------------------------------------------------------------------------
   Section hypotheses. *)

(* ACtl.v:179 RELRO_IMG, ACtl.v:183 LAWS, ACtl.v:191 TFIB_SYMS: ACtl.v's own Section hypotheses, same text. *)
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> Reusable.YG0d.in_img segs a.
Hypothesis LAWS : Reusable.YG0d.AR_laws segs B.
Hypothesis TFIB_SYMS : A.AF0m.CtrlTSyms B.

(* RELRO_CAT: ACtl.v's own (ACtl.v:205, Batch3), same text.  The catalogue SlotModel.CAT [0x9e800, +11 * 296) is
   .data.rel.ro in the RW PT_LOAD, so no read-only segment covers it; its bytes are read through arodata_okS's RELRO
   arm. *)
Hypothesis RELRO_CAT : RLO <= A.Prog.SlotModel.CAT /\ A.Prog.SlotModel.CAT + A.Prog.SlotModel.CAT_N * A.Prog.SlotModel.CAT_ROW <= RHI.
Lemma r6_relro_cat : forall a, SM.CAT <= a < SM.CAT + 3256 -> RLO <= a < RHI.
Proof.
  intros a Ha. destruct RELRO_CAT as [Hlo Hhi].
  unfold A.Prog.SlotModel.CAT_N, A.Prog.SlotModel.CAT_ROW in Hhi. lia.
Qed.

(* The registered globals the callee specs take (ACtl.v:307, same text; CtrlRo.v: the composition fixes the list and
   discharges globs_marked).  NAME_GLOB: the name string of every catalogue row that has one lies in a registered
   global (the build_as spec's names premise, :112); added to ACtl.v's Section with this text by a Theorem Labs lane under another Theorem Labs lane. *)
Variable GLOBS_A : list (Z * Z).
Hypothesis NAME_GLOB : forall i, 0 <= i < 11 -> OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcSynth.has (A.Prog.SlotModel.rowb i) <> 0 -> OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcSynth.rname (A.Prog.SlotModel.rowb i) <> 0 -> exists q sz, In (q, sz) GLOBS_A /\ q <= OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcSynth.rname (A.Prog.SlotModel.rowb i) /\ OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcSynth.rname (A.Prog.SlotModel.rowb i) + Z.of_nat (length (A.Prog.SlotModel.img_cstr (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcSynth.rname (A.Prog.SlotModel.rowb i)) 16)) <= q + sz.

(* TBUILD: ACtl.v's own (ACtl.v:325, same text): a Theorem Labs lane's cgif-form spec of reac_ctrl_build_as, by name
   (C_reac_ctrl_build_as.v:72-119), at the function's address 0x848ac (= BASE + AF_reac_ctrl_build_as) and the walk's
   read-only span; the sink head explicit. *)
Hypothesis TBUILD : A.Prog.C_reac_ctrl_build_as.treac_ctrl_build_as_spec (SK := A.AE2k.tfib_sink_head) B GLOBS_A 0x848ac RLO RHI.

(* The shadow of a live heap block from AR (ProgWorld.v :849): ctl_block_shadow_of_AR_stmt is no longer open:
   a Theorem Labs lane's PROVED A.ProgWorldShadow.ctl_block_shadow_of_AR (on the glue base since 29ddfc3ea99), named locally. *)
Let BLOCK_SHADOW : PW.ctl_block_shadow_of_AR_stmt B := A.ProgWorldShadow.ctl_block_shadow_of_AR B.

(* ---------------------------------------------------------------------------------------------------------
   The stage. *)
Lemma glue_seg_R6 : forall POST (b : nat), CF POST (ix_cut C_A815ec_at [Z.of_nat b]) -> CF POST (ix_cut C_A815cc_at [Z.of_nat b]).
Proof.
  intros POST b HX cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
  (* G1: the entry cut at [Z.of_nat b] (ix_cut, ACtlCut.v:232-234; C_A815cc_at, ACtlCutP.v:1274-1294). *)
  destruct Hbody as [Hidx Hb]. subst idx.
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A815cc_at ACtlCutP.ixn ACtlCutP.ixz nth] in Hb.
  rewrite Nat2Z.id in Hb.
  destruct Hb as (HP & HFRAC & Hn26 & HRS & HOUTA & S128 & HPRO & S104 & S96 & Ha0 & R24 & S64 & S112 & R21 &
    S152 & S144 & HA2176 & S192 & HRW2688 & HRW2768 & S280 & S240 & HRW3040 & HRW3056 & HRXS).
  cbv beta iota zeta delta [ACtlCut.cut_kmax ACtlCut.ix_cut ACtlCutP.C_A815cc_at ACtlCutP.ixn nth] in Hk.
  rewrite Nat2Z.id in Hk.
  pose proof HRS as (Hb6 & HCUR & HOUR & R23 & HIDB & HFGB).
  pose proof HPRO as (P40 & P120 & P136 & P160 & P168 & P176 & P208 & P248 & Pad & Pin & Pg & P184 & P256 &
    P264 & P272 & P32).
  pose proof HRXS as (X48 & X56 & X88 & X80 & X72 & X8 & X0 & X200 & X216 & Xad).
  (* ---- G2: the entry's pre, the journal, the owned frame, FRAC ---- *)
  pose proof HB as ((HAFN & _ & _ & _ & Hinp & Hlen & _ & _ & _ & _ & Haro & _) & _).
  pose proof HAFN as (_ & _ & _ & Hgp0 & _).
  pose proof HJ as (HAR & _).
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstkp & _).
  pose proof (@CM05.alloc_ceiling_value rc) as ((Hac0 & Hac1) & _).
  destruct (KM.kitmem_own6 B cx [] ly3 S3 W3 mem3 md3 k fr LAWS HJ HF HL)
    as (Hin & Efr3 & Hfr4096 & Hfr32 & Hfceil & Hceilsp).
  destruct (YG0d.al_frames _ _ LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin) as (_ & Hfapp & Hfb & Hfsh).
  assert (Efs : YG00.fs_frame_bytes 6 = 4096) by reflexivity.
  rewrite Efr3, Efs in Hfapp, Hfb, Hfsh. rewrite Efs in Hfceil. change (4096 / 8) with 512 in Hfsh.
  unfold ACfn.LLVMF_STK in Hceilsp, Hstkp.
  pose proof HFRAC as (Af & sp & Hr2 & Hspm & Hspz & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & HAm & HAsp &
    HspA & HfrA & HA416 & Hsp4096 & HspEnd & _).
  unfold ACtlCutP.FRAME_BYTES in HfrA. unfold ART.APPMEM_END in HspEnd.
  assert (HAfb : 0 <= Af < 2 ^ 63) by lia.
  (* frame bytes are off the image (al_client_img), present and visible (al_frames); so is their shadow *)
  assert (NIF : forall x, fr <= x < fr + 4096 -> ~ YG0d.in_img segs x).
  { intros x Hx. refine (proj2 (YG0d.al_client_img _ _ LAWS ly3 S3 W3 mem3 md3 x HAR _)).
    right. left. exists 6, (ACtlCut.c_fpos cx). split; [exact Hin|]. rewrite Efr3, Efs. exact Hx. }
  assert (ESH : YG0f.shadow_addr fr = ACtlCutP.Sfr fr).
  { unfold YG0f.shadow_addr, YG0f.SHADOW_OFF, ACtlCutP.Sfr, ART.shadow_addr, ART.ASAN_K. lia. }
  assert (SHX : forall j, 0 <= j < 4096 -> ART.shadow_addr (fr + j) = ACtlCutP.Sfr fr + j / 8).
  { intros j Hj. unfold ACtlCutP.Sfr, ART.shadow_addr, ART.ASAN_K. revert Hfr32. Z.div_mod_to_equations. lia. }
  assert (FSV : forall i, 0 <= i < 512 -> YG0n.apresent (YA0n.w_H W3) mem3 (ACtlCutP.Sfr fr + i)).
  { intros i Hi. rewrite <- ESH. exact (proj1 (Hfsh i ltac:(lia))). }
  assert (FSV' : forall j, 0 <= j < 4096 -> YG0n.apresent (YA0n.w_H W3) mem3 (ART.shadow_addr (fr + j))).
  { intros j Hj. rewrite SHX by exact Hj. apply FSV. Z.div_mod_to_equations. lia. }
  (* the four spill words the stretch reads *)
  pose proof (r6_spill_at regs3 mem3 96 0x1234 Af S96 Hr9 HAfb ltac:(lia)) as C96.
  pose proof (r6_spill_at regs3 mem3 104 0x21140 Af S104 Hr9 HAfb ltac:(lia)) as C104.
  pose proof (r6_spill_at regs3 mem3 112 (SM.mrow (ACtlCut.c_in cx)) Af S112 Hr9 HAfb ltac:(lia)) as C112.
  pose proof (r6_spill_at regs3 mem3 168 (fr + 2624) Af P168 Hr9 HAfb ltac:(lia)) as C168.
  (* the stretch's footprint: the spill cells lie in the journal's stack window (KitMem.kitmem_rng_win) *)
  assert (HRW : forall lo len, sp <= lo -> lo + len <= ACtlCut.c_sp cx -> LEF.rng (PBr.RNG_W (YA0n.w_H W3)) lo len).
  { intros lo len H1 H2.
    apply (KM.kitmem_rng_win B ACfn.LLVMF_STK (ACtlCut.c_sp cx) [] _ _ _ _ _ _ _ _ _ _ _ _ lo len HJ);
      unfold ACfn.LLVMF_STK; lia. }
  (* ---- G3: the walk moved to the run's canonical start map ---- *)
  rewrite PBr.cfg_at_MS.
  change (ACtlCut.cut_pc (ix_cut C_A815cc_at [Z.of_nat b])) with 0x815cc.
  apply (YA0nR.SRr_xregs_eqv segs W3 (LR6.mkR_of regs3) regs3 CK11.fp_regs (Z_to_bv 64 0x815cc) CK11.fp_csr None
           mem3 (CK11.seg_rom segs) md3 (POST cx)); [| exact (LR6.xregs_eqv_sym _ _ (LR6.mkR_of_eqv regs3))].
  unfold LR6.mkR_of.
  (* ---- G4: the stretch 0x815cc -> 0x848ac (Seg/R6Fs.v r6_evt_pre_Fs), lifted ---- *)
  pose proof (SR6Fs.r6_evt_pre_Fs (PBr.RNG_W (YA0n.w_H W3))
    (reg_get regs3 1) (reg_get regs3 2) (reg_get regs3 3) (reg_get regs3 4) (reg_get regs3 5) (reg_get regs3 6)
    (reg_get regs3 7) (reg_get regs3 8) (reg_get regs3 9) (reg_get regs3 10) (reg_get regs3 11) (reg_get regs3 12)
    (reg_get regs3 13) (reg_get regs3 14) (reg_get regs3 15) (reg_get regs3 16) (reg_get regs3 17)
    (reg_get regs3 18) (reg_get regs3 19) (reg_get regs3 20) (reg_get regs3 21) (reg_get regs3 22)
    (reg_get regs3 23) (reg_get regs3 24) (reg_get regs3 25) (reg_get regs3 26) (reg_get regs3 27)
    (reg_get regs3 28) (reg_get regs3 29) (reg_get regs3 30) (reg_get regs3 31)
    CK11.fp_regs CK11.fp_csr mem3 Af (SM.mrow (ACtlCut.c_in cx)) (fr + 2624) Hr9 ltac:(lia) ltac:(lia)
    C96 C104 C112 C168
    (HRW (Af + 96) 8 ltac:(lia) ltac:(lia)) (HRW (Af + 104) 8 ltac:(lia) ltac:(lia))
    (HRW (Af + 112) 8 ltac:(lia) ltac:(lia)) (HRW (Af + 168) 8 ltac:(lia) ltac:(lia))) as HRUN.
  pose proof (PBr.fevt_of_evtF _ _ _ HRUN) as HFS.
  rewrite <- PBr.tfibsegs_rsegs in HFS.
  apply (YA0nR.SRr_fevt segs Kit.kit_wx W3 _ md3 (PBr.RNG_W (YA0n.w_H W3)) _ (POST cx) HFS).
  { exact (PBr.fp_avoids_RNG_W (YA0n.w_H W3)). }
  intros ms' md' HQ0 Hsbm.
  destruct HQ0 as (ra' & a1' & a3' & a4' & a5' & a6' & a7' & Ems & Era & Ea1 & Ea3 & Ea4 & Ea5 & Ea6 & Ea7).
  subst ms' ra' a1' a3' a4' a5' a6' a7'.
  match goal with |- context [LMS.MS ?RR _ (Z_to_bv 64 0x848ac) _ _ _ _] => set (R := RR) end.
  change (YA0n.SRr segs W3 (YG0d.cfg_at segs 0x848ac R mem3 md') (POST cx)).
  (* ---- G5: at reac_ctrl_build_as's entry ---- *)
  (* the journal across the model's materialization (no byte written) *)
  assert (HJ' : YCbq.ajournal (SK := AE2k.tfib_sink_head) segs B ACfn.LLVMF_STK (ACtlCut.c_sp cx) []
                  (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx)
                  (ACtlCut.own6 cx) ly3 S3 W3 mem3 md' k).
  { eapply (YCbq.ajournal_exec segs B LAWS Kit.kit_segs_low) with (Wr := fun _ : Z => False);
      [exact HJ | intros x _; reflexivity | apply CK1b.mem_grows_refl | intros x _; reflexivity
      | exact Hsbm | intros a Ha; destruct Ha]. }
  (* the read-only view at the call (KitMem.kitmem_arodataS_journal) *)
  assert (HARO3 : YE01.arodata_okS segs B RLO RHI (YG0n.aview segs (YA0n.w_H W3) mem3)).
  { exact (KM.kitmem_arodataS_journal B RLO RHI _ _ _ _ _ _ _ _ _ _ _ _ _ _ RELRO_IMG HJ' Haro). }
  (* the callee-entry map R *)
  assert (G1 : CK11.getr R 1 = Z_to_bv 64 0x815ec) by reflexivity.
  assert (G2 : CK11.getr R 2 = CK11.getr regs3 2) by reflexivity.
  assert (G3 : CK11.getr R 3 = CK11.getr regs3 3) by reflexivity.
  assert (G4 : CK11.getr R 4 = CK11.getr regs3 4) by reflexivity.
  assert (G10 : CK11.getr R 10 = CK11.getr regs3 10) by reflexivity.
  assert (G11 : CK11.getr R 11 = Z_to_bv 64 (SM.mrow (ACtlCut.c_in cx))) by reflexivity.
  assert (G12 : CK11.getr R 12 = CK11.getr regs3 23) by reflexivity.
  assert (G13 : CK11.getr R 13 = Z_to_bv 64 (fr + 2624)) by reflexivity.
  assert (G14 : CK11.getr R 14 = Z_to_bv 64 0x21140) by reflexivity.
  assert (G15 : CK11.getr R 15 = Z_to_bv 64 0x1234) by reflexivity.
  assert (G17 : CK11.getr R 17 = Z_to_bv 64 0) by reflexivity.
  assert (EspR : YG0d.spZ R = sp) by (unfold YG0d.spZ; rewrite G2; exact Hspz).
  assert (ECAT : VAL (CPT.A_OBJ BAS.A_CAT) = SM.CAT) by (vm_compute; reflexivity).
  assert (EBOX : VAL (CPT.A_OBJ BAS.A_BOX) = 0x21140) by (vm_compute; reflexivity).
  assert (Hist : 0 <= SM.istar (ACtlCut.c_in cx) < 11).
  { unfold SM.istar, SM.CAT_N. apply Z.mod_pos_bound. lia. }
  set (i := SM.istar (ACtlCut.c_in cx)) in *.
  assert (Ei : i = Z.of_nat (Z.to_nat i)) by lia.
  (* the spec's image premises *)
  assert (HBOXG : YI00.garr8 segs (YK04.mrestrict (YA0n.w_H W3) mem3) (VAL (CPT.A_OBJ BAS.A_BOX))
                    (map (fun bb : byte => bv_unsigned bb) SM.box6)).
  { rewrite EBOX. apply (r6_garr8_ro B RLO RHI _ _ true 0x21140 SM.box6 TFIB_SYMS HARO3 r6_box_chk).
    intros E; discriminate E. }
  assert (HCATG : YI00.garr8 segs (YK04.mrestrict (YA0n.w_H W3) mem3) (SM.mrow (ACtlCut.c_in cx))
                    (map (fun bb : byte => bv_unsigned bb) (SM.rowb i))).
  { pose proof r6_cat_chk as Hc. rewrite forallb_forall in Hc.
    specialize (Hc (Z.to_nat i) ltac:(apply in_seq; lia)). rewrite <- Ei in Hc.
    change (SM.mrow (ACtlCut.c_in cx)) with (SM.CAT + SM.CAT_ROW * i).
    apply (r6_garr8_ro B RLO RHI _ _ false _ _ TFIB_SYMS HARO3 Hc).
    intros _ j Hj. rewrite SR6.r6_row_len in Hj. apply r6_relro_cat. unfold SM.CAT_ROW in *. lia. }
  assert (HNAMES : (RL.ly_bb (PB.ba_row (Z.of_nat b)) = 5 \/ RL.ly_bb (PB.ba_row (Z.of_nat b)) = 6) ->
     RS.has (SM.rowb i) <> 0 -> RS.rname (SM.rowb i) <> 0 ->
     RB.name_ok (SM.rt_nb (ACtlCut.c_in cx)) /\
     YI00.garr8 segs (YK04.mrestrict (YA0n.w_H W3) mem3) (RS.rname (SM.rowb i))
       (map (fun bb : byte => bv_unsigned bb) (SM.rt_nb (ACtlCut.c_in cx))) /\
     (exists q sz, In (q, sz) GLOBS_A /\ q <= RS.rname (SM.rowb i) /\
        RS.rname (SM.rowb i) + Z.of_nat (length (SM.rt_nb (ACtlCut.c_in cx))) <= q + sz) /\
     (forall x, RS.rname (SM.rowb i) <= x < RS.rname (SM.rowb i) + Z.of_nat (length (SM.rt_nb (ACtlCut.c_in cx))) ->
        APB.in_roP segs RLO RHI x /\ ~ Exists (YG0n.in_zr x) (YG0f.as_owned_static B) /\
        ~ (YG0f.as_errno B <= x < YG0f.as_errno B + 4))).
  { intros _ Hhas Hrn.
    pose proof r6_name_chk as Hc. rewrite forallb_forall in Hc.
    specialize (Hc (Z.to_nat i) ltac:(apply in_seq; lia)). rewrite <- Ei in Hc.
    rewrite (proj2 (Z.eqb_neq _ _) Hhas), (proj2 (Z.eqb_neq _ _) Hrn) in Hc. cbn [orb] in Hc.
    change (SM.rt_nb (ACtlCut.c_in cx)) with (SM.img_cstr (RS.rname (SM.rowb i)) 16).
    split; [exact (proj1 (SR6.r6_name_facts i Hist Hhas Hrn))|].
    split; [apply (r6_garr8_ro B RLO RHI _ _ true _ _ TFIB_SYMS HARO3 Hc); intros E; discriminate E|].
    split; [exact (NAME_GLOB i Hist Hhas Hrn)|].
    intros x Hx.
    destruct (r6_rob_sound true _ _ Hc (Z.to_nat (x - RS.rname (SM.rowb i))) ltac:(lia))
      as (Hseg & Hown & Herr & _).
    rewrite Z2Nat.id in Hseg, Hown, Herr by lia.
    replace (RS.rname (SM.rowb i) + (x - RS.rname (SM.rowb i))) with x in Hseg, Hown, Herr by lia.
    split; [left; exact (Hseg eq_refl)|].
    split; [rewrite (AF0m.ts_owned B TFIB_SYMS); exact Hown | rewrite (AF0m.ts_errno B TFIB_SYMS); exact Herr]. }
  (* the frame facts the spec reads *)
  assert (MBF : forall x, fr <= x < fr + 4096 ->
            YP09.mbyte segs (YK04.mrestrict (YA0n.w_H W3) mem3) x = LMem.mrd segs mem3 (Z_to_bv 64 x)).
  { intros x Hx. destruct (Hfb x Hx) as ((Hh & b0 & Hb0) & _).
    unfold YP09.mbyte, YK04.mrestrict, LMem.mrd. rewrite Hh, Hb0. reflexivity. }
  assert (HOURG : YI00.garr8 segs (YK04.mrestrict (YA0n.w_H W3) mem3) (fr + 2624)
                    (map (fun bb : byte => bv_unsigned bb) (SM.OUR (ACtlCut.c_in cx)))).
  { apply r6_garr8_of_mbyte. intros j Hj. rewrite SM.OUR_length in Hj.
    rewrite MBF by lia. destruct HOUR as (_ & _ & HO). exact (HO j ltac:(rewrite SM.OUR_length; exact Hj)). }
  (* reac_ctrl_build_as's address: 0x848ac, TBUILD's *)
  eapply YA0n.SRr_bind.
  { refine (TBUILD ACfn.LLVMF_STK (ACtlCut.c_sp cx) [] (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx)
      (ACtlCut.c_mem cx) (ACtlCut.c_md cx) (ACtlCut.own6 cx) ly3 S3 W3 mem3 md' k R
      (fr + 544) (SM.mrow (ACtlCut.c_in cx)) (fr + 2624) 0x1234 (Z.of_nat b) 0 i
      (SM.rowb i) (SM.rt_nb (ACtlCut.c_in cx)) (SM.OUR (ACtlCut.c_in cx)) SM.box6
      HJ' HARO3
      ltac:(rewrite G1; first [reflexivity | (unfold YK0s.ret_ok; apply bv_eq; vm_compute; reflexivity)])
      ltac:(unfold YG0d.raZ; rewrite G1, LMS.unsigned_lit by lia; lia)
      ltac:(rewrite G3, Hr3; exact Hgp0)
      ltac:(rewrite G4; exact Hr4)
      ltac:(rewrite G10; exact Ha0)
      ltac:(lia)
      G11
      ltac:(rewrite ECAT; unfold SM.mrow, BAS.CAT_BYTES, SM.CAT_ROW; reflexivity)
      Hist
      ltac:(rewrite G12; exact R23)
      ltac:(lia)
      G13
      ltac:(rewrite G14, EBOX; reflexivity)
      G15
      ltac:(lia)
      G17
      ltac:(lia)
      ltac:(rewrite EspR; exact Hspm)
      ltac:(rewrite EspR; unfold ACfn.LLVMF_STK, BAS.TBUILD_STK; lia)
      ltac:(rewrite EspR; lia)
      ltac:(rewrite HF; reflexivity)
      ltac:(rewrite HF; reflexivity)
      ltac:(lia)
      ltac:(revert Hfr32; Z.div_mod_to_equations; lia)
      ltac:(lia)
      ltac:(unfold YG0d.amem_range, YG0f.kLowMemEnd, YG0f.kHighMemBeg, YG0f.kHighMemEnd;
            unfold YG0f.in_app, YG0f.kLowShadowBeg, YG0f.kHighMemBeg, YG0f.ASAN_CEIL in Hfapp; lia)
      ltac:(intros x Hx; apply NIF; lia)
      _ _ _ _ _
      (SM.OUR_length (ACtlCut.c_in cx)) HOURG
      _
      ltac:(intros x Hx; apply NIF; lia)
      ltac:(left; lia)
      ltac:(left; rewrite EspR; unfold BAS.TBUILD_STK; lia)
      ltac:(revert Hfr32; Z.div_mod_to_equations; lia)
      eq_refl HBOXG HCATG (SR6.r6_row_len i) HNAMES).
  - (* twr_ok: the 1492 bytes of out[] are owned-frame bytes, present, not owned, below the stack *)
    intros a Ha. split; [|split; [|split]].
    + right. right. right. exists 6, (ACtlCut.c_fpos cx). split; [left; reflexivity|].
      left. unfold YG0n.in_zr. cbn [fst snd]. rewrite Efr3, Efs. lia.
    + exact (proj1 (Hfb a ltac:(lia))).
    + exact (proj2 (Hfb a ltac:(lia))).
    + rewrite EspR. unfold YG0d.ESTACK. lia.
  - (* afobj *)
    split; [|split].
    + exists 6, (ACtlCut.c_fpos cx). split; [exact Hin|]. split; [lia|].
      rewrite Efr3, Efs. split; [revert Hfr32; Z.div_mod_to_equations; lia | lia].
    + revert Hfr32; Z.div_mod_to_equations; lia.
    + apply r6_range_addr; [exact HOUTA|]. intros j Hj.
      replace (fr + 544 + j) with (fr + (544 + j)) by lia. exact (proj1 (FSV' (544 + j) ltac:(lia))).
  - (* out[] in the class-6 frame *)
    exists 6, (ACtlCut.c_fpos cx). rewrite Efr3, Efs. split; [exact Hin | lia].
  - (* our[] in the class-6 frame *)
    exists 6, (ACtlCut.c_fpos cx). rewrite Efr3, Efs. split; [exact Hin | lia].
  - (* tfr_hull (C_ctrl_lay_block.v 0e94852de76: In (cid, pos) (frames S) /\ 2 <= cid /\ the 64-byte hull): the owned
       class-6 frame, cid = 6 (Hin from kitmem_own6 at the own6 cut) *)
    exists 6, (ACtlCut.c_fpos cx). rewrite Efr3, Efs. split; [exact Hin|]. split; [lia|].
    split; Z.div_mod_to_equations; lia.
  - (* tsrc_ok of our[] *)
    split; [|split; [|split; [|split; [|split]]]].
    + intros a Ha. split.
      * destruct (Hfb a ltac:(lia)) as ((Hh & b0 & Hb0) & _). intros Hn.
        pose proof (eq_trans (eq_sym (r6_vis_some _ _ a b0 Hh Hb0)) Hn) as Hc. discriminate Hc.
      * rewrite EspR. unfold YG0d.ESTACK. lia.
    + apply r6_range_addr; [exact Pad|]. intros j Hj.
      replace (fr + 2624 + j) with (fr + (2624 + j)) by lia. exact (proj1 (FSV' (2624 + j) ltac:(lia))).
    + intros s Hs.
      assert (Hj : 0 <= s - ACtlCutP.Sfr fr < 512).
      { rewrite <- ESH. unfold YG0f.shadow_addr, YG0f.SHADOW_OFF in *. revert Hs Hfr32. Z.div_mod_to_equations. lia. }
      destruct (FSV (s - ACtlCutP.Sfr fr) Hj) as (Hh & b0 & Hb0).
      replace (ACtlCutP.Sfr fr + (s - ACtlCutP.Sfr fr)) with s in Hh, Hb0 by lia.
      intros Hn. pose proof (eq_trans (eq_sym (r6_vis_some _ _ s b0 Hh Hb0)) Hn) as Hc. discriminate Hc.
    + unfold YG0d.amem_range, YG0f.kLowMemEnd, YG0f.kHighMemBeg, YG0f.kHighMemEnd.
      unfold YG0f.in_app, YG0f.kLowShadowBeg, YG0f.kHighMemBeg, YG0f.ASAN_CEIL in Hfapp. lia.
    + lia.
    + lia.
  }
  - (* ---- G6: TBUILD's post, the return to 0x815ec = the exit cut ---- *)
    intros W2 c2 Hle HPOST.
    unfold BAS.treac_ctrl_build_as_post, EMA.tctrl_emit_as_post in HPOST. cbv zeta in HPOST.
    destruct HPOST as (ly2 & S2 & regs2 & mem2 & md2 & Ec2 & HJ2 & Hpres & Hfr2 & Hbl2 & Ha02 & Hout & Hkept).
    subst c2.
    (* the emitter's E / len / R / frame are build_as's: the turn's rt_E / rt_n / rt_F (SlotModel) *)
    assert (EE : RE.em_E (EMA.EM_L (PB.ba_row (Z.of_nat b))) (EMA.EM_G (PB.ba_row (Z.of_nat b)))
                   (RP.bm_uw (SM.mrow (ACtlCut.c_in cx)) (firstn 8 (skipn 16 (SM.rowb i))))
                   (RE.em_hid (SM.rowb i)) = SM.rt_E (ACtlCut.c_in cx) (Z.of_nat b))
      by (rewrite r6_E_eq by exact Hb6; reflexivity).
    assert (EL : RE.em_len (EMA.EM_L (PB.ba_row (Z.of_nat b)))
                   (RP.bm_uw (SM.mrow (ACtlCut.c_in cx)) (firstn 8 (skipn 16 (SM.rowb i)))) =
                 52 + 36 * SM.rt_uw (ACtlCut.c_in cx))
      by (rewrite r6_len_eq by exact Hb6; reflexivity).
    rewrite EE, EL in Ha02, Hout, Hkept. rewrite EE in HJ2.
    assert (ER : (if SM.rt_E (ACtlCut.c_in cx) (Z.of_nat b) then 52 + 36 * SM.rt_uw (ACtlCut.c_in cx) else 0) =
                 ACtlCutP.rnb cx b) by reflexivity.
    rewrite ER in Ha02, Hkept.
    assert (EV0 : (if SM.rt_E (ACtlCut.c_in cx) (Z.of_nat b) then EMA.EV_EMIT else 0) = 0)
      by (destruct (SM.rt_E _ _); reflexivity).
    rewrite EV0, Z.add_0_r in HJ2.
    pose proof (r6_rtn_range (ACtlCut.c_in cx) (Z.of_nat b)) as Hrn.
    change (SM.rt_n (ACtlCut.c_in cx) (Z.of_nat b)) with (ACtlCutP.rnb cx b) in Hrn.
    (* what the call keeps *)
    destruct Hkept as (KHI & KBL & _ & KFR & _ & _).
    assert (ETS : EMA.TEMIT_STK = 4640) by (vm_compute; reflexivity).
    assert (KS : forall x, sp <= x < ACtlCut.c_sp cx ->
               LMem.mrd Img0.rsegs mem2 (LMem.wa x) = LMem.mrd Img0.rsegs mem3 (LMem.wa x)).
    { intros x Hx. unfold LMem.mrd, LMem.wa. rewrite (r6_keep_mem W3 W2 mem3 mem2 x); [reflexivity | | |].
      - apply PWC.seg_rom_none_high. lia.
      - apply Hstkp. lia.
      - apply KHI; [lia | rewrite EspR, ETS; lia | cbv beta; lia]. }
    assert (KF : forall x, fr <= x < fr + 4096 -> ~ (fr + 544 <= x < fr + 544 + ACtlCutP.rnb cx b) ->
               mem2 (Z_to_bv 64 x) = mem3 (Z_to_bv 64 x)).
    { intros x Hx Hnx. apply (r6_keep_mem W3 W2 mem3 mem2 x).
      - apply YCbq.seg_rom_none; [lia | exact (NIF x Hx)].
      - exact (proj1 (Hfb x Hx)).
      - apply (KFR 6 (ACtlCut.c_fpos cx) x Hin); [|exact Hnx].
        left. unfold YG0n.in_zr, YCbq.frame_rng. cbn [fst snd]. rewrite Efr3, Efs. lia. }
    assert (KFm : forall x, fr <= x < fr + 4096 -> ~ (fr + 544 <= x < fr + 544 + ACtlCutP.rnb cx b) ->
               LMem.mrd Img0.rsegs mem2 (LMem.wa x) = LMem.mrd Img0.rsegs mem3 (LMem.wa x)).
    { intros x Hx Hnx. unfold LMem.mrd, LMem.wa. rewrite (KF x Hx Hnx). reflexivity. }
    assert (KH : forall x, ACtlCutP.Sfr fr <= x < ACtlCutP.Sfr fr + 512 ->
               LMem.mrd Img0.rsegs mem2 (LMem.wa x) = LMem.mrd Img0.rsegs mem3 (LMem.wa x)).
    { intros x Hx. unfold LMem.mrd, LMem.wa.
      rewrite (r6_keep_mem W3 W2 mem3 mem2 x); [reflexivity | | |].
      - apply PWC.seg_rom_none_high. unfold ACtlCutP.Sfr, ART.shadow_addr, ART.ASAN_K in Hx.
        revert Hx Hfr4096. Z.div_mod_to_equations. lia.
      - replace x with (ACtlCutP.Sfr fr + (x - ACtlCutP.Sfr fr)) by lia. apply FSV. lia.
      - apply (KFR 6 (ACtlCut.c_fpos cx) x Hin).
        + right. unfold YG0n.in_zr. cbn [fst snd]. rewrite Efr3, Efs, ESH. change (4096 / 8) with 512. lia.
        + cbv beta. unfold ACtlCutP.Sfr, ART.shadow_addr, ART.ASAN_K in Hx.
          unfold YG0f.in_app, YG0f.kLowShadowBeg, YG0f.kHighMemBeg, YG0f.ASAN_CEIL in Hfapp.
          revert Hx Hfapp. Z.div_mod_to_equations. lia. }
    (* registers kept by the call (aregs_preserved) *)
    assert (P2 : CK11.getr regs2 2 = CK11.getr regs3 2) by exact (Hpres 2 ltac:(unfold YG0d.acallee_saved; lia)).
    assert (P3 : CK11.getr regs2 3 = CK11.getr regs3 3) by exact (Hpres 3 ltac:(unfold YG0d.acallee_saved; lia)).
    assert (P4 : CK11.getr regs2 4 = CK11.getr regs3 4) by exact (Hpres 4 ltac:(unfold YG0d.acallee_saved; lia)).
    assert (P8 : CK11.getr regs2 8 = CK11.getr regs3 8) by exact (Hpres 8 ltac:(unfold YG0d.acallee_saved; lia)).
    assert (P9 : CK11.getr regs2 9 = CK11.getr regs3 9) by exact (Hpres 9 ltac:(unfold YG0d.acallee_saved; lia)).
    assert (P19 : CK11.getr regs2 19 = CK11.getr regs3 19) by exact (Hpres 19 ltac:(unfold YG0d.acallee_saved; lia)).
    assert (P21 : CK11.getr regs2 21 = CK11.getr regs3 21) by exact (Hpres 21 ltac:(unfold YG0d.acallee_saved; lia)).
    assert (P22 : CK11.getr regs2 22 = CK11.getr regs3 22) by exact (Hpres 22 ltac:(unfold YG0d.acallee_saved; lia)).
    assert (P23 : CK11.getr regs2 23 = CK11.getr regs3 23) by exact (Hpres 23 ltac:(unfold YG0d.acallee_saved; lia)).
    assert (P24 : CK11.getr regs2 24 = CK11.getr regs3 24) by exact (Hpres 24 ltac:(unfold YG0d.acallee_saved; lia)).
    assert (P25 : CK11.getr regs2 25 = CK11.getr regs3 25) by exact (Hpres 25 ltac:(unfold YG0d.acallee_saved; lia)).
    assert (P26 : CK11.getr regs2 26 = CK11.getr regs3 26) by exact (Hpres 26 ltac:(unfold YG0d.acallee_saved; lia)).
    (* a spill moves through s1 and the stack clause *)
    assert (SPK : forall off v, 0 <= off <= 304 -> ACtlCutP.spill regs3 mem3 off v -> ACtlCutP.spill regs2 mem2 off v).
    { intros off v Hoff Hs. apply (r6_spill_keep regs3 regs2 mem3 mem2 off v Af Hs Hr9 HAfb ltac:(lia) P9).
      intros x Hx. apply KS. lia. }
    (* frame bytes away from out[] *)
    assert (BYF : forall a bs, fr + 2048 <= a -> a + Z.of_nat (length bs) <= fr + 4096 ->
               LMem.bytes_at segs mem3 a bs -> LMem.bytes_at segs mem2 a bs).
    { intros a bs H1 H2 Hb. apply (KM.kitmem_bytes_at_mrd mem3 mem2 a bs Hb). intros j Hj. apply KFm; lia. }
    assert (ADF : forall p n, fr <= p -> p + n <= fr + 4096 -> ART.addressable mem3 p n -> ART.addressable mem2 p n).
    { intros p n H1 H2 Ha. apply (KM.kitmem_addressable_mrd mem3 mem2 p n Ha). intros j Hj.
      replace (p + j) with (fr + (p - fr + j)) by lia. rewrite SHX by lia. apply KH.
      Z.div_mod_to_equations. lia. }
    assert (RWF : forall a (n : nat) bs, fr + 2048 <= a -> a + Z.of_nat n <= fr + 4096 ->
               LST.rw_cells segs mem3 a [LCE.CB n bs] -> LST.rw_cells segs mem2 a [LCE.CB n bs]).
    { intros a n bs H1 H2 Hrw. apply (KM.kitmem_rw_cells_mrd mem3 mem2 a _ Hrw).
      cbn [LCE.cells_size LCE.csize]. try rewrite Nat.add_0_r. intros j Hj. split.
      - apply KFm; lia.
      - unfold LMem.wa. rewrite (KF (a + j)) by lia. destruct (Hfb (a + j) ltac:(lia)) as ((_ & b0 & Hb0) & _).
        rewrite Hb0. discriminate. }
    (* the exit cut, at the return configuration *)
    change (YA0n.SRr segs W2 (YG0d.cfg_at segs (ACtlCut.cut_pc (ix_cut C_A815ec_at [Z.of_nat b])) regs2 mem2 md2)
              (POST cx)).
    apply (HX cx [Z.of_nat b] fr k ly2 S2 W2 regs2 mem2 md2 HB).
    + (* journal *) exact HJ2.
    + (* frames *) rewrite Hfr2. exact HF.
    + (* frame law *) exact HL.
    + (* event bound: k <= 2b, the call counts no event (EV_EMIT = 0) *)
      cbv beta iota zeta delta [ACtlCut.cut_kmax ACtlCut.ix_cut ACtlCutP.C_A815ec_at ACtlCutP.ixn nth].
      rewrite Nat2Z.id. exact Hk.
    + (* the exit body, C_A815ec_at (ACtlCutP.v:1298-1321) *)
      cbv beta iota zeta delta [ACtlCut.cut_body ACtlCut.ix_cut ACtlCutP.C_A815ec_at ACtlCutP.ixn ACtlCutP.ixz nth].
      rewrite Nat2Z.id.
      split; [reflexivity|].
      split; [rewrite Hbl2; exact HP|].
      split.
      { apply (r6_frac_keep B cx fr fr regs3 regs2 mem3 mem2 HFRAC P2 P3 P4 P8 P9 P19 P26).
        intros x Hx. change ACtlCutP.FRAME_SHADOW with 392 in Hx.
        destruct Hx as [Hx | [Hx | [Hx | Hx]]].
        - apply KS. lia.
        - apply KFm; lia.
        - apply KFm; lia.
        - apply KH. lia. }
      exists Af.
      split; [exact Hn26|]. split; [exact Hb6|].
      split; [unfold ACtlK.ANMAX; lia|].
      split; [unfold ACtlK.a_size; lia|].
      split; [lia|].
      split; [unfold ACtlCut.rgv in *; rewrite P9; exact Hr9|].
      split; [unfold ACtlCut.rgv in *; rewrite P24; exact R24|].
      split; [exact Ha02|].
      split; [apply (KM.kitmem_bytes_at_mrd mem3 mem2 (Af + 64) _ (r6_spill_at regs3 mem3 64 _ Af S64 Hr9 HAfb ltac:(lia)));
              rewrite LMem.length_le8; change (Z.of_nat 8) with 8; intros j Hj; apply KS; lia|].
      split; [exact (SPK 128 _ ltac:(lia) S128)|].
      assert (LRID : Z.of_nat (length (SM.RID (ACtlCut.c_in cx) b)) = 38)
        by (unfold SM.RID; rewrite (proj1 (r6_rst_len (ACtlCut.c_in cx) b)); reflexivity).
      assert (LRFG : Z.of_nat (length (SM.RFG (ACtlCut.c_in cx) b)) = 72)
        by (unfold SM.RFG; rewrite (proj2 (r6_rst_len (ACtlCut.c_in cx) b)); reflexivity).
      split; [apply BYF; [lia | rewrite LRID; lia | exact HIDB]|].
      split; [apply BYF; [lia | rewrite LRFG; lia | exact HFGB]|].
      split.
      { (* the emitted frame: rnb <> 0 -> out[] holds rt_F *)
        intros Hnz.
        assert (HE : SM.rt_E (ACtlCut.c_in cx) (Z.of_nat b) = true).
        { unfold ACtlCutP.rnb, SM.rt_n in Hnz. destruct (SM.rt_E _ _); [reflexivity | congruence]. }
        specialize (Hout HE).
        assert (EF : RE.em_fr (SM.OUR (ACtlCut.c_in cx)) SM.box6 (0x1234 mod 65536) (Z_to_bv 8 0xcd) (Z_to_bv 8 0xea)
                       (RF.fin (EMA.EM_C (PB.ba_row (Z.of_nat b))) 0 0
                          (RL.ly_Z (SM.mrow (ACtlCut.c_in cx)) (SM.rowb i) (SM.rt_nb (ACtlCut.c_in cx))
                             (RL.ly_bb (PB.ba_row (Z.of_nat b)))))
                       (52 + 36 * SM.rt_uw (ACtlCut.c_in cx)) = SM.rt_F (ACtlCut.c_in cx) (Z.of_nat b)).
        { unfold SM.rt_F, SM.rt_X, SM.rt_n. rewrite HE, r6_blk_eq by exact Hb6. reflexivity. }
        rewrite EF in Hout.
        assert (HlF : Z.of_nat (length (SM.rt_F (ACtlCut.c_in cx) (Z.of_nat b))) = ACtlCutP.rnb cx b).
        { unfold SM.rt_F. apply SR6.r6_emfr_len; [apply SM.OUR_length | reflexivity | | ].
          - apply SR6.r6_baX_len. apply SR6.r6_row_len.
          - pose proof (SR6.r6_rtn (ACtlCut.c_in cx) (Z.of_nat b) Hnz) as Hr6.
            change (SM.rt_n (ACtlCut.c_in cx) (Z.of_nat b)) with (ACtlCutP.rnb cx b) in Hr6 |- *. lia. }
        destruct (PW.ctl_out_bytes W2 mem2 (fr + 544) (SM.rt_F (ACtlCut.c_in cx) (Z.of_nat b)) ltac:(lia) ltac:(lia)
                    ltac:(intros j Hj; apply NIF; lia) Hout)
          as (Hbo & _).
        exact Hbo. }
      split; [unfold ACtlCut.rgv in *; rewrite P23; exact R23|].
      split; [apply BYF; [lia | rewrite SM.OUR_length; change (Z.of_nat 6) with 6; lia | exact HOUR]|].
      split; [apply ADF; [lia | lia | exact HOUTA]|].
      split; [destruct HCUR as (Hc7 & Hc22 & Hc25); unfold ACtlCutP.CUR, ACtlCut.rgv in *; rewrite P22, P25;
              split; [exact Hc7 | split; [exact Hc22 | exact Hc25]]|].
      split; [exact (SPK 112 _ ltac:(lia) S112)|].
      split.
      { (* PRO *) unfold ACtlCutP.PRO.
        split; [exact (SPK 40 _ ltac:(lia) P40)|]. split; [exact (SPK 120 _ ltac:(lia) P120)|].
        split; [exact (SPK 136 _ ltac:(lia) P136)|]. split; [exact (SPK 160 _ ltac:(lia) P160)|].
        split; [exact (SPK 168 _ ltac:(lia) P168)|]. split; [exact (SPK 176 _ ltac:(lia) P176)|].
        split; [exact (SPK 208 _ ltac:(lia) P208)|]. split; [exact (SPK 248 _ ltac:(lia) P248)|].
        split; [apply ADF; [lia | lia | exact Pad]|].
        split.
        { (* the input block's bytes: a live block of the call's heap, kept (tcj_kept's block clause) *)
          apply (KM.kitmem_bytes_at_mrd mem3 mem2 _ _ Pin). intros j Hj.
          destruct Hinp as [(Hn0 & _) | (Hnpos & Hinb)].
          { rewrite <- Hlen in Hj. lia. }
          assert (Hin3 : In (ACtlCut.c_p cx, ACtlCut.c_n cx) (YG0d.ablocks B ly3 S3)).
          { apply (Permutation_in _ (Permutation_sym HP)). exact Hinb. }
          destruct (YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 _ _ HAR Hin3) as (_ & _ & _ & _ & Hpres3 & _).
          pose proof (YCbq.sep_block_frame segs B LAWS ly3 S3 W3 mem3 md3 _ _ 6 (ACtlCut.c_fpos cx) HAR Hin3 Hin)
            as Hdis.
          assert (Ereq : YG00.req_size (ACtlCut.c_n cx) = ACtlCut.c_n cx).
          { unfold YG00.req_size. destruct (Z.eqb_spec (ACtlCut.c_n cx) 0); lia. }
          unfold YG0f.zdisjoint in Hdis. cbn [fst snd] in Hdis. rewrite Efr3, Efs, Ereq in Hdis.
          rewrite <- Hlen in Hj.
          unfold LMem.mrd, LMem.wa.
          rewrite (r6_keep_mem W3 W2 mem3 mem2 (ACtlCut.c_p cx + j)); [reflexivity | | |].
          - apply YCbq.seg_rom_none; [pose proof Pin as (Hp0 & Hp1 & _); rewrite <- Hlen in Hp1; lia|].
            refine (proj2 (YG0d.al_client_img _ _ LAWS ly3 S3 W3 mem3 md3 _ HAR _)).
            left. exists (ACtlCut.c_p cx), (ACtlCut.c_n cx). split; [exact Hin3 | rewrite Ereq; lia].
          - exact (proj1 (Hpres3 (ACtlCut.c_p cx + j) ltac:(rewrite Ereq; lia))).
          - apply (KBL (ACtlCut.c_p cx) (ACtlCut.c_n cx) j Hin3); [rewrite Ereq; lia | cbv beta; lia]. }
        split.
        { (* the input block's shadow: from the post's AR (BLOCK_SHADOW) *)
          intros Hnpos. destruct Hinp as [(Hn0 & _) | (_ & Hinb)]; [lia|].
          pose proof HJ2 as (HAR2 & _).
          assert (Hin2 : In (ACtlCut.c_p cx, ACtlCut.c_n cx) (YG0d.ablocks B ly2 S2)).
          { rewrite Hbl2. apply (Permutation_in _ (Permutation_sym HP)). exact Hinb. }
          apply (BLOCK_SHADOW LAWS ly2 S2 W2 mem2 md2 _ _ _ _ HAR2 Hin2); [lia | lia |].
          unfold YG00.req_size. destruct (Z.eqb_spec (ACtlCut.c_n cx) 0); lia. }
        split; [exact (SPK 184 _ ltac:(lia) P184)|]. split; [exact (SPK 256 _ ltac:(lia) P256)|].
        split; [exact (SPK 264 _ ltac:(lia) P264)|]. split; [exact (SPK 272 _ ltac:(lia) P272)|].
        exact (SPK 32 _ ltac:(lia) P32). }
      split; [exact (SPK 104 _ ltac:(lia) S104)|].
      split; [exact (SPK 96 _ ltac:(lia) S96)|].
      split; [exact (SPK 144 _ ltac:(lia) S144)|].
      split; [exact (SPK 192 _ ltac:(lia) S192)|].
      split; [destruct HRW2688 as (idb & Hrw); exists idb;
              apply (RWF _ 38%nat idb); [lia | change (Z.of_nat 38) with 38; lia | exact Hrw]|].
      split; [destruct HRW2768 as (junk & Hrw); exists junk;
              apply (RWF _ 72%nat junk); [lia | change (Z.of_nat 72) with 72; lia | exact Hrw]|].
      split; [exact (SPK 280 _ ltac:(lia) S280)|].
      split; [exact (SPK 240 _ ltac:(lia) S240)|].
      split; [destruct HRW3040 as (jy & Hrw); exists jy;
              apply (RWF _ 1%nat jy); [lia | change (Z.of_nat 1) with 1; lia | exact Hrw]|].
      split; [destruct HRW3056 as (junk & Hrw); exists junk;
              apply (RWF _ 32%nat junk); [lia | change (Z.of_nat 32) with 32; lia | exact Hrw]|].
      split; [exact (SPK 152 _ ltac:(lia) S152)|].
      split; [unfold ACtlCut.rgv in *; rewrite P21; exact R21|].
      split; [apply ADF; [lia | lia | exact HA2176]|].
      (* RXS *) unfold ACtlCutP.RXS.
      split; [exact (SPK 48 _ ltac:(lia) X48)|]. split; [exact (SPK 56 _ ltac:(lia) X56)|].
      split; [exact (SPK 88 _ ltac:(lia) X88)|]. split; [exact (SPK 80 _ ltac:(lia) X80)|].
      split; [exact (SPK 72 _ ltac:(lia) X72)|]. split; [exact (SPK 8 _ ltac:(lia) X8)|].
      split; [exact (SPK 0 _ ltac:(lia) X0)|]. split; [exact (SPK 200 _ ltac:(lia) X200)|].
      split; [exact (SPK 216 _ ltac:(lia) X216)|].
      apply ADF; [lia | lia | exact Xad].
    + (* ctl_rt_C: from the post's AR and the read-only view the journal carries (ProgWorldCtlRtC.ctl_rt_C_of_AR) *)
      pose proof HJ2 as (HAR2 & _).
      apply (PWCC.ctl_rt_C_of_AR B TFIB_SYMS LAWS RLO RHI ly2 S2 W2 mem2 md2 HAR2).
      apply (PW.arodata_okP_of_S B RLO RHI RLO RHI); [| lia | lia].
      exact (KM.kitmem_arodataS_journal B RLO RHI _ _ _ _ _ _ _ _ _ _ _ _ _ _ RELRO_IMG HJ2 Haro).
Qed.

End GlueR6.

Print Assumptions glue_seg_R6.

(* Gate check (a Theorem Labs lane 07:18Z): the classes the Sections bind are the CORE copies of the twin modules. *)
Locate CM05.RunCeil.
Locate CO09.lib_shape.
Locate CK11.FPState.
