(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA L5Defs L5Core L5LazyA Pm4PlanKit Pm4L5DefsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmHeapIfaceA IcptIfaceA PmLibDefs PmLibSpecs PmEncSpecs PmLibDefsA PmLibSpecsA PmLibStaticsA PmEncSpecsA PmEncSpecs2A.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeapA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmEncA Require Import EncKitA EncVBeginORkXA EncVBeginARkXA EncVBeginOR0XA EncVBeginAR0XA EncVBeginOIOFXA EncVBeginAIOFXA EncVBeginOIOSXA EncVBeginAIOSXA EncVBeginOIA0FXA EncVBeginAIA0FXA EncVBeginOIA0SXA EncVBeginAIA0SXA EncVBeginOIAKFXA EncVBeginAIAKFXA EncVBeginOIAKSXA EncVBeginAIAKSXA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module EVBGA.
Import PMES.
Section VisitBegin.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable HI : asan_iface.
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.
Hypothesis LAY : L5A.as0_layout L C.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps (hl_segs L) (@mkst fx R (Z_to_bv 64 pc) M (seg_rom (hl_segs L))) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom (hl_segs L))) -> PMSA.fp_ok fx -> PMSA.fp_ok fx'.
Variable CL : Z.
Variable onmax : Z.
Variable IL0 : icpt_layout.
Hypothesis ACC_OBRACE : PMESA.img_aacc HI 0x24b28 1.
Hypothesis ACC_OBRACKET : PMESA.img_aacc HI 0x24b2e 1.
Hypothesis ACC_COMMA : PMESA.img_aacc HI 0x24b1c 2.
Hypothesis ISH : rt_img_shadow L IL0 HI.
Hypothesis POI_VBO : Forall (fun r : Z * Z => 0x15ab58 + 8 <= fst r \/ snd r <= 0x15ab58) (icl_poison IL0).
Hypothesis FOOTXC : forall a, PMLA.in_footx PMLA.C_xasan a -> ~ hl_rt_static L a /\ ~ hl_rt_ro L a.
Hypothesis NEWLINE2_OK : PMESA.new_line2_specA L ar HI PMLA.C_xasan CL 0xba814.
Hypothesis APPEND_OK : PMESA.str_append_x_specA L ar HI PMLA.C_xasan CL 0xfe144.
Hypothesis CLOK : EKA.clok CL onmax.
Hypothesis PUSH_FAST_ROOT : PMES2A.push_fast_specA L ar HI 0xca6bc.
Hypothesis PUSH_SLOW_ROOT : PMES2A.push_slow_specA L ar HI onmax 0xca6bc.
Hypothesis PUSH_FAST_NESTED : PMES2A.push_fast_specA L ar HI 0xca1ac.
Hypothesis PUSH_SLOW_NESTED : PMES2A.push_slow_specA L ar HI onmax 0xca1ac.

Theorem visit_begin_object_ok : PMESA.visit_begin_object_specA L ar HI PMLA.C_xasan PMESA.EC_xasan 12800 CL PMESA.PC_VISIT_BEGIN_OBJECT_xasan.
Proof.
  intros LBo FF LK cr A sp r V S2 kx bx g.
  destruct g as [es len rep sb scap] eqn:Hg. rewrite <- Hg.
  destruct es as [|[arr cnt nla0] r0].
  - destruct (Z.eq_dec scap 0) as [Z0|NZ].
    + exact (visit_begin_object_root0_ok L ar C HI HIok LAY FPM CL onmax IL0 ACC_OBRACE ISH POI_VBO FOOTXC APPEND_OK CLOK PUSH_SLOW_ROOT LBo FF LK cr A sp r V S2 kx bx g ltac:(rewrite Hg; reflexivity) ltac:(rewrite Hg; exact Z0)).
    + exact (visit_begin_object_rootk_ok L ar C HI HIok LAY FPM CL IL0 ACC_OBRACE ISH POI_VBO FOOTXC APPEND_OK PUSH_FAST_ROOT LBo FF LK cr A sp r V S2 kx bx g ltac:(rewrite Hg; reflexivity) ltac:(rewrite Hg; exact NZ)).
  - destruct (Z_lt_dec (32 * depth (ECtx arr cnt nla0 :: r0)) scap) as [LT|GE].
    + destruct arr.
      * destruct (Z.eq_dec cnt 0) as [C0|CK].
        -- exact (visit_begin_object_inarr0_fast_ok L ar C HI HIok LAY FPM CL IL0 ACC_OBRACE ISH POI_VBO FOOTXC NEWLINE2_OK APPEND_OK PUSH_FAST_NESTED LBo FF LK cr A sp r V S2 kx bx g _ r0 ltac:(rewrite Hg; reflexivity) eq_refl C0 ltac:(rewrite Hg; exact LT)).
        -- exact (visit_begin_object_inarrk_fast_ok L ar C HI HIok LAY FPM CL IL0 ACC_OBRACE ACC_COMMA ISH POI_VBO FOOTXC NEWLINE2_OK APPEND_OK PUSH_FAST_NESTED LBo FF LK cr A sp r V S2 kx bx g _ r0 ltac:(rewrite Hg; reflexivity) eq_refl CK ltac:(rewrite Hg; exact LT)).
      * exact (visit_begin_object_inobj_fast_ok L ar C HI HIok LAY FPM CL IL0 ACC_OBRACE ISH POI_VBO FOOTXC APPEND_OK PUSH_FAST_NESTED LBo FF LK cr A sp r V S2 kx bx g _ r0 ltac:(rewrite Hg; reflexivity) eq_refl ltac:(rewrite Hg; exact LT)).
    + destruct arr.
      * destruct (Z.eq_dec cnt 0) as [C0|CK].
        -- exact (visit_begin_object_inarr0_slow_ok L ar C HI HIok LAY FPM CL onmax IL0 ACC_OBRACE ISH POI_VBO FOOTXC NEWLINE2_OK APPEND_OK CLOK PUSH_SLOW_NESTED LBo FF LK cr A sp r V S2 kx bx g _ r0 ltac:(rewrite Hg; reflexivity) eq_refl C0 ltac:(rewrite Hg; cbn [g_scap g_es]; clear - GE; lia)).
        -- exact (visit_begin_object_inarrk_slow_ok L ar C HI HIok LAY FPM CL onmax IL0 ACC_OBRACE ACC_COMMA ISH POI_VBO FOOTXC NEWLINE2_OK APPEND_OK CLOK PUSH_SLOW_NESTED LBo FF LK cr A sp r V S2 kx bx g _ r0 ltac:(rewrite Hg; reflexivity) eq_refl CK ltac:(rewrite Hg; cbn [g_scap g_es]; clear - GE; lia)).
      * exact (visit_begin_object_inobj_slow_ok L ar C HI HIok LAY FPM CL onmax IL0 ACC_OBRACE ISH POI_VBO FOOTXC APPEND_OK CLOK PUSH_SLOW_NESTED LBo FF LK cr A sp r V S2 kx bx g _ r0 ltac:(rewrite Hg; reflexivity) eq_refl ltac:(rewrite Hg; cbn [g_scap g_es]; clear - GE; lia)).
Qed.

Theorem visit_begin_array_ok : PMESA.visit_begin_array_specA L ar HI PMLA.C_xasan PMESA.EC_xasan 12800 CL PMESA.PC_VISIT_BEGIN_ARRAY_xasan.
Proof.
  intros LBo FF LK cr A sp r V S2 kx bx g.
  destruct g as [es len rep sb scap] eqn:Hg. rewrite <- Hg.
  destruct es as [|[arr cnt nla0] r0].
  - destruct (Z.eq_dec scap 0) as [Z0|NZ].
    + exact (visit_begin_array_root0_ok L ar C HI HIok LAY FPM CL onmax IL0 ACC_OBRACKET ISH POI_VBO FOOTXC APPEND_OK CLOK PUSH_SLOW_ROOT LBo FF LK cr A sp r V S2 kx bx g ltac:(rewrite Hg; reflexivity) ltac:(rewrite Hg; exact Z0)).
    + exact (visit_begin_array_rootk_ok L ar C HI HIok LAY FPM CL IL0 ACC_OBRACKET ISH POI_VBO FOOTXC APPEND_OK PUSH_FAST_ROOT LBo FF LK cr A sp r V S2 kx bx g ltac:(rewrite Hg; reflexivity) ltac:(rewrite Hg; exact NZ)).
  - destruct (Z_lt_dec (32 * depth (ECtx arr cnt nla0 :: r0)) scap) as [LT|GE].
    + destruct arr.
      * destruct (Z.eq_dec cnt 0) as [C0|CK].
        -- exact (visit_begin_array_inarr0_fast_ok L ar C HI HIok LAY FPM CL IL0 ACC_OBRACKET ISH POI_VBO FOOTXC NEWLINE2_OK APPEND_OK PUSH_FAST_NESTED LBo FF LK cr A sp r V S2 kx bx g _ r0 ltac:(rewrite Hg; reflexivity) eq_refl C0 ltac:(rewrite Hg; exact LT)).
        -- exact (visit_begin_array_inarrk_fast_ok L ar C HI HIok LAY FPM CL IL0 ACC_OBRACKET ACC_COMMA ISH POI_VBO FOOTXC NEWLINE2_OK APPEND_OK PUSH_FAST_NESTED LBo FF LK cr A sp r V S2 kx bx g _ r0 ltac:(rewrite Hg; reflexivity) eq_refl CK ltac:(rewrite Hg; exact LT)).
      * exact (visit_begin_array_inobj_fast_ok L ar C HI HIok LAY FPM CL IL0 ACC_OBRACKET ISH POI_VBO FOOTXC APPEND_OK PUSH_FAST_NESTED LBo FF LK cr A sp r V S2 kx bx g _ r0 ltac:(rewrite Hg; reflexivity) eq_refl ltac:(rewrite Hg; exact LT)).
    + destruct arr.
      * destruct (Z.eq_dec cnt 0) as [C0|CK].
        -- exact (visit_begin_array_inarr0_slow_ok L ar C HI HIok LAY FPM CL onmax IL0 ACC_OBRACKET ISH POI_VBO FOOTXC NEWLINE2_OK APPEND_OK CLOK PUSH_SLOW_NESTED LBo FF LK cr A sp r V S2 kx bx g _ r0 ltac:(rewrite Hg; reflexivity) eq_refl C0 ltac:(rewrite Hg; cbn [g_scap g_es]; clear - GE; lia)).
        -- exact (visit_begin_array_inarrk_slow_ok L ar C HI HIok LAY FPM CL onmax IL0 ACC_OBRACKET ACC_COMMA ISH POI_VBO FOOTXC NEWLINE2_OK APPEND_OK CLOK PUSH_SLOW_NESTED LBo FF LK cr A sp r V S2 kx bx g _ r0 ltac:(rewrite Hg; reflexivity) eq_refl CK ltac:(rewrite Hg; cbn [g_scap g_es]; clear - GE; lia)).
      * exact (visit_begin_array_inobj_slow_ok L ar C HI HIok LAY FPM CL onmax IL0 ACC_OBRACKET ISH POI_VBO FOOTXC APPEND_OK CLOK PUSH_SLOW_NESTED LBo FF LK cr A sp r V S2 kx bx g _ r0 ltac:(rewrite Hg; reflexivity) eq_refl ltac:(rewrite Hg; cbn [g_scap g_es]; clear - GE; lia)).
Qed.
End VisitBegin.
End EVBGA.
Print Assumptions EVBGA.visit_begin_object_ok.
