(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_HufStats.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseWalkArith StrFun HufWalkKit FseRdKit2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RF_huf_tbl_kit RF_huf_rnc_mem RF_huf_rs_pure RF_huf_rs_cl
  RF_huf_rs_fin.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RF_huf_rs_tail () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00C45stdpp9bitvector;definitions7Z_to_bvK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z6to_natC47Corelib5Lists7ListDef6repeatK47Corelib4Init5Logic2eq01K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rI47Corelib4Init9Datatypes6option00C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC47Corelib4Init9Datatypes3appK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell02K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4prod00C56Stdlib6ZArith6BinInt1Z3addK47Corelib4Init9Datatypes4list02C5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_rs_pure7rs_tailC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_rs_pure4rresC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRK47Corelib4Init9Datatypes6option02C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC47Corelib4Init3Nat3addK47Corelib4Init9Datatypes3nat02I47Corelib4Init5Logic2eq00C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr04C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3subC46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib5Lists4List:length_mapC46Stdlib5Lists4List:length_appC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSK4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1C45stdpp9bitvector;definitions9bv_signedC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiC45stdpp9bitvector;definitions6bv_addC56Stdlib6ZArith6BinInt1Z7add_0_rC45stdpp9bitvector;definitions;bv_unsignedC5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC4ELinuxProcessSemantics5Riscv7Prelude4sextC4ELinuxProcessSemantics5Riscv3Sem5alu64C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiI4ELinuxProcessSemantics5Riscv7Prelude4tree00K4ELinuxProcessSemantics5Riscv5Instr5instr03C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextC5ARocqVerifyHarness?AgentSubmission3Lib3ArrArw_cells_of_u8arrK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell05C56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic3and00I47Corelib4Init5Logic2or00K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega7EnvRing5PExpr01C5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_rnc_mem?rd_memsetZ_postK46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z2ltC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_rnc_mem?rd_memset_specZC5ARocqVerifyHarness?AgentSubmission3Lib6MState6ret_pcK46Stdlib9micromega5Tauto8GFormula01C5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame=disjoint_fromC5ARocqVerifyHarness?AgentSubmission3Lib5FrameBrw_cells_transportC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses8or_morphC46Stdlib9micromega;ZifyClasses9and_morphC5ARocqVerifyHarness?AgentSubmission3Lib3Arr?u8arr_transportC47Corelib4Init5Logic3notC5ARocqVerifyHarness?AgentSubmission3Lib5Frame7outsideC5ARocqVerifyHarness?AgentSubmission3Lib5Frame6sub_fpC5ARocqVerifyHarness?AgentSubmission3Lib5Frame<munch_weakenC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;munch_transC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;wmono_transC5ARocqVerifyHarness?AgentSubmission3Lib6MState;ret_pc_evenC47Corelib4Init5Logic6eq_symC5ARocqVerifyHarness?AgentSubmission3Lib3ArrAu8arr_of_rw_cellsC5ARocqVerifyHarness?AgentSubmission3Lib3Arr4u32sC5ARocqVerifyHarness?AgentSubmission3Lib3Mem5wr_atC56Stdlib6ZArith6BinInt1Z3mulK47Corelib4Init5Logic3and01C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbK4ELinuxProcessSemantics5Riscv5Instr5instr05C56Stdlib6ZArith6BinInt1Z3eqbC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeBinr64_unsigned_litC47Corelib4Init5Logic6eq_indC56Stdlib6ZArith6BinInt1Z6eqb_eqI47Corelib5Lists7ListDef6Forall00C56Stdlib6ZArith6BinInt1Z3oppI5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res00K5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res02C5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount9highbit32C56Stdlib6ZArith6BinInt1Z3ltbC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount5shl32C5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3u32C47Corelib4Init9Datatypes4negbC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount6assertC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4loadC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount5storeC56Stdlib6ZArith6BinInt1Z4landC47Corelib4Init9Datatypes3orbK5ARocqVerifyHarness?AgentSubmission4Spec@HufPure_HufStats6hstats01K5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res01C5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4bindC56Stdlib6ZArith6BinInt1Z7eqb_neqC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atC5ARocqVerifyHarness?AgentSubmission3Lib3Mem<bytes_at_appC47Corelib4Init5Logic5proj1K47Corelib5Lists7ListDef6Forall01K46Stdlib9micromega7EnvRing5PExpr05C5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_rs_cl5cl_okC5ARocqVerifyHarness?AgentSubmission3Lib5Frame:munch_reflC5ARocqVerifyHarness?AgentSubmission3Lib5Frame:wmono_reflC5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_rs_cl6cl_invC47Corelib5Lists7ListDef5skipnC5ARocqVerifyHarness?AgentSubmission4Spec@HufPure_HufStats<collect_loopK47Corelib4Init9Datatypes4prod01C5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_rs_fin6rs_finC5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_rs_cl7cl_loopC5ARocqVerifyHarness?AgentSubmission3Lib6ExElim:ex_elim_15C5ARocqVerifyHarness?AgentSubmission3Lib4Exec7evt_cutC5ARocqVerifyHarness?AgentSubmission3Lib3Arr5u8arrC47Corelib5Lists7ListDef3mapC5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC5ARocqVerifyHarness?AgentSubmission3Lib4Exec3evtC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula06C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepK45stdpp9bitvector;definitions2bv01K4ELinuxProcessSemantics5Riscv5Instr5instr08K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:interp_effC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission3Lib6MState8step_genC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lift_resultC46Stdlib9micromega;ZifyClasses5mkappK46Stdlib9micromega5Tauto8GFormula07C5ARocqVerifyHarness?AgentSubmission3Lib3Arr6u32arrK47Corelib5Lists7ListDef6Forall02C5ARocqVerifyHarness?AgentSubmission3Lib4Exec8evt_stepC5ARocqVerifyHarness?AgentSubmission5Ubsan4UImg5usegsI47Corelib7Numbers7BinNums1Z00I5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00I47Corelib4Init9Datatypes3nat00C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addK46Stdlib9micromega:ZMicromega;ZArithProof01I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K4ELinuxProcessSemantics5Riscv5Instr5aluop01K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00C4ELinuxProcessSemantics5Riscv3Sem2w0C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_litC46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqK46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init5Logic4True00I5ARocqVerifyHarness?AgentSubmission4Spec@HufPure_HufStats6hstats00C56Stdlib6ZArith4Znat5Nat2Z8inj_succK47Corelib4Init9Datatypes3nat01C46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib4Init5Logic5False00c5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_rs_tail;u32s_zero13K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01C5ARocqVerifyHarness?AgentSubmission4Spec9FseNCountNZSTD_error_corruption_detectedC5ARocqVerifyHarness?AgentSubmission4Spec@HufPure_HufStats@HUF_TABLELOG_MAXC5ARocqVerifyHarness?AgentSubmission4Spec@HufPure_HufStatsCHUF_SYMBOLVALUE_MAXI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00".
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma u32s_zero13 : u32s (map (Z_to_bv 64) (repeat 0 13)) = repeat (Z_to_bv 8 0) (Z.to_nat 52).
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_rs_tail ()) [] "p;1p;2p;3g0000j10Tg000Uj19Tg0013j13Tg001Vj12Tg0026j28Tg002\j11Tg003Aj17Tg003_j14Tg004?j35Tg004^j26Tg0058R0#0#0#0#9R1#3R2#2g005],81%10#0#1#0#0#7#4552'6o"). Qed.

Section TL.
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  (* [comment removed for export] *)
  Variables (x22 x23 x24 x25 x26 x27 : word).
  Variables (m : fmem) (HW RK NSP TLP iS : Z) (ws : list Z) (junk : list byte) (nsv tlv : word).
  Variable POST : machine_state -> Prop.
  Hypothesis HWS : 0 <= zlen ws <= 255.
  Hypothesis HWB : Forall (fun c => 0 <= c < 256) ws.
  Hypothesis HIS : 0 <= iS <= 128.
  Hypothesis HJK : zlen junk = 256 - zlen ws.
  Hypothesis HHW : 0 < HW /\ HW + 256 <= 2^64.
  Hypothesis HRK : 0 < RK /\ RK + 52 <= 2^64.
  Hypothesis HNT : 0 < NSP /\ NSP + 4 <= TLP /\ TLP + 4 <= 2^64.
  Hypothesis DHR : HW + 256 <= RK \/ RK + 52 <= HW.
  Hypothesis DHN : HW + 256 <= NSP \/ TLP + 4 <= HW.
  Hypothesis DRN : RK + 52 <= NSP \/ TLP + 4 <= RK.
  Hypothesis ARK : RK mod 4 = 0.
  Hypothesis ANS : NSP mod 4 = 0.
  Hypothesis ATL : TLP mod 4 = 0.

  Notation WF := [(HW, HW + 256); (RK, RK + 52); (NSP, NSP + 4); (TLP, TLP + 4)].

  Lemma rs_tail_walk : forall m1 (jr : list byte) (x1 x5 x6 x7 x10 x11 x12 x15 x16 x17 x20 x21 x28 x29 x30 x31 : word),
    u8arr usegs m1 RK jr -> zlen jr = 52 ->
    u8arr usegs m1 HW (map (Z_to_bv 8) ws ++ junk) ->
    rw_cells usegs m1 NSP [C4 nsv] -> rw_cells usegs m1 TLP [C4 tlv] ->
    munch WF m m1 -> wmono usegs m m1 -> mem_inv usegs m1 ->
    (forall m2 a0v (y1 y5 y6 y7 y8 y9 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y28 y29 y30 y31 : word),
       munch WF m m2 -> wmono usegs m m2 -> mem_inv usegs m2 ->
       rres HW RK NSP TLP (rs_tail ws (zlen ws) iS) m2 a0v ->
       evt usegs POST (MS (mkR y1 sp gp tp y5 y6 y7 y8 y9 (Z_to_bv 64 a0v) y11 y12 y13 y14 y15 y16
                               y17 y18 y19 y20 y21 x22 x23 x24 x25 x26 x27 y28 y29 y30 y31)
                          F (Z_to_bv 64 0x1f124) fc None m2 (seg_rom usegs))) ->
    evt usegs POST (MS (mkR x1 sp gp tp x5 x6 x7 (Z_to_bv 64 RK) (Z_to_bv 64 HW) x10 x11 x12 (Z_to_bv 64 NSP)
                            (Z_to_bv 64 TLP) x15 x16 x17 (Z_to_bv 64 (zlen ws)) (Z_to_bv 64 iS) x20 x21 x22 x23 x24 x25 x26 x27
                            x28 x29 x30 x31)
                       F (Z_to_bv 64 0x1eec0) fc None m1 (seg_rom usegs)).
Proof using All.
  intros m1 jr x1 x5 x6 x7 x10 x11 x12 x15 x16 x17 x20 x21 x28 x29 x30 x31 RKA RKL HWA NSC TLC MU WM MI K.
  pose proof (rw_cells_of_u8arr _ _ _ _ RKA) as RKC. clear RKA.
  replace (length jr) with (Z.to_nat 52) in RKC by lia.
  do 6 zstep.
  call (rd_memset_specZ RK 52 0); [exact RKC | exact MI | reflexivity | reflexivity | reflexivity | lia | lia | lia |].
  lazymatch goal with H : rw_cells usegs ?mm RK [CB _ (repeat _ _)] |- _ =>
    apply u8arr_of_rw_cells in H; destruct H as [Hb Hw];
    assert (RK0 : u32arr usegs mm RK (map (Z_to_bv 64) (repeat 0 13)))
      by (split; [rewrite u32s_zero13; exact Hb | rewrite repeat_length in Hw; rewrite length_map, repeat_length; exact Hw]);
    clear Hb Hw
  end.
  zstep. zstep. if_cases K4; zify_cond K4.
  { assert (WS0 : ws = []) by (apply length_zero_iff_nil; lia).
    assert (RE : rs_tail ws (zlen ws) iS = Err ZSTD_error_corruption_detected) by (rewrite WS0; reflexivity).
    eapply K; [exact MU | exact WM | assumption |]. rewrite RE. cbn [rres]. unfold ZSTD_error_corruption_detected. lia. }
  zstep. cl_chk. do 9 zstep.
  pose proof (proj1 HWA) as HB1. apply bytes_at_app in HB1. destruct HB1 as [HB1 _].
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply (cl_loop _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm HW RK ws POST ltac:(lia) HWB HHW HRK DHR
              (Z.to_nat (zlen ws)) 0 (repeat 0 13) 0 mm)
  end;
    [ lia | lia
    | split; [reflexivity | split; [apply Forall_forall; intros v Hv; apply repeat_spec in Hv; subst v; cbv beta; lia | lia]]
    | split; [exact RK0 | split; [exact HB1 | split; [apply munch_refl | split; [apply wmono_refl | assumption]]]]
    | | ].
  - intros m2 rank' wt' y5 y6 y7 y17 y28 CE OK2 INV2.
    destruct INV2 as (RK2 & HB2 & MU2 & WM2 & MI2).
    lazymatch type of MU2 with munch _ ?mm _ => transport_after_call usegs mm m2 MU2 WM2 end.
    eapply rs_fin with (m := m) (ws := ws) (iS := iS) (junk := junk) (nsv := nsv) (tlv := tlv) (m1 := m2)
                       (rank1 := rank') (wt := wt').
    all: try (intros; eapply K; eassumption).
    all: try exact CE.
    all: try eassumption.
    all: try lia.
  - intros m2 rank' y5 y6 y7 y14 y17 y28 CE INV2.
    destruct INV2 as (RK2 & HB2 & MU2 & WM2 & MI2).
    assert (CE' : collect_loop ws (repeat 0 (Z.to_nat (HUF_TABLELOG_MAX + 1))) 0 = Err ZSTD_error_corruption_detected) by exact CE.
    assert (RE : rs_tail ws (zlen ws) iS = Err ZSTD_error_corruption_detected) by (unfold rs_tail; cbv zeta; rewrite CE'; reflexivity).
    lazymatch type of MU2 with munch _ ?mm _ => transport_after_call usegs mm m2 MU2 WM2 end.
    eapply K; [exact MU | exact WM | exact MI2 |]. rewrite RE. cbn [rres]. unfold ZSTD_error_corruption_detected. lia.
Qed.
End TL.
