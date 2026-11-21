(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the recorded proofs of zal_ex, lock_spec replaced by plain proofs). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import ImageA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import Arr Walk.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Malloc Require Import MallocKit_AB.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import R_small R_cache_defs R_depot_defs.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import FarStep.
Ltac2 kr_t_R_depot_lock () := "C56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z6moduloI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3divC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z2leK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic6eq_indK47Corelib4Init5Logic2ex01K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op205K47Corelib7Numbers7BinNums8positive03K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums8positive01I47Corelib4Init9Datatypes6option00K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powI47Corelib4Init5Logic3and00C45stdpp9bitvector;definitions7Z_to_bvK69OSSVerify5KrLib2K53Lib5Cells4cell02C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z3subI47Corelib4Init9Datatypes4prod00C69OSSVerify5KrLib2K53Lib5Frame:munch_reflC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame5munchC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame:wmono_reflC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02C56Stdlib6ZArith6BinInt1Z6of_natC47Corelib4Init5Logic8iff_reflC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr04C69OSSVerify5KrLib2K53Lib5Frame9stk_carveC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00c69OSSVerify5KrLib2K53B23<R_depot_lock9lock_postC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame3mkRC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K56Common8PropExec7seg_romC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03C56Stdlib6ZArith6BinInt1Z7comparec69OSSVerify5KrLib2K53B23<R_depot_lock6zal_exC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions9bv_signedC69OSSVerify5KrLib2K56Common8PropExec6v_addiC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude4sextC69OSSVerify5KrLib2K56Common8PropExec8alu_addiC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr08K4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02C69OSSVerify5KrLib2K53Lib6MState2MSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast8sf_congTC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr07C69OSSVerify5KrLib2K53Lib3Mem3le8C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions6bv_addC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC69OSSVerify5KrLib2K56Common8PropExec9b_addsextC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9add_assocC69OSSVerify5KrLib2K53Lib8StepFast6sf_ad1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast=sf_addr_ztobvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast@sf_store8_directC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast7sf_reflC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast@sf_install_storeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells;cb_split_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells8cb_splitC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K53Lib5Cells4cell01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells5csizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4StepArw_cells_store_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells8cell_updC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells6cbytesC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6eq_iffK46Stdlib9micromega7EnvRing5PExpr07C47Corelib4Init9Datatypes6lengthC69OSSVerify5KrLib2K53Lib3Mem:length_le8C1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses;rew_iff_revC69OSSVerify5KrLib2K53Lib5Frame6insideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame;munch_writeC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00C46Stdlib9micromega;ZifyClasses8or_morphC69OSSVerify5KrLib2K53Lib3Mem2waC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6firstnC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega5Tauto8GFormula01C69OSSVerify5KrLib2K53Lib5Frame=disjoint_fromC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5FrameBrw_cells_transportC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7add_0_rC69OSSVerify5KrLib2K53Lib4StepDunsigned_Z_to_bv_addC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem5alu64C56Stdlib6ZArith6BinInt1Z6shiftlC69OSSVerify5KrLib2K56Common8PropExec5v_luiC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions9bv_concatC69OSSVerify5KrLib2K56Common8PropExec5b_luiC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr01C4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC69OSSVerify5KrLib2K53Lib3Mem4sx32C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem3le4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem@sext_extract_le4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Step=wa_of_Z_to_bvC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC69OSSVerify5KrLib2K53Lib4Step@rw_cells_read_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast<sf_load_goalC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr06C4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setK4ELinuxProcessSemantics5Riscv5Instr5instr05C4ELinuxProcessSemantics5Riscv7Prelude6bv_ltsC47Corelib4Init9Datatypes4negbC69OSSVerify5KrLib2K53Lib8StepFast<sf_branch_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast8sf_cong1C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3ltbC46Stdlib4Bool4Bool=negb_true_iffC56Stdlib6ZArith6BinInt1Z6ltb_geC47Corelib4Init5Logic5proj2K46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z3oppC69OSSVerify5KrLib2K53B23<R_depot_defs>dep_signed_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K56Common8PropExec4v_orC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib7ZBridge6zr_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib7ZBridgeBinr64_unsigned_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K56Common8PropExec6alu_orC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0:C56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z6eqb_eqC69OSSVerify5KrLib2K53Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepK4ELinuxProcessSemantics5Riscv5Instr5instr0DK4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC69OSSVerify5KrLib2K53Lib6MState:interp_effC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib6MState;lift_resultC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okK4ELinuxProcessSemantics5Riscv3Sem3eff06C4ELinuxProcessSemantics5Riscv3Sem5is_x0K4ELinuxProcessSemantics5Riscv3Sem3eff01K4ELinuxProcessSemantics5Riscv3Sem3eff07C69OSSVerify5KrLib2K53Lib6MState;lit_add_litC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude4tgetC69OSSVerify5KrLib2K53Lib6MState8step_genC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC46Stdlib4Bool4Bool>negb_false_iffK4ELinuxProcessSemantics5Riscv5Instr5instr0EC4ELinuxProcessSemantics5Riscv3Sem5low32K4ELinuxProcessSemantics5Riscv3Sem3eff08C35stdpp7tactics<f_equal_helpC69OSSVerify5KrLib2K53Lib4StepDrw_cells_store_ok_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Step>store_bytes_4'C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8eqb_reflC4ELinuxProcessSemantics5Riscv7Prelude4tsetC4ELinuxProcessSemantics5Riscv3Sem7reg_getC69OSSVerify5KrLib2K53Lib4Step>rw_cells_writeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem:length_le4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Step>rw_cells_frameC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib8StepFast?sf_load8_directC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Step@Z_to_bv_lit_selfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame;stk_releaseC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions6bv_notC45stdpp9bitvector;definitions6bv_andC69OSSVerify5KrLib2K53Lib6MState6ret_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib6MState;ret_pc_foldC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr04C69OSSVerify5KrLib2K53Lib4Exec8evt_doneC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Exec8evt_stepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B237R_small<sx32_small_AC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame3stkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib2K53Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelK69OSSVerify5KrLib2K53Lib5Cells4cell05C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Exec3evtC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr03C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C47Corelib5Lists7ListDef5skipnC69OSSVerify5KrLib2K53Lib4StepArw_cells_cb_splitC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC69OSSVerify5KrLib2K53Lib4Step>rw_cells_boundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells7cell_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4StepDmem_inv_store_cbytesC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses7rew_iffK46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula06C69OSSVerify5KrLib2K53Lib5Frame;wmono_writeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame9stk_writeC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions:bv_extractC69OSSVerify5KrLib2K53Lib8StepFast?sf_install_loadC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lorC4ELinuxProcessSemantics5Riscv3Sem;amo_alignedC69OSSVerify5KrLib2K53Lib8StepFast;sf_evt_stepC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K53Lib5Cells4cell00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236ImageA5asegsC1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib4Init9Datatypes3nat00K46Stdlib9micromega=RingMicromega3Op203K4ELinuxProcessSemantics5Riscv5Instr5aluop01K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics5Riscv3Sem4core00K47Corelib4Init5Logic4True01C4ELinuxProcessSemantics5Riscv3Sem2w0C69OSSVerify5KrLib2K53Lib6MState6w0_litC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N01K47Corelib4Init9Datatypes3nat01K4ELinuxProcessSemantics5Riscv5Instr6awidth01K4ELinuxProcessSemantics5Riscv5Instr5msize04I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00K46Stdlib9micromega:ZMicromega;ZArithProof01K4ELinuxProcessSemantics5Riscv5Instr5msize03K4ELinuxProcessSemantics5Riscv5Instr;branch_cond04K4ELinuxProcessSemantics5Riscv5Instr5aluop09I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I4ELinuxProcessSemantics5Riscv3Sem3eff00I47Corelib7Numbers7BinNums1N00I47Corelib7Numbers7BinNums8positive00K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02C4ELinuxProcessSemantics5Riscv3Sem2w1K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01C69OSSVerify5KrLib2K53Lib6MState6w1_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23<R_depot_defs:lock_entryC1?~~~~~~~~~~~~~~~".   (* [comment removed for export] *)
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Definition zal (k x r : Z) : Prop := (x mod k = r)%Z.
Local Lemma zal_ex : forall k x r : Z, (0 < k)%Z -> (x mod k = r)%Z -> exists q, x = (k * q + r)%Z.
Proof. intros k x r Hk H. exists (x / k)%Z. rewrite <- H. apply Z.div_mod. lia. Qed.
Local Ltac zlit x := lazymatch x with Zpos _ => idtac | Z0 => idtac | Zneg _ => idtac end.
Local Ltac zget_mod t :=
  lazymatch type of t with
  | (?x mod ?k = ?r)%Z => let H' := fresh "Hzm" in pose proof t as H'
  | ?A /\ ?B => first [ zget_mod constr:(proj1 t) | zget_mod constr:(proj2 t) ]
  end.
Local Ltac zhide :=
  repeat match goal with
  | H : context [(?x mod ?k)%Z] |- _ => zlit x; zlit k; let v := eval cbv in (x mod k)%Z in change (x mod k)%Z with v in H
  end;
  repeat match goal with
  | H : (?x mod ?k = ?r)%Z |- _ =>
      let q := fresh "zq" in let Hq := fresh "Hzq" in
      destruct (zal_ex k x r (eq_refl : (0 < k)%Z) H) as [q Hq]; change (zal k x r) in H
  | H : context [(?x mod ?k = ?r)%Z] |- _ =>
      lazymatch type of H with (_ mod _ = _)%Z => fail | _ => idtac end;
      (try zget_mod H); change (x mod k = r)%Z with (zal k x r) in H
  end;
  repeat match goal with
  | H : context [(2 ^ ?k)%Z] |- _ => let T := type of H in zify_arith_prop T;
      let v := eval cbv in (2 ^ k)%Z in lazymatch v with Zpos _ => change (2 ^ k)%Z with v in H end
  end.
(* [comment removed for export] *)
Local Definition zidle (P : Prop) : Prop := P.
Local Ltac zidle1 H := let T := type of H in change (zidle T) in H.
Local Ltac zidle_nsp H A sp := lazymatch A with context [bv_unsigned sp] => fail | _ => zidle1 H end.
Local Ltac zidle_begin sp n MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
    pose proof (munch_refl [(bv_unsigned sp - n, bv_unsigned sp)]%Z m) as MUz; pose proof (wmono_refl segs m) as WMz;
    repeat match goal with
    | H : rw_cells segs m ?A _ |- _ => zidle_nsp H A sp
    | H : ro_cells segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u8arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u32arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u64arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : bytes_at segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u8ro segs m ?A _ |- _ => zidle_nsp H A sp
    end
  end.
Local Ltac zidle_end MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch type of MUz with munch _ ?m _ =>
      try unfold zidle in *; transport_after_call segs m mm MUz WMz; clear MUz WMz end end.
(* [comment removed for export] *)
Local Ltac zidle_end_m m :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with MU : munch _ m mm, WM : wmono _ m mm |- _ =>
      unfold zidle in *; transport_after_call asegs m mm MU WM end end.
Open Scope bv_scope.
Notation mem := (word -> option byte).

(* [comment removed for export] *)
Definition lock_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A v lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 v) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(A, A + 4); (bv_unsigned sp - 48, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ (exists w, rw_cells asegs m' A [C4 w])
    /\ stk asegs m' lo (bv_unsigned sp).

Lemma lock_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (A v lo : Z),
  (0 <= A /\ A + 4 <= 2^63)%Z -> (A mod 4 = 0)%Z -> (0 <= v < 2^31)%Z ->
  rw_cells asegs m A [C4 (Z_to_bv 64 v)] ->
  stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 48)%Z -> (A + 4 <= lo \/ bv_unsigned sp <= A)%Z ->
  mem_inv asegs m ->
  evt asegs (lock_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A v lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 lock_entry) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros HA HA4 Hv BK ST HLO HSEP MI. unfold lock_entry.
  pose proof (munch_refl [(A, A + 4); (bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  carve_frame 48%nat ST.
  zhide.
  zidle_begin sp 48%Z MUz WMz.
  do 6 zstep.
  zidle_end MUz WMz.
  do 4 zstep.
  zstep. rewrite (sx32_small_A v) by lia.
  zstep. dIfT_s.
  zstep.
  assert (AMO : amo_aligned AW (Z_to_bv 64 A) = true).
  { unfold amo_aligned, amo_bytes. rewrite unsigned_lit by lia. apply Z.eqb_eq. exact HA4. }
  amo_step AMO. rewrite (sx32_small_A v) by lia.
  zstep. ifF.
  amo_step AMO; try fix_lit_store.
  zstep. ifF.
  zstep. ifT.
  do 6 zstep.
  release_frame FR ST (bv_unsigned sp).
  zstep.
  finish.
  eexists. eassumption.
Qed.
