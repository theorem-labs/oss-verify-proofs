(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From stdpp Require list.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Ubsan.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PropExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SeqExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StepTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.WalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StartupTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SumWalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StoreOk OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MemSplit OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Hoare OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ShapeAlg OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SRealizes OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefReadLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.FPSteps OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibIface OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibBudget OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibEff OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MmapSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibMaskBits OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ZStores OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3Sound OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymRun3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.U1Layout.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.CRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.StrLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.LiveStats OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContStmts2 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.U1Facts.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRepFacts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HStmtsU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HCommonU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HConstsU1.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsNeeds OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsInv OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmBaseU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmHyps OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmHypsU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmCoreU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStepU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep2U1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmLoopU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmInstU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep3U1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmODefsU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep4U1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmZw OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmOLoopU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmOLoop2U1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Module PmOLoop3U1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.

Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PropExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SeqExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StepTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.WalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StartupTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SumWalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StoreOk OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MemSplit OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Hoare OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ShapeAlg OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SRealizes OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefReadLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.FPSteps OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibIface OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibBudget OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibEff OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MmapSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibMaskBits OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ZStores OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3Sound OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymRun3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.U1Layout.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.CRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.StrLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.LiveStats OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContStmts2 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.U1Facts.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRepFacts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HStmtsU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HCommonU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HConstsU1.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsNeeds OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsInv OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmBaseU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmHyps OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmHypsU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmCoreU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStepU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep2U1.PmUpdU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep2U1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmLoopU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmInstU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep3U1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmODefsU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep4U1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmZw OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmOLoopU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmOLoop2U1.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Abbreviation SEGS := Ubsan.M.loaded_segments.

Module Ly := U1Layout.

Section PM.
Context {AC : AllocCeiling}.
  Context {MI : MallocIface SEGS Ly.L} {ST : StaticsIface SEGS Ly.L}.
  Context {G : grammar} {idesc : Z -> Z -> Prop} {odesc edesc : Z -> Z -> Z -> Prop}
          {generates_type is_ext_inst is_nonsemantic : Z -> bool}
          {ds_rep : AS MI -> mem -> Z -> Z -> Z -> list (Z * Z) -> Prop}.
  Variable CL : pm_calleesU1 SEGS Ly.L MI ST G tcU1 dcU1 nfcU1 HConstsU1.hc ccU1 kcU1
                  idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep.

  #[local] Notation PMX := (PmBaseU1.PMX MI ST).
  #[local] Notation cfg fx R pc M model := (mkCfg (@mkst fx R (Z_to_bv 64 pc) M (seg_rom SEGS)) model).
  #[local] Notation DL := (cu_ds_laws _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
  #[local] Notation pm_exit := (PmCoreU1.pm_exit MI ST).
  #[local] Notation pmx_ds_room := (PmStepU1.pmx_ds_room CL).
  #[local] Notation pm_tail_6733c := (PmStepU1.pm_tail_6733c CL).
  #[local] Notation cregs_kept := (PmStepU1.cregs_kept CL).
  #[local] Notation pm_put_cstr := (PmStepU1.pm_put_cstr CL).
  #[local] Notation pm_put_chars := (PmStepU1.pm_put_chars CL).
  #[local] Notation pm_put_num := (PmStepU1.pm_put_num CL).
  #[local] Notation pm_put_u16 := (PmStepU1.pm_put_u16 CL).
  #[local] Notation pm_put_u32 := (PmStepU1.pm_put_u32 CL).
  #[local] Notation pm_put_u64 := (PmStepU1.pm_put_u64 CL).
  #[local] Notation pm_put_int := (PmStepU1.pm_put_int CL).
  #[local] Notation pm_pdiagQ := (PmStepU1.pm_pdiagQ CL).
  #[local] Notation pm_dtor := (PmStepU1.pm_dtor CL).
  #[local] Notation pm_exhausted := (PmStepU1.pm_exhausted CL).
  #[local] Notation pm_fixword := (PmStepU1.pm_fixword CL).
  #[local] Notation pm_is_host_endian := (PmStepU1.pm_is_host_endian CL).
  #[local] Notation pm_binend := (PmStepU1.pm_binend CL).
  #[local] Notation pm_ecw_pbs := (PmStep2U1.pm_ecw_pbs CL).
  #[local] Notation pm_ecw_pbs1 := (PmStep2U1.pm_ecw_pbs1 CL).
  #[local] Notation pm_ecw_pbs2 := (PmStep2U1.pm_ecw_pbs2 CL).
  #[local] Notation pmx_upd_foot := (PmStep2U1.pmx_upd_foot).
  #[local] Notation pm_v2_push_fast := (PmStep2U1.pm_v2_push_fast).
  #[local] Notation pm_opcode_split := (PmStep2U1.pm_opcode_split CL).
  #[local] Notation pm_lookup_opcode := (PmStep2U1.pm_lookup_opcode CL).
  #[local] Notation pm_lookup_operand := (PmStep2U1.pm_lookup_operand CL).
  #[local] Notation pm_lookup_ext := (PmStep2U1.pm_lookup_ext CL).
  #[local] Notation pm_idesc_operands := (PmStep3U1.pm_idesc_operands CL).
  #[local] Notation pm_odesc_operands := (PmStep3U1.pm_odesc_operands CL).
  #[local] Notation pm_edesc_operands := (PmStep3U1.pm_edesc_operands CL).
  #[local] Notation pm_push_types := (PmStep3U1.pm_push_types CL).
  #[local] Notation pm_take_first := (PmStep3U1.pm_take_first CL).

  #[local] Notation izero := (PmInstU1.izero).
  #[local] Notation ictx := (PmInstU1.ictx).
  #[local] Notation nodes := (PmLoopU1.nodes).
  #[local] Notation macct := (PmLoopU1.macct).
  #[local] Notation ipure := (PmODefsU1.ipure (G:=G) (idesc:=idesc)).
  #[local] Notation arm_stmt := (PmODefsU1.arm_stmt (MI:=MI) (ST:=ST) (G:=G) (idesc:=idesc)).
  #[local] Notation pm_check_err := (@PmOLoopU1.pm_check_err AC MI ST).
  #[local] Notation pm_X1 := (PmOLoopU1.pm_X1 CL).
  #[local] Notation pm_push := (PmOLoopU1.pm_push CL).
  #[local] Notation PREGS := (PmOLoopU1.PREGS).
  #[local] Notation pm_copy_loop := (PmOLoop2U1.pm_copy_loop CL).
  #[local] Notation pm_v2_end_store := (PmOLoop2U1.pm_v2_end_store).

  Lemma set_v2_self : forall c, set_v2 c (c_v2 c) = c.
  Proof using. intros c; destruct c; reflexivity. Qed.

  Ltac oregs_seeded HRn Qgp Qtp :=
    let G2 := fresh in let G3 := fresh in let G4 := fresh in let G8 := fresh in let G9 := fresh in
    let G18 := fresh in let G19 := fresh in let G20 := fresh in let G21 := fresh in let G25 := fresh in
    rreg HRn 2%bv G2; rreg HRn 3%bv G3; rreg HRn 4%bv G4; rreg HRn 8%bv G8; rreg HRn 9%bv G9;
    rreg HRn 18%bv G18; rreg HRn 19%bv G19; rreg HRn 20%bv G20; rreg HRn 21%bv G21; rreg HRn 25%bv G25;
    unfold oregs, loop_regs; rewrite G2, G3, G4, G8, G9, G18, G19, G20, G21, G25; fixregs; rewrite ?Qgp, ?Qtp;
    rewrite ?SymExec.alu64_add_lit; repeat split; reflexivity.
  #[local] Notation OREGSEED := [(9%bv, EAlu ALU_ADD (EVar 33) (ELit 88)); (18%bv, ELit 1); (19%bv, ELit (2 ^ 61)); (20%bv, ELit 20); (21%bv, EAlu ALU_ADD (EVar 33) (ELit 264)); (25%bv, ELit 5)]%list.

  Lemma pm_push_tail2 : forall (w : pmw MI ST) c0 K (fx : FPState) (I : ictxR) A M model c R (t nw : Z),
    PMS w c0 K -> frm_zero (@fp_csr fx) -> ipure I ->
    PMX w A M model c -> c_tr c = [] -> pm_bud (w_n w) c -> oregs w R -> loop_mem w M ->
    ictx w M (i_io I) (i_fw I) (i_iwc I) (i_op I) (i_d I) -> ifr w M ->
    c_icount c + 4 <= i_io I -> c_endian c < 2 -> w_words w <> 0 -> macct c -> Forall (fun t => 0 <= t < 2 ^ 31) (t3b (c_v3 c)) ->
    getr R 27%bv = Z_to_bv 64 t -> getr R 23%bv = Z_to_bv 64 (i_io I) -> getr R 26%bv = Z_to_bv 64 (i_op I) -> 0 <= t < 2 ^ 32 ->
    cellw SEGS M (w_sp w + 718) 2 nw ->
    i_io I + 1 <= c_widx c -> c_widx c < i_io I + i_iwc I ->
    Zlen (t3b (c_v2 c)) <= c_widx c - i_io I ->
    (forall A' M' model' R' (v2 : Z * list Z * Z),
        OBASE w I A' M' model' (set_scal (set_v2 c v2) (c_widx c + nw) (c_icount c) (c_endian c) (c_reqconv c)) R' ->
        Zlen (t3b v2) <= Zlen (t3b (c_v2 c)) + nw -> c_widx c + nw <= w_n w ->
        srealizes SEGS (cfg fx R' 0x677d0 M' model') K) ->
    srealizes SEGS (cfg fx R 0x67fec M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx I A M model c R t nw PS FZ IP X Htr BUD OR LM IC IFR Hic He2 Hw MACC FR3 Q27 Q23 Q26 Ht Cnw Hw1 Hw2 Hv2 HEADK.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & [Gc2 Gcal] & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof (x_scal X) as (Sc1 & Sc2 & Sc3 & Sc4). pose proof (ipure_ranges I IP) as (Riwc & Rop). pose proof IP as IP'. destruct IP' as (_ & _ & _ & _ & _ & _ & Rio).
    pose proof OR as OR'. destruct OR' as (Qsp & Qgp & Qtp & Qs0 & Qs1 & Qs2 & Qs3 & Qs4 & Qs5 & Qs9).
    pose proof (proj1 Cnw) as Rnw. cbn in Rnw.
    destruct (Gw Hw) as (W1 & W2 & W3 & W4 & W5).
    pose proof (fld_cellw M _ 8 _ (x_widx X) ltac:(lia)) as Cwi. unfold O_WIDX in Cwi.
    pose proof (fld_cellw M _ 8 _ (x_n X) ltac:(lia)) as Cn. unfold O_N in Cn.
    pose proof (flags_lo_byte M (w_p w) (c_reqconv c) ltac:(pose proof (x_flags X) as F; unfold O_FLAGS in F; exact F) Sc4) as C92.
    pose proof (fld_cellw M _ 4 _ (x_endian X) ltac:(lia)) as Ce. unfold O_ENDIAN in Ce.
    pose proof (fld_cellw M _ 8 _ (x_words X) ltac:(lia)) as Cws. unfold O_WORDS in Cws.

    assert (TAIL : forall A2 M2 model2 R4 (v2 : Z * list Z * Z),
              PMX w A2 M2 model2 (set_v2 c v2) -> pm_bud (w_n w) (set_v2 c v2) -> Zlen (t3b v2) <= Zlen (t3b (c_v2 c)) + nw ->
              oregs w R4 -> getr R4 24%bv = Z_to_bv 64 (c_widx c + nw) -> loop_mem w M2 ->
              ictx w M2 (i_io I) (i_fw I) (i_iwc I) (i_op I) (i_d I) -> ifr w M2 -> c_widx c + nw <= w_n w ->
              srealizes SEGS (cfg fx R4 0x68120 M2 model2) K).
    { intros A2 M2 model2 R4 v2 X2 BUD2 Hl2 OR4 F24 LM2 IC2 IFR2 Hfit. pose proof (x_ms X2) as MS2.
      pose proof OR4 as OR4'. destruct OR4' as (Usp & Ugp & Utp & Us0 & Us1 & Us2 & Us3 & Us4 & Us5 & Us9).
      pm_seed R4 w (set_v2 c v2) [Z_to_bv 64 (c_widx c + nw)].
      seedHR HR E ([(2%bv, EVar 32); (8%bv, EVar 33); (24%bv, EVar 39)] ++ OREGSEED)%list R4. seedHK HK w A2 M2 model2 (set_v2 c v2) E X2.
      xruns HR HK 100%nat (0x677d0 :: STOPS) (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
      postrun. name_run HRn R5.

      lazymatch type of HRn with regs_ok ?E5 _ _ =>
        lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ => assert (HK2 : know_ok SEGS E5 m []) by constructor end end.
      xruns HRn HK2 20%nat (0x677d0 :: STOPS) (SCR [] [] []) 50%N.
      { split_scs; try sc_auto1. }
      postrun. name_run HRm R6.
      assert (OR6 : oregs w R6) by (oregs_seeded HRm Ugp Utp). clear HRm HRn HR HK HK2.
      lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ => set (M3 := m) in * end.
      assert (ST3 : stores_in (zwin (w_p w + 72) (w_p w + 80)) M2 M3) by (unfold M3; stin).
      pose proof (x_scal X2) as (T1 & T2 & T3 & T4). cbn [set_v2 c_widx c_icount c_endian c_reqconv] in T1, T2, T3, T4.
      assert (X3 : PMX w A2 M3 model2 (set_scal (set_v2 c v2) (c_widx c + nw) (c_icount c) (c_endian c) (c_reqconv c))).
      { eapply (pmx_stores SEGS Ly.L MI ST ly_img_low ly_rw_img ly_relro_img);
          [exact X2 | exact ST3 | intros a Ha; right; unfold scal_win, zwin, O_WIDX, O_FLAGS, w_sp0, PM_FRAME in *; lia
          | unfold M3, O_WIDX; rdback
          | eapply fld_keep; [exact ST3 | exact (x_icount X2) | unfold O_ICOUNT; lia | unfold O_ICOUNT; cbn; lia | unfold O_ICOUNT, zwin; cbn; intros; lia]
          | eapply fld_keep; [exact ST3 | exact (x_endian X2) | unfold O_ENDIAN; lia | unfold O_ENDIAN; cbn; lia | unfold O_ENDIAN, zwin; cbn; intros; lia]
          | eapply fld_keep; [exact ST3 | exact (x_flags X2) | unfold O_FLAGS; lia | unfold O_FLAGS; cbn; lia | unfold O_FLAGS, zwin; cbn; intros; lia]
          | lia | cbn [set_v2 c_widx c_icount]; lia | cbn [set_v2 c_endian]; lia | cbn [set_v2 c_reqconv]; exact Sc4]. }
      pose proof (loop_mem_frame w M2 M3 LM2 ltac:(lia) ltac:(lia) ltac:(eapply stores_in_agree; [exact ST3 | unfold zwin; intros; lia])) as LM3.
      pose proof (ictx_agree w M2 M3 _ _ _ _ _ IC2 ltac:(lia) ltac:(lia) ltac:(eapply stores_in_agree; [exact ST3 | unfold zwin; cbn; intros; lia])) as IC3.
      pose proof (ifr_agree w M2 M3 IFR2 ltac:(lia) ltac:(lia) ltac:(eapply stores_in_agree; [exact ST3 | unfold zwin; cbn; intros; lia])) as IFR3.
      eapply (HEADK A2 M3 model2 R6 v2); [| exact Hl2 | lia].
      split; [exact X3|]. split; [exact Htr|]. split; [exact BUD2|]. split; [exact OR6|]. split; [exact LM3|]. split; [exact IC3|]. split; [exact IFR3|].
      unfold PmLoopU1.macct in *. cbn [set_v2 set_scal c_icount c_endian c_v3 c_m1 c_m2 c_m3 t3a t3b t3c fst snd] in *.
      destruct MACC as (? & ? & ? & ? & ?). repeat split; try assumption; try lia. }

    pose proof (Z.mod_pos_bound nw 1) as _.
    assert (Hw4 : 4 <= w_words w) by (pose proof (Z.div_mod (w_words w) 4 ltac:(lia)); lia).
    pm_seed R w c [Z_to_bv 64 nw; Z_to_bv 64 (c_endian c); Z_to_bv 64 t; Z_to_bv 64 (i_io I); Z_to_bv 64 (i_op I)].
    seedHR HR E ([(2%bv, EVar 32); (8%bv, EVar 33); (27%bv, EVar 41); (23%bv, EVar 42); (26%bv, EVar 43)] ++ OREGSEED)%list R. seedHK HK w A M model c E X.
    apply (know_more E M [KWord (SA (EVar 32) 718) (N.to_nat 2) (EVar 39);
                          KWord (SA (EVar 33) 88) (N.to_nat 4) (EVar 40); KRange (EVar 39) 0 (2 ^ 16); KRange (EVar 34) 4 (2 ^ 47); KAlign (EVar 34) 4;
                          KRange (EVar 40) 0 1]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil.
         - eapply kword_var; [exact Cnw | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
         - eapply kword_var; [exact Ce | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
         - eapply krange_var; [evs; reflexivity | lia | lia].
         - eapply krange_var; [evs; reflexivity | lia | lia].
         - eapply kalign_var; [evs; reflexivity | lia | lia | exact W2].
         - eapply krange_var; [evs; reflexivity | lia | lia]. }
    destruct (Z.lt_ge_cases (w_n w) (c_widx c + nw)) as [Hov|Hfit].
    {
      xruns HR HK 100%nat (0x677ac :: STOPS) (SCR [true] [] []) 50%N.
      { split_scs; try sc_auto1; cbn [sc_denot]; evs; rewrite ?ext_val_zx2, ?SymExec.alu64_add_lit by lia; rewrite ?br_ltu, ?br_geu, ?br_eq, ?br_ne by lia; bool_lia. }
      postrun. name_run HRn R3.
      rreg HRn (27%bv) G27. rreg HRn (23%bv) G23. rreg HRn (26%bv) G26. assert (OR3 : oregs w R3) by (oregs_seeded HRn Qgp Qtp). clear HRn HR HK.
      eapply (pm_X1 w c0 K fx A M model c R3 (i_io I) (i_op I) t PS FZ X Htr BUD OR3 G23 G26 G27); lia. }
    destruct (Z.eq_dec (c_reqconv c) 0) as [Hrc0|Hrc1].
    {
      rewrite Hrc0 in C92.
      apply (know_more E M [KWord (SA (EVar 33) 92) (N.to_nat 1) (ELit 0)]) in HK.
      2: { repeat apply Forall_cons; try apply Forall_nil. eapply kword_var; [exact C92 | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | cbn [edenot]; reflexivity]. }
      xruns HR HK 100%nat (0x68120 :: STOPS) (SCR [false] [] []) 50%N.
      { split_scs; try sc_auto1; cbn [sc_denot]; evs; rewrite ?ext_val_zx2, ?SymExec.alu64_add_lit by lia; rewrite ?br_ltu, ?br_geu, ?br_eq, ?br_ne by lia; try bool_lia;
        match goal with |- ?G => idtac "SCN"; idtac G end. }
      postrun. name_run HRn R3.
      rreg HRn (24%bv) G24. assert (OR3 : oregs w R3) by (oregs_seeded HRn Qgp Qtp). clear HRn HR HK.
      rewrite ?ext_val_zx2 in G24 by lia. rewrite ?SymExec.alu64_add_lit, ?w_add in G24 by lia.
      eapply (TAIL A M model R3 (c_v2 c)); [rewrite set_v2_self; exact X | rewrite set_v2_self; exact BUD | lia | exact OR3 | exact G24 | exact LM | exact IC | exact IFR | lia]. }
    assert (Hrc : c_reqconv c = 1) by lia. rewrite Hrc in C92.
    destruct (Z.eq_dec nw 0) as [Hnw0|Hnw1].
    {
      subst nw.
      apply (know_more E M [KWord (SA (EVar 33) 92) (N.to_nat 1) (ELit 1); KWord (SA (EVar 32) 718) (N.to_nat 2) (ELit 0)]) in HK.
      2: { repeat apply Forall_cons; try apply Forall_nil.
           - eapply kword_var; [exact C92 | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | cbn [edenot]; reflexivity].
           - eapply kword_var; [exact Cnw | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | cbn [edenot]; reflexivity]. }
      xruns HR HK 100%nat (0x68120 :: 0x68090 :: STOPS) (SCR [false; true; true] [] []) 50%N.
      { split_scs; try sc_auto1; cbn [sc_denot]; evs; rewrite ?ext_val_zx2, ?ext_val_sx4, ?sx32_small, ?SymExec.alu64_add_lit by lia; rewrite ?w_mul, ?w_add by lia;
        rewrite ?br_ltu, ?br_geu, ?br_eq, ?br_ne, ?br_ge by lia; try bool_lia; match goal with |- ?G => idtac "SCZ"; idtac G end. }
      postrun. name_run HRn R3.
      rreg HRn (24%bv) G24. assert (OR3 : oregs w R3) by (oregs_seeded HRn Qgp Qtp). clear HRn HR HK.
      rewrite ?ext_val_zx2 in G24 by lia. rewrite ?SymExec.alu64_add_lit, ?w_add in G24 by lia.
      replace (c_widx c) with (c_widx c + 0) in G24 by lia.
      eapply (TAIL A M model R3 (c_v2 c)); [rewrite set_v2_self; exact X | rewrite set_v2_self; exact BUD | lia | exact OR3 | exact G24 | exact LM | exact IC | exact IFR | lia]. }

    apply (know_more E M [KWord (SA (EVar 33) 92) (N.to_nat 1) (ELit 1); KRange (EVar 39) 1 (2 ^ 16)]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil.
         - eapply kword_var; [exact C92 | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | cbn [edenot]; reflexivity].
         - eapply krange_var; [evs; reflexivity | lia | lia]. }
    xruns HR HK 100%nat (0x68090 :: 0x68120 :: STOPS) (SCR [false; true; true; true] [] []) 50%N.
    { split_scs; try sc_auto1; cbn [sc_denot]; evs; rewrite ?ext_val_zx2, ?ext_val_sx4, ?sx32_small, ?SymExec.alu64_add_lit by lia; rewrite ?w_mul, ?w_add by lia;
      rewrite ?br_ltu, ?br_geu, ?br_eq, ?br_ne, ?br_ge by lia; try bool_lia; match goal with |- ?G => idtac "SCL"; idtac G end. }
    postrun. name_run HRn R3.
    rreg HRn (10%bv) G10. rreg HRn (22%bv) G22. rreg HRn (23%bv) G23. rreg HRn (24%bv) G24.
    assert (OR3 : oregs w R3) by (oregs_seeded HRn Qgp Qtp). clear HRn HR HK.
    rewrite ext_val_zx2 in G24 by lia. rewrite SymExec.alu64_add_lit in G24. rewrite ?ext_val_zx2 in G23 by lia.
    rewrite ?w_mul in G23 by lia. rewrite ?w_add in G23 by lia.
    rewrite ?w_mul in G10 by lia. rewrite ?w_add in G10 by lia.
    replace (w_words w + (4 * c_widx c + 4 * nw)) with (w_words w + 4 * (c_widx c + nw)) in G23 by lia.
    assert (Hk : Z.of_nat (Z.to_nat nw) = nw) by lia.
    eapply (pm_copy_loop (Z.to_nat nw) w c0 K fx I A M model c R3 (w_words w + 4 * c_widx c) (w_words w + 4 * (c_widx c + nw)) (c_widx c + nw) PS FZ X Htr BUD OR3 LM IC IFR G24 G22 He2 G10 G23);
      [rewrite ?Hk; lia | lia | exact Hw | lia | rewrite ?Hk; lia
      | replace (w_words w + 4 * c_widx c) with (w_words w + c_widx c * 4) by lia; rewrite Z_mod_plus_full; exact W2
      | rewrite ?Hk; lia |].
    intros A' M' model' R' b2 cap2 xs2 X' BUD' Hl OR' Q24' LM' IC' IFR'.
    eapply (TAIL A' M' model' R' (b2, xs2, cap2) X' BUD' ltac:(cbn [t3b fst snd]; rewrite Hk in Hl; lia) OR' Q24' LM' IC' IFR'). lia.
  Unshelve. all: try exact SEGS; try exact M.
  Qed.

  Lemma pm_push_tail : forall (w : pmw MI ST) c0 K (fx : FPState) (I : ictxR) A M model c R (t nw : Z),
    PMS w c0 K -> frm_zero (@fp_csr fx) -> ipure I ->
    OBASE w I A M model c R ->
    getr R 27%bv = Z_to_bv 64 t -> getr R 23%bv = Z_to_bv 64 (i_io I) -> getr R 26%bv = Z_to_bv 64 (i_op I) -> 0 <= t < 2 ^ 32 ->
    cellw SEGS M (w_sp w + 718) 2 nw ->
    i_io I + 1 <= c_widx c -> c_widx c < i_io I + i_iwc I ->
    Zlen (t3b (c_v2 c)) <= c_widx c - i_io I ->
    (t3b (c_v1 c) = t3c (c_v1 c) -> 40 * t3c (c_v1 c) + 20 <= 2 ^ 23) ->
    (forall A' M' model' R' (b1 cap1 : Z) (v2 : Z * list Z * Z),
        OBASE w I A' M' model' (set_scal (set_v2 (set_v1 c (b1, t3b (c_v1 c) + 1, cap1)) v2) (c_widx c + nw) (c_icount c) (c_endian c) (c_reqconv c)) R' ->
        Zlen (t3b v2) <= Zlen (t3b (c_v2 c)) + nw -> c_widx c + nw <= w_n w ->
        srealizes SEGS (cfg fx R' 0x677d0 M' model') K) ->
    srealizes SEGS (cfg fx R 0x67f60 M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx I A M model c R t nw PS FZ IP OB Q27 Q23 Q26 Ht Cnw Hw1 Hw2 Hv2 Hgrow HEADK.
    destruct OB as (X & Htr & BUD & OR & LM & IC & IFR & Hic & He2 & Hw & MACC & FR3).
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & [Gc2 Gcal] & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    eapply (pm_push w c0 K fx A M model c R PS X Htr BUD OR LM Hgrow).
    intros A1 M1 model1 R1 b1 cap1 X1 BUD1 OR1 KEPT AG. unfold w_sp0, PM_FRAME in AG.
    keptQ KEPT Q27 Q27b. keptQ KEPT Q23 Q23b. keptQ KEPT Q26 Q26b.
    pose proof (loop_mem_frame w M M1 LM ltac:(lia) ltac:(lia) ltac:(eapply agree_on_weaken; [exact AG | unfold zwin; cbn; intros; lia])) as LM1.
    pose proof (ictx_agree w M M1 _ _ _ _ _ IC ltac:(lia) ltac:(lia) ltac:(eapply agree_on_weaken; [exact AG | unfold zwin; cbn; intros; lia])) as IC1.
    pose proof (ifr_agree w M M1 IFR ltac:(lia) ltac:(lia) ltac:(eapply agree_on_weaken; [exact AG | unfold zwin; cbn; intros; lia])) as IFR1.
    pose proof (cellw_frame M M1 _ _ _ Cnw ltac:(lia) ltac:(cbn; lia) ltac:(eapply agree_on_weaken; [exact AG | unfold zwin; cbn; intros; lia])) as Cnw1.
    set (c1 := set_v1 c (b1, t3b (c_v1 c) + 1, cap1)) in *.
    eapply (pm_push_tail2 w c0 K fx I A1 M1 model1 c1 R1 t nw PS FZ IP X1 Htr BUD1 OR1 LM1 IC1 IFR1);
      cbn [c1 set_v1 c_icount c_endian c_widx c_v2 c_v3 c_reqconv]; try first [exact Hic | exact He2 | exact Hw | exact FR3 | exact Q27b | exact Q23b | exact Q26b | exact Ht | exact Cnw1 | exact Hw1 | exact Hw2 | exact Hv2].
    - unfold PmLoopU1.macct in *. cbn [c1 set_v1 c_icount c_endian c_v3 c_m1 c_m2 c_m3 t3a t3b t3c fst snd] in *. exact MACC.
    - intros A' M' model' R' v2 OB' Hl' Hn'. eapply (HEADK A' M' model' R' b1 cap1 v2); [exact OB' | exact Hl' | exact Hn'].
  Qed.
End PM.
End PmOLoop3U1.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmDispatchU1.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PeLia.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require list.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac WalkTac StartupTac SumWalkTac StoreOk MemSplit Hoare ShapeAlg
  SRealizes RefMemcpyLib RefReadLib FPSteps LibIface LibBudget LibEff MmapSim LibMaskBits
  ZStores SymExec3 SymExec3Sound SymRun3 U1Layout.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContLib StrLib LiveStats ContStmts ContStmts2 U1Facts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts HStmtsU1 HCommonU1 HLib HConstsU1.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsNeeds PrsInv PrsStmts PmBaseU1 PmHyps PmHypsU1 PmCoreU1 PmStepU1. Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep2U1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep2U1.PmUpdU1. From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PmStep2U1 PmLoopU1 PmInstU1 PmStep3U1 PmODefsU1 PmStep4U1 PmZw PmOLoopU1 PmOLoop2U1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmOHeadU1.PmOLoop3U1. From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PmDispatchU1.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PeLia.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Local Ltac lia ::= pe_lia.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Abbreviation SEGS := Ubsan.M.loaded_segments.

Module Ly := U1Layout.

Section PM.
Context {AC : AllocCeiling}.
  Context {MI : MallocIface SEGS Ly.L} {ST : StaticsIface SEGS Ly.L}.
  Context {G : grammar} {idesc : Z -> Z -> Prop} {odesc edesc : Z -> Z -> Z -> Prop}
          {generates_type is_ext_inst is_nonsemantic : Z -> bool}
          {ds_rep : AS MI -> mem -> Z -> Z -> Z -> list (Z * Z) -> Prop}.
  Variable CL : pm_calleesU1 SEGS Ly.L MI ST G tcU1 dcU1 nfcU1 HConstsU1.hc ccU1 kcU1
                  idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep.

  #[local] Notation PMX := (PmBaseU1.PMX MI ST).
  #[local] Notation cfg fx R pc M model := (mkCfg (@mkst fx R (Z_to_bv 64 pc) M (seg_rom SEGS)) model).
  #[local] Notation DL := (cu_ds_laws _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
  #[local] Notation pm_exit := (PmCoreU1.pm_exit MI ST).
  #[local] Notation pmx_ds_room := (PmStepU1.pmx_ds_room CL).
  #[local] Notation pm_tail_6733c := (PmStepU1.pm_tail_6733c CL).
  #[local] Notation cregs_kept := (PmStepU1.cregs_kept CL).
  #[local] Notation pm_put_cstr := (PmStepU1.pm_put_cstr CL).
  #[local] Notation pm_put_chars := (PmStepU1.pm_put_chars CL).
  #[local] Notation pm_put_num := (PmStepU1.pm_put_num CL).
  #[local] Notation pm_put_u16 := (PmStepU1.pm_put_u16 CL).
  #[local] Notation pm_put_u32 := (PmStepU1.pm_put_u32 CL).
  #[local] Notation pm_put_u64 := (PmStepU1.pm_put_u64 CL).
  #[local] Notation pm_put_int := (PmStepU1.pm_put_int CL).
  #[local] Notation pm_pdiagQ := (PmStepU1.pm_pdiagQ CL).
  #[local] Notation pm_dtor := (PmStepU1.pm_dtor CL).
  #[local] Notation pm_exhausted := (PmStepU1.pm_exhausted CL).
  #[local] Notation pm_fixword := (PmStepU1.pm_fixword CL).
  #[local] Notation pm_is_host_endian := (PmStepU1.pm_is_host_endian CL).
  #[local] Notation pm_binend := (PmStepU1.pm_binend CL).
  #[local] Notation pm_ecw_pbs := (PmStep2U1.pm_ecw_pbs CL).
  #[local] Notation pm_ecw_pbs1 := (PmStep2U1.pm_ecw_pbs1 CL).
  #[local] Notation pm_ecw_pbs2 := (PmStep2U1.pm_ecw_pbs2 CL).
  #[local] Notation pmx_upd_foot := (PmStep2U1.pmx_upd_foot).
  #[local] Notation pm_v2_push_fast := (PmStep2U1.pm_v2_push_fast).
  #[local] Notation pm_opcode_split := (PmStep2U1.pm_opcode_split CL).
  #[local] Notation pm_lookup_opcode := (PmStep2U1.pm_lookup_opcode CL).
  #[local] Notation pm_lookup_operand := (PmStep2U1.pm_lookup_operand CL).
  #[local] Notation pm_lookup_ext := (PmStep2U1.pm_lookup_ext CL).
  #[local] Notation pm_idesc_operands := (PmStep3U1.pm_idesc_operands CL).
  #[local] Notation pm_odesc_operands := (PmStep3U1.pm_odesc_operands CL).
  #[local] Notation pm_edesc_operands := (PmStep3U1.pm_edesc_operands CL).
  #[local] Notation pm_push_types := (PmStep3U1.pm_push_types CL).
  #[local] Notation pm_take_first := (PmStep3U1.pm_take_first CL).

  #[local] Notation izero := (PmInstU1.izero).
  #[local] Notation ictx := (PmInstU1.ictx).
  #[local] Notation nodes := (PmLoopU1.nodes).
  #[local] Notation macct := (PmLoopU1.macct).
  #[local] Notation ipure := (PmODefsU1.ipure (G:=G) (idesc:=idesc)).
  #[local] Notation arm_stmt := (PmODefsU1.arm_stmt (MI:=MI) (ST:=ST) (G:=G) (idesc:=idesc)).
  #[local] Notation pm_check_err := (@PmOLoopU1.pm_check_err AC MI ST).
  #[local] Notation pm_X1 := (PmOLoopU1.pm_X1 CL).
  #[local] Notation pm_push := (PmOLoopU1.pm_push CL).
  #[local] Notation PREGS := (PmOLoopU1.PREGS).
  #[local] Notation pm_copy_loop := (PmOLoop2U1.pm_copy_loop CL).
  #[local] Notation pm_push_tail := (PmOLoop3U1.pm_push_tail CL).
  #[local] Notation pm_dispatch := (PmDispatchU1.pm_dispatch).
  #[local] Notation arm_pc := (PmDispatchU1.arm_pc).
  #[local] Notation OLI := (PmODefsU1.OLI (MI:=MI) (ST:=ST) (generates_type:=generates_type)).
  #[local] Notation iacc := (PmODefsU1.iacc (generates_type:=generates_type)).
  Ltac show_goal_dbg := match goal with |- ?g => idtac "SC:" g end.

  Ltac oregs_seeded HRn Qgp Qtp :=
    let G2 := fresh in let G3 := fresh in let G4 := fresh in let G8 := fresh in let G9 := fresh in
    let G18 := fresh in let G19 := fresh in let G20 := fresh in let G21 := fresh in let G25 := fresh in
    rreg HRn 2%bv G2; rreg HRn 3%bv G3; rreg HRn 4%bv G4; rreg HRn 8%bv G8; rreg HRn 9%bv G9;
    rreg HRn 18%bv G18; rreg HRn 19%bv G19; rreg HRn 20%bv G20; rreg HRn 21%bv G21; rreg HRn 25%bv G25;
    unfold oregs, loop_regs; rewrite G2, G3, G4, G8, G9, G18, G19, G20, G21, G25; fixregs; rewrite ?Qgp, ?Qtp;
    rewrite ?SymExec.alu64_add_lit; repeat split; reflexivity.
  #[local] Notation OREGSEED := [(9%bv, EAlu ALU_ADD (EVar 33) (ELit 88)); (18%bv, ELit 1); (19%bv, ELit (2 ^ 61)); (20%bv, ELit 20); (21%bv, EAlu ALU_ADD (EVar 33) (ELit 264)); (25%bv, ELit 5)]%list.

  Ltac hseed R w c A M model X Cwi Cio Ciwc V3f0 V3f1 io iwc b3 xs0 :=
    let E := fresh "E" in let HR := fresh "HR" in let HK := fresh "HK" in
    pm_seed R w c [Z_to_bv 64 io; Z_to_bv 64 iwc; Z_to_bv 64 b3; Z_to_bv 64 (b3 + 4 * Zlen xs0)];
    seedHR HR E ([(2%bv, EVar 32); (8%bv, EVar 33)] ++ OREGSEED)%list R; seedHK HK w A M model c E X;
    apply (know_more E M [KWord (SA (EVar 33) 72) (N.to_nat 8) (EVar 38); KWord (SA (EVar 32) 216) (N.to_nat 8) (EVar 39); KWord (SA (EVar 32) 234) (N.to_nat 2) (EVar 40);
                            KWord (SA (EVar 33) 264) (N.to_nat 8) (EVar 41); KWord (SA (EVar 33) 272) (N.to_nat 8) (EVar 42)]) in HK;
    [ | repeat apply Forall_cons; try apply Forall_nil;
        [ eapply kword_var; [exact Cwi | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity]
        | eapply kword_var; [exact Cio | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity]
        | eapply kword_var; [exact Ciwc | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity]
        | eapply kword_var; [eapply fld_cellw; [exact V3f0 | cbn; lia] | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity]
        | eapply kword_var; [eapply fld_cellw; [replace (w_p w + 272) with (w_p w + 264 + 8) by lia; exact V3f1 | cbn; lia] | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity] ] ].

  Lemma w_mul_lit : forall a b, mul_div M_MUL (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a * b).
  Proof using.
    intros a b. apply bv_eq. cbn [mul_div].
    rewrite bv_mul_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite <- Zmult_mod. reflexivity.
  Qed.
  Lemma kword_expr : forall E M (base : expr) (b off : Z) (w : N) (v : Z) (e : expr),
    cellw SEGS M (b + off) w v -> (w <= 8)%N ->
    edenot E base = Z_to_bv 64 b -> 0 <= b < 2 ^ 64 -> 0 <= b + off < 2 ^ 64 -> b + off + Z.of_N w <= 2 ^ 64 ->
    edenot E e = Z_to_bv 64 v ->
    kentry_ok SEGS E M (KWord (SA base off) (N.to_nat w) e).
  Proof using.
    intros E M base b off w v e [Hv Hr] Hw Hn Hb Hbo Hbow He. cbn [kentry_ok]. rewrite !N_nat_Z.
    split; [lia|]. split.
    - unfold flat, estart. cbn [a_base a_off]. rewrite Hn, u64_of_Z by lia. lia.
    - unfold adenot. cbn [a_base a_off]. rewrite Hn, He, v_addi_Z by lia. exact Hr.
  Qed.
  Lemma kdisj_expr : forall E M (e1 e2 : expr) (b1 b2 o1 o2 l1 l2 : Z),
    edenot E e1 = Z_to_bv 64 b1 -> edenot E e2 = Z_to_bv 64 b2 -> 0 <= b1 < 2 ^ 64 -> 0 <= b2 < 2 ^ 64 ->
    0 <= l1 < 2 ^ 64 -> 0 <= l2 < 2 ^ 64 ->
    (b1 + o1 + l1 <= b2 + o2 \/ b2 + o2 + l2 <= b1 + o1) ->
    kentry_ok SEGS E M (KDisj (SA e1 o1) (ELit l1) (SA e2 o2) (ELit l2)).
  Proof using.
    intros E M e1 e2 b1 b2 o1 o2 l1 l2 H1 H2 Hb1 Hb2 Hl1 Hl2 H. cbn [kentry_ok].
    unfold estart, elenZ. cbn [a_base a_off]. rewrite H1, H2. cbn [edenot]. rewrite !u64_of_Z by lia. exact H.
  Qed.

  Lemma pm_ohead_tf : forall (w : pmw MI ST) c0 K (fx : FPState) (I : ictxR) A M model c R1 (b3 cap3 : Z) (xs0 : list Z),
    PMS w c0 K -> frm_zero (@fp_csr fx) -> fconsts fx -> ipure I ->
    (forall t, arm_stmt t (arm_pc t)) ->
    (forall (fx' : FPState) A' M' model' c' R', frm_zero (@fp_csr fx') -> fconsts fx' -> OLI w I A' M' model' c' R' -> omeas I c' < omeas I c ->
        srealizes SEGS (cfg fx' R' 0x677d0 M' model') K) ->
    PMX w A M model c -> c_tr c = [] -> pm_bud (w_n w) c -> loop_mem w M ->
    ictx w M (i_io I) (i_fw I) (i_iwc I) (i_op I) (i_d I) -> ifr w M ->
    c_icount c + 4 <= i_io I -> c_endian c < 2 -> w_words w <> 0 -> PmLoopU1.macct c -> Forall (fun t => 0 <= t < 2 ^ 31) xs0 ->
    c_v3 c = (b3, xs0, cap3) ->
    i_io I + 1 <= c_widx c -> PmLoopU1.nodes c + 2 <= c_widx c + 3 ->
    t3b (c_v1 c) + (3 * Z.max 0 (i_io I + i_iwc I - c_widx c) + zw_next xs0) <= 3 * 2 ^ 16 + 1 ->
    Zlen (t3b (c_v2 c)) <= c_widx c - i_io I ->
    Zlen xs0 + zw_next xs0 <= 127 * (c_widx c - i_io I) + 1 -> zw_stack_ok xs0 ->
    nty (i_op I) xs0 (c_widx c - i_io I) -> iacc I c ->
    c_widx c < i_io I + i_iwc I -> xs0 <> [] -> 1 <= Zlen xs0 ->
    oregs w R1 -> getr R1 10%bv = Z_to_bv 64 (w_p w + 264) -> getr R1 1%bv = Z_to_bv 64 0x677f8 ->
    srealizes SEGS (cfg fx R1 (tc_take_first tcU1) M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx I A M model c R1 b3 cap3 xs0 PS FZ FC IP ARMS HEADK X Htr BUD LM IC IFR Hic He2 Hw MACC FR3 Ev3 Hw1 ACC CNT V2L V3L ZW HTY IACC Hlt Hne Hl1 OR1 G10 G1.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & [Gc2 Gcal] & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof (x_scal X) as (Sc1 & Sc2 & Sc3 & Sc4). pose proof (ipure_ranges I IP) as (Riwc & Rop).
    pose proof IP as IP'. destruct IP' as (Eiwc & Eop & Hnz & Rfw & Hg & Hdesc & Rio).
    pose proof OR1 as OR'. destruct OR' as (G2 & G3 & G4 & G8 & Qs1 & Qs2 & Qs3 & Qs4 & Qs5 & Qs9).
    pose proof (Zlen_nonneg xs0) as Hl0. pose proof (zw_next_range xs0) as Hzr.
    eapply (pm_take_first w c0 K fx A M model c R1 _ PS X Htr BUD ltac:(cregs_tac G1 G2 G3 G4));
      [unfold O_V3; exact G10 | rewrite Ev3; exact Hne | rewrite Ev3; exact FR3 | rewrite Ev3; cbn [t3b fst snd]; unfold V3MAX; lia |].
    rewrite Ev3. cbn [t3b fst snd].
    intros A1 R2 M1 model1 b3' cap3' X1 BUD1 KEPT Ht0 AG.
    pose proof (oregs_kept w R1 R2 OR1 KEPT) as OR2.
    keptQ KEPT G2 Qsp2. keptQ KEPT G8 Qs02. keptQ KEPT G3 Qgp2. keptQ KEPT G4 Qtp2. clear G1 G2 G3 G4 G8 G10 KEPT OR1.
    eapply (loop_mem_frame w M M1) in LM; [| lia | lia | eapply agree_on_weaken; [exact AG | unfold zwin, w_sp0, PM_FRAME; intros; lia]].
    eapply (ictx_agree w M M1) in IC; [| lia | lia | eapply agree_on_weaken; [exact AG | unfold zwin, w_sp0, PM_FRAME; cbn; intros; lia]].
    eapply (ifr_agree w M M1) in IFR; [| lia | lia | eapply agree_on_weaken; [exact AG | unfold zwin, w_sp0, PM_FRAME; cbn; intros; lia]].
    clear AG X MS. pose proof (x_ms X1) as MS1.
    set (t := fst (take_first xs0)) in *. set (xs1 := snd (take_first xs0)) in *.
    set (c1 := set_v3 c (b3', xs1, cap3')) in *.
    pose proof (take_first_range xs0 FR3) as [Rt FR1]. pose proof (take_first_len xs0 Hne) as [Hlen1 Hlen1'].
    change (fst (take_first xs0)) with t in Rt. change (snd (take_first xs0)) with xs1 in FR1, Hlen1, Hlen1'.
    pose proof IC as IC'. destruct IC' as (Cio & Cfw & Ciwc & Cop & Fd).
    pose proof (fld_cellw M1 _ 8 _ (x_widx X1) ltac:(cbn [c1 set_v3 c_widx]; lia)) as Cwi. unfold O_WIDX in Cwi. cbn [c1 set_v3 c_widx] in Cwi.
    pose proof (fld_cellw M1 _ 8 _ (x_n X1) ltac:(cbn; lia)) as Cn. unfold O_N in Cn.
    destruct (Gw Hw) as (W1 & W2 & W3 & W4 & W5). assert (Hw4 : 4 <= w_words w) by (pose proof (Z.div_mod (w_words w) 4 ltac:(lia)); lia).
    pose proof OR2 as OR'. destruct OR' as (_ & _ & _ & _ & Ps1 & Ps2 & Ps3 & Ps4 & Ps5 & Ps9).

    destruct (Z.lt_ge_cases (c_widx c) (w_n w)) as [Hwn|Hwn].
    2: { pm_seed R2 w c1 [Z_to_bv 64 t; Z_to_bv 64 (i_io I); Z_to_bv 64 (i_op I)].
         seedHR HR E ([(2%bv, EVar 32); (8%bv, EVar 33); (10%bv, EVar 39)] ++ OREGSEED)%list R2. seedHK HK w A1 M1 model1 c1 E X1.
         apply (know_more E M1 [KWord (SA (EVar 32) 216) (N.to_nat 8) (EVar 40); KWord (SA (EVar 33) 72) (N.to_nat 8) (EVar 38); KWord (SA (EVar 33) 56) (N.to_nat 8) (EVar 35);
                                 KWord (SA (EVar 32) 250) (N.to_nat 2) (EVar 41); KRange (EVar 39) 0 (2 ^ 31 - 1)]) in HK.
         2: { repeat apply Forall_cons; try apply Forall_nil.
              - eapply kword_var; [exact Cio | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
              - eapply kword_var; [exact Cwi | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
              - eapply kword_var; [exact Cn | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
              - eapply kword_var; [exact Cop | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
              - eapply krange_var; [evs; reflexivity | lia | lia]. }
         xruns HR HK 100%nat (0x677ac :: STOPS) (SCR [true] [] []) 50%N.
         { split_scs; try sc_auto1. all: cbn [sc_denot]; evs; cbn [c1 set_v3 c_widx]; rewrite ?ext_val_zx2, ?w_add by lia; rewrite ?br_geu, ?br_ltu, ?br_eq, ?br_ne, ?br_ge by lia; try bool_lia. all: show_goal_dbg. }
         postrun. name_run HRn R3.
         rreg HRn (27%bv) G27. rreg HRn (23%bv) G23. rreg HRn (26%bv) G26.
         assert (OR3 : oregs w R3) by (oregs_seeded HRn Qgp2 Qtp2). clear HRn HR HK.
         rewrite ?ext_val_zx2 in G26 by lia.
         lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ => set (M2 := m) in * end.
         assert (ST2 : stores_in (zwin (w_sp w + 716) (w_sp w + 736)) M1 M2) by (unfold M2; stin).
         assert (X2 : PMX w A1 M2 model1 c1).
         { eapply (pmx_frame_stores SEGS Ly.L MI ST ly_img_low ly_rw_img ly_relro_img w A1 M1 M2 model1 c1 (zwin (w_sp w + 716) (w_sp w + 736)));
             [exact X1 | exact ST2 | unfold zwin, w_sp0, PM_FRAME; intros; lia]. }
         eapply (pm_X1 w c0 K fx A1 M2 model1 c1 R3 (i_io I) (i_op I) t PS FZ X2 Htr BUD1 OR3 G23 G26 G27); lia. }
    pose proof (mdef_cell4 M1 (w_words w + 4 * c_widx c) ltac:(eapply mdef_sub; [exact (x_wbuf X1 Hw) | lia | lia]) ltac:(lia) ltac:(lia)) as (raw & Craw).
    pose proof (proj1 Craw) as Rraw. cbn in Rraw.
    pose proof (fld_cellw M1 _ 4 _ (x_endian X1) ltac:(cbn [c1 set_v3 c_endian]; lia)) as Ce. unfold O_ENDIAN in Ce. cbn [c1 set_v3 c_endian] in Ce.
    pm_seed R2 w c1 [Z_to_bv 64 t; Z_to_bv 64 (i_io I); Z_to_bv 64 (i_op I); Z_to_bv 64 (c_endian c); Z_to_bv 64 raw].
    seedHR HR E ([(2%bv, EVar 32); (8%bv, EVar 33); (10%bv, EVar 39)] ++ OREGSEED)%list R2. seedHK HK w A1 M1 model1 c1 E X1.
    assert (AW : edenot E PmInstU1.WIX = Z_to_bv 64 (w_words w + 4 * c_widx c)) by (apply PmInstU1.wix_val; [evs; reflexivity | evs; reflexivity | lia | lia | lia]).
    apply (know_more E M1 [KWord (SA (EVar 32) 216) (N.to_nat 8) (EVar 40); KWord (SA (EVar 33) 72) (N.to_nat 8) (EVar 38); KWord (SA (EVar 33) 56) (N.to_nat 8) (EVar 35);
                            KWord (SA (EVar 32) 250) (N.to_nat 2) (EVar 41); KWord (SA (EVar 33) 48) (N.to_nat 8) (EVar 34); KWord (SA (EVar 33) 88) (N.to_nat 4) (EVar 42);
                            KWord (SA PmInstU1.WIX 0) (N.to_nat 4) (EVar 43);
                            KDisj (SA PmInstU1.WIX 0) (ELit 4) (SA (EVar 32) 0) (ELit 864); KDisj (SA PmInstU1.WIX 0) (ELit 4) (SA (EVar 33) 0) (ELit 288);
                            KRange (EVar 39) 0 (2 ^ 31 - 1); KRange (EVar 34) 4 (2 ^ 47); KAlign (EVar 34) 4; KRange (EVar 42) 0 1]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil.
         - eapply kword_var; [exact Cio | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
         - eapply kword_var; [exact Cwi | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
         - eapply kword_var; [exact Cn | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
         - eapply kword_var; [exact Cop | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
         - eapply kword_var; [eapply fld_cellw; [exact (x_words X1) | lia] | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
         - eapply kword_var; [exact Ce | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
         - eapply kword_expr; [rewrite Z.add_0_r; exact Craw | cbn; lia | exact AW | lia | lia | cbn; lia | evs; reflexivity].
         - eapply kdisj_expr; [exact AW | evs; reflexivity | lia | lia | lia | lia |].
           destruct (W5 (w_words w + 4 * c_widx c) ltac:(unfold zwin; lia)) as [Hnw _].
           destruct (W5 (w_words w + 4 * c_widx c + 3) ltac:(unfold zwin; lia)) as [Hnw' _]. unfold zwin in Hnw, Hnw'. lia.
         - eapply kdisj_expr; [exact AW | evs; reflexivity | lia | lia | lia | lia |].
           destruct (W5 (w_words w + 4 * c_widx c) ltac:(unfold zwin; lia)) as [_ Hnp].
           destruct (W5 (w_words w + 4 * c_widx c + 3) ltac:(unfold zwin; lia)) as [_ Hnp']. lia.
         - eapply krange_var; [evs; reflexivity | lia | lia].
         - eapply krange_var; [evs; reflexivity | lia | lia].
         - eapply kalign_var; [evs; reflexivity | lia | lia | exact W2].
         - eapply krange_var; [evs; reflexivity | lia | lia]. }
    xruns HR HK 100%nat STOPS (SCR [false; true] [] []) 50%N.
    { split_scs; try sc_auto1. all: cbn [sc_denot]; evs; cbn [c1 set_v3 c_widx]; rewrite ?ext_val_zx2, ?w_add by lia; rewrite ?w_mul, ?w_add by lia; rewrite ?br_geu, ?br_ltu, ?br_eq, ?br_ne, ?br_ge by lia; try bool_lia.
      all: try (eapply sc_flat; [exact AW | lia | cbn [a_off]; lia | lia | cbn [a_off]; lia]). all: show_goal_dbg. }
    postrun. name_run HRn R3.
    rreg HRn (1%bv) G1. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11.
    rreg HRn (27%bv) G27. rreg HRn (24%bv) G24. rreg HRn (23%bv) G23. rreg HRn (26%bv) G26.
    assert (OR3 : oregs w R3) by (oregs_seeded HRn Qgp2 Qtp2).
    pose proof OR3 as OR'. destruct OR' as (G2 & G3 & G4 & G8 & _). clear HRn HR HK.
    rewrite ext_val_sx4 in G10 by lia. rewrite ?ext_val_sx4, ?sx32_small in G11 by lia. rewrite ext_val_zx2 in G26 by lia.
    rewrite w_mul_lit, SymExec.alu64_add_lit in G24. rewrite w_mul_lit, SymExec.alu64_add_lit. cbn [c1 set_v3 c_widx] in G24 |- *.
    replace (c_widx c + -1 * i_io I) with (c_widx c - i_io I) in G24 |- * by lia.
    lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ => set (M2 := m) in * end.
    assert (ST2 : stores_in (zwin (w_sp w + 716) (w_sp w + 736)) M1 M2) by (unfold M2; stin).
    assert (X2 : PMX w A1 M2 model1 c1).
    { eapply (pmx_frame_stores SEGS Ly.L MI ST ly_img_low ly_rw_img ly_relro_img w A1 M1 M2 model1 c1 (zwin (w_sp w + 716) (w_sp w + 736)));
        [exact X1 | exact ST2 | unfold zwin, w_sp0, PM_FRAME; intros; lia]. }
    eapply (loop_mem_frame w M1 M2) in LM; [| lia | lia | eapply stores_in_agree; [exact ST2 | unfold zwin; intros; lia]].
    eapply (ictx_agree w M1 M2) in IC; [| lia | lia | eapply stores_in_agree; [exact ST2 | unfold zwin; intros; lia]].
    eapply (ifr_agree w M1 M2) in IFR; [| lia | lia | eapply stores_in_agree; [exact ST2 | unfold zwin; intros; lia]].
    assert (PO : popnd w M2 (c_widx c - i_io I) t).
    { unfold popnd, M2. repeat match goal with |- _ /\ _ => split end; (split; [cbn; lia | rdback]). }
    assert (He32 : 0 <= c_endian c < 2 ^ 32) by lia.
    clear ST2 MS1 Craw Cwi Cn Ce Cio Cfw Ciwc Cop Fd. clearbody M2. clear X1 M1. pose proof (x_ms X2) as MS2.

    eapply (pm_fixword w A1 M2 model1 c1 fx R3 _ K X2 (ex_intro _ raw (ex_intro _ (c_endian c) (conj Rraw (conj G10 (conj He32 G11))))) G1 ltac:(apply bv_eq; vm_compute; reflexivity)).
    intros R4 KEPT (r & Rr & Hr). rewrite TablStmts.sx32_prs in Hr.
    pose proof (oregs_kept w R3 R4 OR3 KEPT) as OR4.
    keptQ KEPT G27 Q27d. keptQ KEPT G24 Q24d. keptQ KEPT G23 Q23d. keptQ KEPT G26 Q26d. clear G1 G2 G3 G4 G8 G10 G11 G27 G24 G23 G26 KEPT OR3 OR2.

    eapply (pm_dispatch w A1 M2 model1 c1 fx R4 t r K X2 OR4 Hr Rr Q27d ltac:(lia)).
    intros R5 OR5 Q22 Q27 Q23 Q24 Q26. rewrite Q23d in Q23. rewrite Q24d in Q24. rewrite Q26d in Q26.
    assert (ST3 : stores_in (zwin (w_sp w + 712) (w_sp w + 716)) M2 (wbytes M2 (Z_to_bv 64 (w_sp w + 712)) (word_to_le_bytes 4 (Z_to_bv 64 r)))) by stin.
    assert (X3 : PMX w A1 (wbytes M2 (Z_to_bv 64 (w_sp w + 712)) (word_to_le_bytes 4 (Z_to_bv 64 r))) model1 c1).
    { eapply (pmx_frame_stores SEGS Ly.L MI ST ly_img_low ly_rw_img ly_relro_img w A1 M2 _ model1 c1 (zwin (w_sp w + 712) (w_sp w + 716)));
        [exact X2 | exact ST3 | unfold zwin, w_sp0, PM_FRAME; intros; lia]. }
    eapply (loop_mem_frame w M2) in LM; [| lia | lia | eapply stores_in_agree; [exact ST3 | unfold zwin; intros; lia]].
    eapply (ictx_agree w M2) in IC; [| lia | lia | eapply stores_in_agree; [exact ST3 | unfold zwin; intros; lia]].
    eapply (ifr_agree w M2) in IFR; [| lia | lia | eapply stores_in_agree; [exact ST3 | unfold zwin; intros; lia]].
    eapply (popnd_agree w M2) in PO; [| lia | lia | eapply stores_in_agree; [exact ST3 | unfold zwin; intros; lia]].
    assert (Cw : cellw SEGS (wbytes M2 (Z_to_bv 64 (w_sp w + 712)) (word_to_le_bytes 4 (Z_to_bv 64 r))) (w_sp w + 712) 4 r) by (split; [cbn; lia | rdback]).

    eapply (ARMS t w c0 K fx I A1 _ model1 c1 R5 r PS FZ FC IP).
    -
      split. { split; [exact X3|]. split; [exact Htr|]. split; [exact BUD1|]. split; [exact OR5|]. split; [exact LM|]. split; [exact IC|]. split; [exact IFR|].
               cbn [c1 set_v3 c_icount c_endian c_v3 t3b fst snd]. repeat (split; [first [assumption | lia] |]). exact FR1. }
      unfold PmLoopU1.nodes in *. cbn [c1 set_v3 c_widx c_v1 c_v2 c_v3 c_m1 c_m2 c_m3 t3a t3b t3c fst snd] in *.
      split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact Rt|]. split; [exact Rr|].
      split; [exact Q22|]. split; [exact Q27|]. split; [exact Q24|]. split; [exact Q23|]. split; [exact Q26|]. split; [exact PO | exact Cw].
    -
      intros fx6 FZ6 FC6 A6 M6 model6 c6 R6 nw l' OB6 U27 U23 U26 Cnw Hnw Ew6 Ev16 Ev26 Hn6 Exs6 Hsf Hl' Hlits Em2 Hm1 Hm3 Hnrid.
      assert (Htf : take_first xs0 = (t, xs1)) by (subst t xs1; destruct (take_first xs0); reflexivity).
      pose proof OB6 as OB6'. destruct OB6' as (X6 & Htr6 & BUD6 & OR6 & LM6 & IC6 & IFR6 & Hic6 & He6 & _ & MACC6 & FR6).
      eapply (pm_push_tail w c0 K fx6 I A6 M6 model6 c6 R6 t nw PS FZ6 IP OB6 U27 U23 U26 ltac:(lia) Cnw);
        [rewrite Ew6; cbn [c1 set_v3 c_widx]; lia | rewrite Ew6; cbn [c1 set_v3 c_widx]; lia | rewrite Ev26, Ew6; cbn [c1 set_v3 c_v2 c_widx]; lia
        | rewrite Ev16; cbn [c1 set_v3 c_v1 t3b t3c fst snd]; intros Hfull; lia |].
      intros A7 M7 model7 R7 b1 cap1 v2 OB7 Hl7 Hn7.
      pose proof (zw_next_range (xs1 ++ l')) as Hzr1. pose proof (zw_next_range xs1) as Hzr2.
      pose proof (Zlen_nonneg l') as Hl'0.

      assert (HM : 3 * Z.max 0 (i_io I + i_iwc I - (c_widx c + nw)) + zw_next (xs1 ++ l') + 1
                   <= 3 * Z.max 0 (i_io I + i_iwc I - c_widx c) + zw_next xs0
              /\ Zlen xs1 + Zlen l' + zw_next (xs1 ++ l') <= 127 * (c_widx c + nw - i_io I) + 1).
      { destruct Hnw as [Hnw1|(Hnw0 & Hzt & ->)].
        - split; lia.
        - rewrite app_nil_r in *. subst nw. destruct (zw_take_zero xs0 ZW Hne Hzt) as [Z1 Z0].
          change (zw_next (snd (take_first xs0))) with (zw_next xs1) in Z0. rewrite Z0, Z1 in *. change (Zlen (@nil Z)) with 0. lia. }
      destruct HM as [HM1 HM2].
      rewrite Ew6 in *. cbn [c1 set_v3 c_widx] in Hn7, HM1, HM2 |- *.
      eapply HEADK; [exact FZ6 | exact FC6 | |].
      +
        split; [exact OB7|]. unfold omeas, PmLoopU1.nodes in *.
        cbn [set_scal PmBaseU1.set_scal set_v1 set_v2 c_widx c_icount c_endian c_reqconv c_v1 c_v2 c_v3 c_m1 c_m2 c_m3 t3a t3b t3c fst snd] in *.
        rewrite ?Ew6, ?Ev16, ?Ev26, ?Exs6 in *. cbn [c1 set_v3 c_widx c_v1 c_v2 c_v3 c_m1 c_m2 c_m3 t3a t3b t3c fst snd] in *.
        split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [rewrite ?Zlen_app; lia|].
        split; [exact (zw_take_push xs0 l' ZW Hne Hsf)|].
        split. { replace (c_widx c + nw - i_io I) with (c_widx c - i_io I + nw) by lia. exact (nty_step (i_op I) xs0 l' nw (c_widx c - i_io I) Hne HTY Hnw ltac:(destruct Hlits as [Hlq|(Nq1 & Nq2 & _)]; [left; exact Hlq | right; split; [exact Nq1 | exact Nq2]])). }
        lazymatch goal with |- PmODefsU1.iacc _ ?cc =>
          apply (iacc_step I c cc t xs1 l' nw IACC ltac:(rewrite Ev3; exact Hne) Hw1 ltac:(rewrite Ev3; exact Htf));
          cbn [set_scal PmBaseU1.set_scal set_v1 set_v2 c_v3 c_widx c_m1 c_m2 c_m3 t3b t3c fst snd];
          first [exact Exs6 | reflexivity | exact Hnw | exact Hlits | exact Em2 | exact Hm1 | exact Hm3 | exact Hnrid | idtac "IACC-LEFT"]
        end.
        all: show_goal_dbg.
      +
        unfold omeas. cbn [set_scal PmBaseU1.set_scal set_v1 set_v2 c_widx c_v3 t3b fst snd]. rewrite ?Ew6, ?Exs6.
        cbn [c1 set_v3 c_widx c_v3 t3b fst snd]. rewrite Ev3. cbn [t3b fst snd]. lia.
    -   intros fx6 FZ6 FC6. exact (pm_check_err w c0 K fx6 PS FZ6).
    -   apply (iacc_aacc I c c1 t xs1 IACC ltac:(rewrite Ev3; exact Hne) ltac:(rewrite Ev3; cbn [t3b fst snd]; subst t xs1; destruct (take_first xs0); reflexivity));
        cbn [c1 set_v3 c_m1 c_m3 c_widx]; reflexivity.
  Unshelve. all: first [exact SEGS | exact M].
  Qed.

  Lemma pm_ohead : forall (w : pmw MI ST) c0 K (fx : FPState) (I : ictxR) A M model c R,
    PMS w c0 K -> frm_zero (@fp_csr fx) -> fconsts fx -> ipure I -> OLI w I A M model c R ->
    (forall t, arm_stmt t (arm_pc t)) ->
    (forall (fx' : FPState) A' M' model' c' R', frm_zero (@fp_csr fx') -> fconsts fx' -> OLI w I A' M' model' c' R' -> omeas I c' < omeas I c ->
        srealizes SEGS (cfg fx' R' 0x677d0 M' model') K) ->
    (forall R', oregs w R' -> i_io I + i_iwc I <= c_widx c ->
        getr R' 22%bv = Z_to_bv 64 (c_widx c) -> getr R' 23%bv = Z_to_bv 64 (i_io I) -> getr R' 10%bv = Z_to_bv 64 (i_iwc I) ->
        getr R' 11%bv = Z_to_bv 64 (i_io I + i_iwc I) -> getr R' 13%bv = Z_to_bv 64 (t3a (c_v3 c)) ->
        getr R' 12%bv = Z_to_bv 64 (t3a (c_v3 c) + 4 * Zlen (t3b (c_v3 c))) ->
        srealizes SEGS (cfg fx R' 0x68560 M model) K) ->
    (forall R', oregs w R' -> c_widx c < i_io I + i_iwc I -> t3b (c_v3 c) = [] ->
        getr R' 22%bv = Z_to_bv 64 (c_widx c) -> getr R' 23%bv = Z_to_bv 64 (i_io I) -> getr R' 10%bv = Z_to_bv 64 (i_iwc I) ->
        srealizes SEGS (cfg fx R' 0x685b4 M model) K) ->
    srealizes SEGS (cfg fx R 0x677d0 M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx I A M model c R PS FZ FC IP HOLI ARMS HEADK EXITK D7K.
    destruct HOLI as (OB & Hw1 & ACC & CNT & V2L & V3L & ZW & HTY & IACC). unfold omeas in CNT.
    pose proof OB as OB'. destruct OB' as (X & Htr & BUD & OR & LM & IC & IFR & Hic & He2 & Hw & MACC & FR3).
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & [Gc2 Gcal] & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof (x_scal X) as (Sc1 & Sc2 & Sc3 & Sc4). pose proof (ipure_ranges I IP) as (Riwc & Rop).
    pose proof IP as IP'. destruct IP' as (Eiwc & Eop & Hnz & Rfw & Hg & Hdesc & Rio).
    pose proof OR as OR'. destruct OR' as (Qsp & Qgp & Qtp & Qs0 & Qs1 & Qs2 & Qs3 & Qs4 & Qs5 & Qs9).
    pose proof IC as IC'. destruct IC' as (Cio & Cfw & Ciwc & Cop & Fd).
    pose proof (x_v3 X) as V3. destruct (c_v3 c) as [[b3 xs0] cap3] eqn:Ev3. cbn [t3a t3b t3c fst snd] in *.
    destruct V3 as (_ & _ & _ & V3len & V3blk & V3f0 & V3f1 & _). unfold O_V3 in V3f0, V3f1.
    pose proof (fld_cellw M _ 8 _ (x_widx X) ltac:(lia)) as Cwi. unfold O_WIDX in Cwi.
    assert (Rb3 : 0 <= b3 /\ b3 + 4 * Zlen xs0 < 2 ^ 64).
    { destruct V3blk as [[-> ->]|(Hb & _ & _ & Hbc & _)]; [unfold Zlen in *; lia | lia]. }
    pose proof (Zlen_nonneg xs0) as Hl0. pose proof (zw_next_range xs0) as Hzr.

    destruct (Z.lt_ge_cases (c_widx c) (i_io I + i_iwc I)) as [Hlt|Hge].
    2: {
         hseed R w c A M model X Cwi Cio Ciwc V3f0 V3f1 (i_io I) (i_iwc I) b3 xs0.
         xruns HR HK 100%nat (0x68560 :: 0x685b4 :: STOPS) (SCR [true] [] []) 50%N.
         { split_scs; try sc_auto1. all: cbn [sc_denot]; evs; rewrite ?ext_val_zx2, ?w_add by lia; rewrite ?br_geu, ?br_ltu, ?br_eq, ?br_ne by lia; try bool_lia. all: show_goal_dbg. }
         postrun. name_run HRn R1.
         rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12. rreg HRn (13%bv) G13. rreg HRn (22%bv) G22. rreg HRn (23%bv) G23.
         assert (OR1 : oregs w R1) by (oregs_seeded HRn Qgp Qtp). clear HRn HR HK.
         rewrite ?ext_val_zx2 in G10 by lia. rewrite ?ext_val_zx2 in G11 by lia. rewrite ?w_add in G11 by lia.
         eapply (EXITK R1 OR1 Hge G22 G23 G10 G11 G13 G12). }
    destruct xs0 as [|x0 xs0'] eqn:Exs.
    {
      pose proof (@Zlen_nil Z) as Hz0.
      hseed R w c A M model X Cwi Cio Ciwc V3f0 V3f1 (i_io I) (i_iwc I) b3 (@nil Z).
      xruns HR HK 100%nat (0x68560 :: 0x685b4 :: STOPS) (SCR [false; true] [] []) 50%N.
      { split_scs; try sc_auto1. all: cbn [sc_denot]; evs; rewrite ?ext_val_zx2, ?w_add by lia; rewrite ?br_geu, ?br_ltu, ?br_eq, ?br_ne by lia; try bool_lia. all: show_goal_dbg. }
      postrun. name_run HRn R1.
      rreg HRn (10%bv) G10. rreg HRn (22%bv) G22. rreg HRn (23%bv) G23.
      assert (OR1 : oregs w R1) by (oregs_seeded HRn Qgp Qtp). clear HRn HR HK.
      rewrite ?ext_val_zx2 in G10 by lia.
      eapply (D7K R1 OR1 Hlt eq_refl G22 G23 G10). }
    assert (Hne : xs0 <> []) by (rewrite Exs; discriminate).
    assert (Hl1 : 1 <= Zlen xs0) by (rewrite Exs, Zlen_cons; pose proof (Zlen_nonneg xs0'); lia).
    rewrite <- Exs in *. clear x0 xs0' Exs.
    hseed R w c A M model X Cwi Cio Ciwc V3f0 V3f1 (i_io I) (i_iwc I) b3 xs0.
    xruns HR HK 100%nat (0x68560 :: 0x685b4 :: STOPS) (SCR [false; false] [] []) 50%N.
    { split_scs; try sc_auto1. all: cbn [sc_denot]; evs; rewrite ?ext_val_zx2, ?w_add by lia; rewrite ?br_geu, ?br_ltu, ?br_eq, ?br_ne by lia; try bool_lia. all: show_goal_dbg. }
    postrun. name_run HRn R1.
    rreg HRn (1%bv) G1. rreg HRn (10%bv) G10.
    assert (OR1 : oregs w R1) by (oregs_seeded HRn Qgp Qtp). clear HRn HR HK.
    rewrite ?SymExec.alu64_add_lit in G10.

    eapply (pm_ohead_tf w c0 K fx I A M model c R1 b3 cap3 xs0 PS FZ FC IP ARMS); eassumption.
  Qed.

  Lemma pm_oloop : forall (w : pmw MI ST) c0 K (I : ictxR),
    PMS w c0 K -> ipure I ->
    (forall t, arm_stmt t (arm_pc t)) ->
    (forall (fx : FPState) A M model c R', frm_zero (@fp_csr fx) -> fconsts fx -> OLI w I A M model c R' -> i_io I + i_iwc I <= c_widx c ->
        getr R' 22%bv = Z_to_bv 64 (c_widx c) -> getr R' 23%bv = Z_to_bv 64 (i_io I) -> getr R' 10%bv = Z_to_bv 64 (i_iwc I) ->
        getr R' 11%bv = Z_to_bv 64 (i_io I + i_iwc I) -> getr R' 13%bv = Z_to_bv 64 (t3a (c_v3 c)) ->
        getr R' 12%bv = Z_to_bv 64 (t3a (c_v3 c) + 4 * Zlen (t3b (c_v3 c))) ->
        srealizes SEGS (cfg fx R' 0x68560 M model) K) ->
    (forall (fx : FPState) A M model c R', frm_zero (@fp_csr fx) -> fconsts fx -> OLI w I A M model c R' -> c_widx c < i_io I + i_iwc I -> t3b (c_v3 c) = [] ->
        getr R' 22%bv = Z_to_bv 64 (c_widx c) -> getr R' 23%bv = Z_to_bv 64 (i_io I) -> getr R' 10%bv = Z_to_bv 64 (i_iwc I) ->
        srealizes SEGS (cfg fx R' 0x685b4 M model) K) ->
    forall (fx : FPState) A M model c R, frm_zero (@fp_csr fx) -> fconsts fx -> OLI w I A M model c R -> srealizes SEGS (cfg fx R 0x677d0 M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K I PS IP ARMS EXITK D7K fx A M model c R FZ FC HOLI.
    remember (Z.to_nat (omeas I c)) as n eqn:Hn. revert fx FZ FC A M model c R HOLI Hn.
    induction n as [n IH] using (well_founded_induction Wf_nat.lt_wf). intros fx FZ FC A M model c R HOLI Hn.
    assert (Hm0 : 0 <= omeas I c) by (unfold omeas; pose proof (zw_next_range (t3b (c_v3 c))); lia).
    eapply (pm_ohead w c0 K fx I A M model c R PS FZ FC IP HOLI ARMS).
    - intros fx' A' M' model' c' R' FZ' FC' HOLI' Hlt.
      assert (Hm0' : 0 <= omeas I c') by (unfold omeas; pose proof (zw_next_range (t3b (c_v3 c'))); lia).
      eapply (IH (Z.to_nat (omeas I c'))); [lia | exact FZ' | exact FC' | exact HOLI' | reflexivity].
    - intros R' OR' Hge Q22 Q23 Q10 Q11 Q13 Q12. destruct HOLI as (OB & REST). destruct OB as (X & Htr & BUD & OR & REST2).
      eapply (EXITK fx A M model c R' FZ FC); try eassumption. split; [| exact REST]. split; [exact X|]. split; [exact Htr|]. split; [exact BUD|]. split; [exact OR' | exact REST2].
    - intros R' OR' Hlt Hnil Q22 Q23 Q10. destruct HOLI as (OB & REST). destruct OB as (X & Htr & BUD & OR & REST2).
      eapply (D7K fx A M model c R' FZ FC); try eassumption. split; [| exact REST]. split; [exact X|]. split; [exact Htr|]. split; [exact BUD|]. split; [exact OR' | exact REST2].
  Qed.
End PM.
