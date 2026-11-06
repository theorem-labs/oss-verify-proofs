(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Ubsan.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PropExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SeqExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StepTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.WalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StoreOk OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MemSplit OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Hoare OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ShapeAlg OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SRealizes OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MmapSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibIface OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibEff OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibBudget OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.FPSteps OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SumMemsetLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3Sound OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymRun3.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRepFacts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HStmtsU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HWord OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HUbsan OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HConstsU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HCommonU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HFpu OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HFpuU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HFindU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HBlkU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HNtCtxU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HNtAU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HNtFU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HNtRU1.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRehashModel OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.U1_code_689b8_69044 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.U1_code_6f888_6f894.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HNtDU1C.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HNtDU1B.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PeLia.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Module HNtDU1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PropExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SeqExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StepTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.WalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StoreOk OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MemSplit OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Hoare OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ShapeAlg OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SRealizes OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MmapSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibIface OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibEff OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibBudget OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.FPSteps OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SumMemsetLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3Sound OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymRun3.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRepFacts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HStmtsU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HWord OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HUbsan OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HConstsU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HCommonU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HFpu OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HFindU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HBlkU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRehashModel OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HNtCtxU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.U1_code_689b8_69044 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.U1_code_6f888_6f894.

Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PeLia.
Local Ltac lia ::= pe_lia.

Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation SEGS := Ubsan.M.loaded_segments.

Abbreviation STOPSD := HNtDU1C.STOPSD.

#[local] Notation ent := (Z * (Z * (Z * Z * Z)))%type.

Abbreviation KND := HNtDU1C.KND.

Abbreviation popcD := HNtDU1C.popcD.

Abbreviation popcDw := HNtDU1C.popcDw.

Abbreviation popcD_env := HNtDU1C.popcD_env.

Ltac vm_popcD :=
  match goal with |- context [bv_unsigned (popcDw ?w)] =>
    let v := eval vm_compute in (bv_unsigned (popcDw w)) in
    replace (bv_unsigned (popcDw w)) with v by (vm_compute; reflexivity) end.

Abbreviation popcD_ge2 := HNtDU1C.popcD_ge2.

Section NtD.
Context {AC : AllocCeiling}.

  Variables (L : Layout) (MI : MallocIface SEGS L) (ST : StaticsIface SEGS L) (NEW_STACK DEL_STACK : Z).
  Variables (fx : FPState) (A0 : AS MI) (s : LibIface.SX ST) (R0 : bvmap 5 word) (M0 : mem) (model0 : Model).
  Variables (sp parser key bl bc w1 w2 w3 : Z) (val : Z * Z * Z) (ents : list (Z * (Z * (Z * Z * Z)))) (K : TSet).
  Variable C : @ntctx AC L MI ST NEW_STACK DEL_STACK fx A0 s R0 M0 model0 sp parser key bl bc w1 w2 w3 val ents K.
  #[local] Abbreviation NTS := (NT_STACK NEW_STACK DEL_STACK).
  #[local] Abbreviation cfg fx R pc M model := (mkCfg (@mkst fx R (Z_to_bv 64 pc) M (seg_rom SEGS)) model).
  #[local] Abbreviation live_facts' := (live_facts L MI).
  #[local] Abbreviation live_offimg' := (live_offimg L MI).
  #[local] Abbreviation agree_above_via_eff' := (agree_above_via_eff L MI (c_HLimg_lo C) (c_HLrw_img C) (c_HLerr_rw C)).
  #[local] Abbreviation img_ro_clear_via_eff' := (img_ro_clear_via_eff L MI (c_HLimg_lo C) (c_HLerr_rw C)).
  #[local] Abbreviation sx_inv_via_eff' := (sx_inv_via_eff L MI ST (c_HLimg_lo C) (c_HLrw_img C) (c_HLrelro_img C) (c_HLrw_relro C) (c_HLerr_rw C)).
  #[local] Abbreviation ro_clear_via_eff' := (ro_clear_via_eff L MI (c_HLimg_lo C) (c_HLerr_rw C)).
  #[local] Abbreviation agree_block_via_eff' := (agree_block_via_eff L MI (c_HLrw_img C) (c_HLerr_rw C)).
  #[local] Abbreviation own_sx_via_eff' := (own_sx_via_eff L MI ST (c_HLrw_img C)).
  #[local] Abbreviation hi_unowned' := (hi_unowned L MI (c_HLimg_lo C) (c_HLrw_img C)).
  #[local] Abbreviation obj := (parser + 136).
  #[local] Abbreviation sent := (parser + 152).
  #[local] Abbreviation W := (Wnt NEW_STACK DEL_STACK sp).
  #[local] Abbreviation base_ok := (nt_base_ok L R0 sp parser).
  #[local] Abbreviation pframe := (nt_pframe sp parser key w1 w2).
  #[local] Abbreviation fbase := (nt_fbase fx).
  #[local] Abbreviation SPF := (sp_facts C).
  #[local] Abbreviation BCF := (bc_facts C).
  #[local] Abbreviation VF := (val_facts C).
  #[local] Ltac ctx := ntctx_pose C.

  #[local] Abbreviation del_call := (HNtDU1C.del_call (AC:=AC) L MI ST NEW_STACK DEL_STACK fx A0 s R0 M0 model0 sp parser key bl bc w1 w2 w3 val ents K C).

  Section Reh.

    Variables (fxr : FPState) (Ar : AS MI) (Mr : mem) (modelr : Model) (Rr : bvmap 5 word) (pn : Z).
    #[local] Abbreviation n := (bseq_next bc).
    Hypothesis AIr : ainv MI Ar Mr modelr.
    Hypothesis MSr : mstd modelr.
    Hypothesis Hfsr : m_fs modelr = m_fs model0.
    Hypothesis Hfdsr : m_fds modelr = m_fds model0.
    Hypothesis SXr : sx_inv ST s Mr.
    Hypothesis RCr : ro_clear L Mr.
    Hypothesis OSXr : forall a, owned MI Ar a -> ~ sx_region ST a.

    #[local] Abbreviation dbase := (HNtDU1C.dbase L R0 sp parser key w3 pn).
    Hypothesis Br : dbase Rr.
    Hypothesis Q22r : getr Rr 22%bv = Z_to_bv 64 n.
    Hypothesis Q10r : getr Rr 10%bv = Z_to_bv 64 (8 * n).
    Hypothesis Q1r : getr Rr 1%bv = Z_to_bv 64 NT_NEW2R.
    Hypothesis Ur : umapx MI 32 (nval32 SEGS) Ar Mr obj bl bc ents.
    Hypothesis DEFWr : defined Mr (sp - NTS) NTS.
    Hypothesis FRr : pframe Mr.
    Hypothesis SPLr : cell8 SEGS Mr sp (2 ^ 60).
    Hypothesis DEF0r : defined Mr sp 8.
    Hypothesis ROOMr : roomL MI Ar (live MI Ar) (8 * n).
    Hypothesis CONTD : forall A' R' M' model' (bl' : Z) (ents' : list ent),
        ainv MI A' M' model' -> mstd model' -> m_fs model' = m_fs model0 -> m_fds model' = m_fds model0 ->
        dbase R' ->
        umapx MI 32 (nval32 SEGS) A' M' obj bl' n ents' -> Permutation ents' ents ->
        lapply (live MI Ar) (LAdd bl' (8 * n) :: (if bc =? 0 then [] else [LDel bl])) (live MI A') ->
        eff MI Ar A' Mr M' W (fun a => umap_foot 32 obj bl bc ents a \/ umap_foot 32 obj bl' n ents' a) ->
        defined M' (sp - NTS) NTS -> getr R' 6%bv = Z_to_bv 64 (2 ^ 60) ->
        srealizes SEGS (cfg fxr R' NT_AFTER M' model') K.

    #[local] Abbreviation n_facts := (HNtDU1C.n_facts (AC:=AC) L MI ST NEW_STACK DEL_STACK fx A0 s R0 M0 model0 sp parser key bl bc w1 w2 w3 val ents K C).
    #[local] Opaque bseq_next.

    #[local] Abbreviation iroc_r := (HNtDU1C.iroc_r (AC:=AC) L MI ST NEW_STACK DEL_STACK fx A0 s R0 M0 model0 sp parser key bl bc w1 w2 w3 val ents K C Mr SXr RCr).

    #[local] Abbreviation tbl_blocks_live := (HNtDU1C.tbl_blocks_live (AC:=AC) L MI NEW_STACK DEL_STACK R0 model0 sp parser key bl bc w3 ents K fxr Ar Mr pn Ur CONTD).

    #[local] Abbreviation foot_offimg := (HNtDU1C.foot_offimg (AC:=AC) L MI ST NEW_STACK DEL_STACK fx A0 s R0 M0 model0 sp parser key bl bc w1 w2 w3 val ents K C Ar Mr modelr AIr Ur).

    #[local] Abbreviation win_r := (HNtDU1C.win_r (AC:=AC) L MI ST NEW_STACK DEL_STACK fx A0 s R0 M0 model0 sp parser key bl bc w1 w2 w3 val ents K C).

    #[local] Abbreviation phaseA := (HNtDU1C.phaseA (AC:=AC) L MI ST NEW_STACK DEL_STACK fx A0 s R0 M0 model0 sp parser key bl bc w1 w2 w3 val ents K C fxr Ar Mr modelr Rr pn AIr MSr Hfsr Hfdsr SXr RCr OSXr Br Q22r Q10r Q1r Ur DEFWr ROOMr CONTD).

    #[local] Abbreviation dbase_kept := (HNtDU1C.dbase_kept L R0 sp parser key w3 pn).

    Ltac dbase_from HR' D :=
      let B := fresh in let Q23 := fresh in let Q27 := fresh in let Q26 := fresh in
      pose proof D as B; destruct B as (B & Q23 & Q27 & Q26);
      split; [nt_base_from HR' B
             | split; [ let Q := fresh in rreg HR' 23%bv Q; rewrite Q; first [reflexivity | exact Q23]
                      | split; [ let Q := fresh in rreg HR' 27%bv Q; rewrite Q; first [reflexivity | exact Q27]
                               | let Q := fresh in rreg HR' 26%bv Q; rewrite Q; first [reflexivity | exact Q26] ] ] ].

    #[local] Abbreviation rst := (HNtDU1C.rst (AC:=AC) L MI NEW_STACK DEL_STACK R0 model0 sp parser key bc w3 Ar Mr pn).
    #[local] Abbreviation RST := (HNtDU1C.RST (AC:=AC) L MI NEW_STACK DEL_STACK R0 model0 sp parser key bc w3 Ar Mr pn).
    #[local] Abbreviation r_ai := (HNtDU1C.r_ai (AC:=AC) L MI NEW_STACK DEL_STACK R0 model0 sp parser key bc w3 Ar Mr pn).
    #[local] Abbreviation r_ms := (HNtDU1C.r_ms (AC:=AC) L MI NEW_STACK DEL_STACK R0 model0 sp parser key bc w3 Ar Mr pn).
    #[local] Abbreviation r_fs := (HNtDU1C.r_fs (AC:=AC) L MI NEW_STACK DEL_STACK R0 model0 sp parser key bc w3 Ar Mr pn).
    #[local] Abbreviation r_fds := (HNtDU1C.r_fds (AC:=AC) L MI NEW_STACK DEL_STACK R0 model0 sp parser key bc w3 Ar Mr pn).
    #[local] Abbreviation r_regs := (HNtDU1C.r_regs (AC:=AC) L MI NEW_STACK DEL_STACK R0 model0 sp parser key bc w3 Ar Mr pn).
    #[local] Abbreviation r_s6 := (HNtDU1C.r_s6 (AC:=AC) L MI NEW_STACK DEL_STACK R0 model0 sp parser key bc w3 Ar Mr pn).
    #[local] Abbreviation r_def := (HNtDU1C.r_def (AC:=AC) L MI NEW_STACK DEL_STACK R0 model0 sp parser key bc w3 Ar Mr pn).
    #[local] Abbreviation r_eff := (HNtDU1C.r_eff (AC:=AC) L MI NEW_STACK DEL_STACK R0 model0 sp parser key bc w3 Ar Mr pn).
    #[local] Abbreviation r_lap := (HNtDU1C.r_lap (AC:=AC) L MI NEW_STACK DEL_STACK R0 model0 sp parser key bc w3 Ar Mr pn).
    #[local] Abbreviation r_p0 := (HNtDU1C.r_p0 (AC:=AC) L MI NEW_STACK DEL_STACK R0 model0 sp parser key bc w3 Ar Mr pn).
    #[local] Abbreviation r_pc := (HNtDU1C.r_pc (AC:=AC) L MI NEW_STACK DEL_STACK R0 model0 sp parser key bc w3 Ar Mr pn).
    #[local] Abbreviation r_pal := (HNtDU1C.r_pal (AC:=AC) L MI NEW_STACK DEL_STACK R0 model0 sp parser key bc w3 Ar Mr pn).
    #[local] Abbreviation r_plive := (HNtDU1C.r_plive (AC:=AC) L MI NEW_STACK DEL_STACK R0 model0 sp parser key bc w3 Ar Mr pn).
    #[local] Abbreviation r_pnew := (HNtDU1C.r_pnew (AC:=AC) L MI NEW_STACK DEL_STACK R0 model0 sp parser key bc w3 Ar Mr pn).
    #[local] Abbreviation r_Foff := (HNtDU1C.r_Foff (AC:=AC) L MI NEW_STACK DEL_STACK R0 model0 sp parser key bc w3 Ar Mr pn).
    #[local] Abbreviation r_hdef := (HNtDU1C.r_hdef (AC:=AC) L MI NEW_STACK DEL_STACK R0 model0 sp parser key bc w3 Ar Mr pn).

    #[local] Abbreviation FA := (HNtDU1C.FA bc).

    #[local] Abbreviation FB := (HNtDU1C.FB parser bl bc).

    #[local] Abbreviation opsB := (HNtDU1C.opsB bl bc).

    #[local] Abbreviation cell_via := (HNtDU1C.cell_via (AC:=AC) L MI ST NEW_STACK DEL_STACK fx A0 s R0 M0 model0 sp parser key bl bc w1 w2 w3 val ents K C Ar Mr modelr AIr).

    #[local] Abbreviation frame_via := (HNtDU1C.frame_via (AC:=AC) L MI ST NEW_STACK DEL_STACK fx A0 s R0 M0 model0 sp parser key bl bc w1 w2 w3 val ents K C Ar Mr modelr AIr FRr SPLr).

    #[local] Abbreviation f2_via := (HNtDU1C.f2_via (AC:=AC) L MI ST NEW_STACK DEL_STACK fx A0 s R0 M0 model0 sp parser key bl bc w1 w2 w3 val ents K C Ar Mr modelr AIr FRr SPLr).

    #[local] Abbreviation p_apart := (HNtDU1C.p_apart (AC:=AC) L MI NEW_STACK DEL_STACK R0 model0 sp parser key bl bc w3 ents K fxr Ar Mr pn Ur CONTD).

    #[local] Abbreviation phaseB := (HNtDU1C.phaseB (AC:=AC) L MI ST NEW_STACK DEL_STACK fx A0 s R0 M0 model0 sp parser key bl bc w1 w2 w3 val ents K C fxr Ar Mr modelr pn AIr SXr RCr Ur CONTD).

    #[local] Abbreviation FC := (HNtDU1C.FC parser bl bc).

    #[local] Abbreviation zloop := (HNtDU1C.zloop (AC:=AC) L MI ST NEW_STACK DEL_STACK fx A0 s R0 M0 model0 sp parser key bl bc w1 w2 w3 val ents K C fxr pn).

    #[local] Abbreviation phaseC := (HNtDU1C.phaseC (AC:=AC) L MI ST NEW_STACK DEL_STACK fx A0 s R0 M0 model0 sp parser key bl bc w1 w2 w3 val ents K C fxr Ar Mr modelr pn AIr Ur FRr SPLr CONTD).

    #[local] Notation lent := (Z * (Z * (Z * Z * Z)))%type.

    #[local] Abbreviation d0 := HNtDU1C.d0.
    #[local] Notation addr := (HRehashModel.addr (Z * Z * Z)%type).
    #[local] Notation hkey := (HRehashModel.hkey (Z * Z * Z)%type).
    #[local] Notation hh := (HRehashModel.hh (Z * Z * Z)%type n).
    #[local] Notation snt := (obj + 16).

    #[local] Abbreviation sc_disjZ := HNtDU1C.sc_disjZ.

    #[local] Abbreviation lst := (HNtDU1C.lst (AC:=AC) L MI R0 sp parser key bc w3 ents pn).
    #[local] Abbreviation LST := (HNtDU1C.LST (AC:=AC) L MI R0 sp parser key bc w3 ents pn).
    #[local] Abbreviation l_regs := (HNtDU1C.l_regs (AC:=AC) L MI R0 sp parser key bc w3 ents pn).
    #[local] Abbreviation l_x10 := (HNtDU1C.l_x10 (AC:=AC) L MI R0 sp parser key bc w3 ents pn).
    #[local] Abbreviation l_x22 := (HNtDU1C.l_x22 (AC:=AC) L MI R0 sp parser key bc w3 ents pn).
    #[local] Abbreviation l_x11 := (HNtDU1C.l_x11 (AC:=AC) L MI R0 sp parser key bc w3 ents pn).
    #[local] Abbreviation l_x15 := (HNtDU1C.l_x15 (AC:=AC) L MI R0 sp parser key bc w3 ents pn).
    #[local] Abbreviation l_x12 := (HNtDU1C.l_x12 (AC:=AC) L MI R0 sp parser key bc w3 ents pn).
    #[local] Abbreviation l_c13 := (HNtDU1C.l_c13 (AC:=AC) L MI R0 sp parser key bc w3 ents pn).
    #[local] Abbreviation l_c14 := (HNtDU1C.l_c14 (AC:=AC) L MI R0 sp parser key bc w3 ents pn).
    #[local] Abbreviation l_c6 := (HNtDU1C.l_c6 (AC:=AC) L MI R0 sp parser key bc w3 ents pn).
    #[local] Abbreviation l_perm := (HNtDU1C.l_perm (AC:=AC) L MI R0 sp parser key bc w3 ents pn).
    #[local] Abbreviation l_binv := (HNtDU1C.l_binv (AC:=AC) L MI R0 sp parser key bc w3 ents pn).
    #[local] Abbreviation l_P := (HNtDU1C.l_P (AC:=AC) L MI R0 sp parser key bc w3 ents pn).
    #[local] Abbreviation l_p1 := (HNtDU1C.l_p1 (AC:=AC) L MI R0 sp parser key bc w3 ents pn).
    #[local] Abbreviation l_chain := (HNtDU1C.l_chain (AC:=AC) L MI R0 sp parser key bc w3 ents pn).
    #[local] Abbreviation l_hash := (HNtDU1C.l_hash (AC:=AC) L MI R0 sp parser key bc w3 ents pn).
    #[local] Abbreviation l_tail := (HNtDU1C.l_tail (AC:=AC) L MI R0 sp parser key bc w3 ents pn).
    #[local] Abbreviation l_bkt := (HNtDU1C.l_bkt (AC:=AC) L MI R0 sp parser key bc w3 ents pn).
    #[local] Abbreviation l_defp := (HNtDU1C.l_defp (AC:=AC) L MI R0 sp parser key bc w3 ents pn).
    #[local] Abbreviation l_defh := (HNtDU1C.l_defh (AC:=AC) L MI R0 sp parser key bc w3 ents pn).
    #[local] Abbreviation l_defn := (HNtDU1C.l_defn (AC:=AC) L MI R0 sp parser key bc w3 ents pn).
    #[local] Abbreviation l_live := (HNtDU1C.l_live (AC:=AC) L MI R0 sp parser key bc w3 ents pn).
    #[local] Abbreviation l_plive := (HNtDU1C.l_plive (AC:=AC) L MI R0 sp parser key bc w3 ents pn).

    #[local] Abbreviation Wloop := (HNtDU1C.Wloop parser bc ents).

    #[local] Abbreviation ent_facts := (HNtDU1C.ent_facts (AC:=AC) L MI parser bl bc ents).

    Ltac rdx Hh H := eapply (sc_read_cellw _ _ _ _ _ _ _ _ H);
      [ cbn; lia | evs; rewrite ?w_remu, ?w_mul, ?w_add by lia; rewrite ?v_addi_Z by lia; rewrite ?Hh; first [reflexivity | f_equal; lia] | evs; first [reflexivity | f_equal; lia] ].

    #[local] Abbreviation last_any := HNtDU1C.last_any.

    #[local] Abbreviation hda := (HNtDU1C.hda L).

    #[local] Abbreviation lnk := HNtDU1C.lnk.

    #[local] Abbreviation lnk_chain := HNtDU1C.lnk_chain.

    #[local] Abbreviation hd_app := HNtDU1C.hd_app.

    #[local] Abbreviation hdaddr_hda := HNtDU1C.hdaddr_hda.

    #[local] Abbreviation lnk_app := HNtDU1C.lnk_app.

    #[local] Abbreviation last_app_ne := HNtDU1C.last_app_ne.

    #[local] Abbreviation lnk_agree := HNtDU1C.lnk_agree.

    #[local] Abbreviation perm_nodup := (HNtDU1C.perm_nodup (AC:=AC) L MI parser bl bc ents).

    #[local] Abbreviation nodup_app_ne := HNtDU1C.nodup_app_ne.

    #[local] Abbreviation last_in := HNtDU1C.last_in.

    #[local] Abbreviation apart_sub := HNtDU1C.apart_sub.

    #[local] Abbreviation apart_sym := HNtDU1C.apart_sym.

    #[local] Abbreviation splice_facts := (HNtDU1C.splice_facts (AC:=AC) L MI parser bl bc ents).

    #[local] Abbreviation nodes_apart := (HNtDU1C.nodes_apart (AC:=AC) L MI parser bl bc ents).

    #[local] Abbreviation p_node_apart := (HNtDU1C.p_node_apart (AC:=AC) L MI parser bl bc ents Ar Mr Ur).

    Ltac sub_of x y := lazymatch y with | x => idtac | Z.add x _ => idtac | Z.add (Z.add x _) _ => idtac end.
    Ltac dj_apart Hr :=
      cbn [a_off]; rewrite ?Z.add_0_r;
      lazymatch goal with |- ?a + ?k <= ?b \/ ?b + ?m <= ?a => change (apart a k b m) end;
      match goal with H : apart ?a0 _ ?b0 _ |- apart ?a _ ?b _ =>
        first [ sub_of a0 a; sub_of b0 b; eapply (apart_sub _ _ _ _ _ _ _ _ H); clear - Hr; lia
              | sub_of a0 b; sub_of b0 a; eapply (apart_sub _ _ _ _ _ _ _ _ (apart_sym _ _ _ _ H)); clear - Hr; lia ] end.
    Ltac dj Hh := eapply sc_disjZ;
      [ evs; rewrite ?w_remu, ?w_mul, ?w_add by lia; rewrite ?v_addi_Z by lia; rewrite ?Hh; reflexivity
      | evs; rewrite ?w_remu, ?w_mul, ?w_add by lia; rewrite ?v_addi_Z by lia; rewrite ?Hh; reflexivity
      | lia | lia | lia | lia | cbn [a_off]; lia | cbn [a_off]; lia | cbn [a_off]; lia | cbn [a_off]; lia | cbn [a_off]; unfold apart in *; lia ].

    Ltac nrm Hrm Hba := rewrite ?Hrm; rewrite ?Hba.
    Ltac rdq Hrm Hba H :=
      lazymatch type of H with cellw _ _ ?a _ _ =>
      eapply (sc_read_cellw _ _ _ _ _ _ _ _ H);
      [ apply N.le_refl
      | evs; nrm Hrm Hba; lazymatch goal with |- v_addi (Z_to_bv 64 ?b) _ = _ => sub_of b a end;
        rewrite ?v_addi_Z by lia; rewrite ?Z.add_0_r; first [reflexivity | f_equal; lia]
      | evs; first [reflexivity | f_equal; lia] ] end.
    Ltac djq Hrm Hba Hr := eapply sc_disjZ;
      [ evs; nrm Hrm Hba; reflexivity | evs; nrm Hrm Hba; reflexivity
      | lia | lia | lia | lia | cbn [a_off]; lia | cbn [a_off]; lia | cbn [a_off]; lia | cbn [a_off]; lia | dj_apart Hr ].
    Ltac soq Hrm Hba := eapply (sc_storeok _ _ _ _ _ 8);
      [ evs; nrm Hrm Hba; reflexivity | lia | cbn [a_off]; lia | cbn [a_off]; lia
      | cbn [a_off]; rewrite ?Z.add_0_r;
        first [ lazymatch goal with |- defined _ ?a _ => match goal with D : defined _ a _ |- _ => eapply (defined_sub _ _ _ _ _ D); lia end end
              | match goal with D : defined _ _ _ |- _ => eapply (defined_sub _ _ _ _ _ D); lia end ] ].
    Ltac flq Hrm Hba := eapply sc_flat; [evs; nrm Hrm Hba; reflexivity | lia | cbn [a_off]; lia | lia | cbn [a_off]; lia].
    Ltac brq Hrm Hba := cbn [sc_denot]; evs; nrm Hrm Hba; rewrite ?br_eq, ?br_ne, ?br_ltu by lia; bool_lia.

    Ltac trapq Hrm Hba :=
      first [ eapply sc_trap_align; [evs; nrm Hrm Hba; reflexivity | lia | first [assumption | apply align16_8; assumption] ]
            | eapply sc_trap_srl; [evs; nrm Hrm Hba; rewrite ?w_add by lia; reflexivity | lia | lia]
            | eapply sc_trap_null; [evs; nrm Hrm Hba; reflexivity | lia]
            | eapply sc_trap_wrap; [evs; nrm Hrm Hba; reflexivity | evs; reflexivity | lia | lia | lia] ].

    Ltac popq := cbn [sc_denot]; evs; rewrite branch_geu_lit_r by lia; bool_lia.
    Ltac scq Hrm Hba Hr :=
      lazymatch goal with
      | |- sc_denot _ _ _ (SCBr false BC_NE (EAlu ALU_AND _ (ELit 7)) (ELit 0)) => trapq Hrm Hba
      | |- sc_denot _ _ _ (SCBr false BC_NE (EAlu ALU_SRL _ (ELit 61)) (ELit 0)) => trapq Hrm Hba
      | |- sc_denot _ _ _ (SCBr true BC_EQ (EAlu ALU_AND _ (ELit 7)) (ELit 0)) => cbn [sc_denot]; cbn [edenot]; evs; nrm Hrm Hba; rewrite w_and, land_7 by lia;
            match goal with H : ?t mod 8 = 0 |- context [Z_to_bv 64 (?t mod 8)] => rewrite H; reflexivity | _ => rewrite align16_8 by assumption; reflexivity end
      | |- sc_denot _ _ _ (SCBr true BC_GEU _ (ELit 2)) => popq
      | |- sc_denot _ _ _ (SCBr _ _ _ _) => first [brq Hrm Hba | trapq Hrm Hba]
      | |- sc_denot _ _ _ (SCFlat _ _) => flq Hrm Hba
      | |- sc_denot _ _ _ (SCDisj _ _ _ _) => djq Hrm Hba Hr
      | |- sc_denot _ _ _ (SCStoreOk _ _) => soq Hrm Hba
      | |- sc_denot _ _ _ (SCReadBase _ _ _ _) => match goal with H : cellw _ _ _ 8%N _ |- _ => rdq Hrm Hba H end
      end.
    Ltac scqs Hrm Hba Hr := split_scs; scq Hrm Hba Hr.

    Ltac finq Hrm Hba FIN HR' DB :=
      eapply FIN;
      [ first [ exact (or_intror I) | evs; nrm Hrm Hba; rewrite ?w_add, ?v_addi_Z by lia; rewrite ?Z.add_0_r; reflexivity ]
      | dbase_from HR' DB
      | let Q := fresh in rreg HR' 10%bv Q; exact Q
      | let Q := fresh in rreg HR' 22%bv Q; exact Q
      | let Q := fresh in rreg HR' 11%bv Q; exact Q
      | let Q := fresh in rreg HR' 15%bv Q; rewrite Q; reflexivity
      | let Q := fresh in rreg HR' 12%bv Q; rewrite Q; nrm Hrm Hba; first [reflexivity | f_equal; lia]
      | let Q := fresh in rreg HR' 13%bv Q; exact Q
      | let Q := fresh in rreg HR' 14%bv Q; exact Q
      | let Q := fresh in rreg HR' 6%bv Q; exact Q
      | ].

    #[local] Abbreviation loop_step := (HNtDU1B.loop_step (AC:=AC) L MI ST NEW_STACK DEL_STACK fx A0 s R0 M0 model0 sp parser key bl bc w1 w2 w3 val ents K C fxr Ar Mr pn Ur).

#[local] Definition HTHNtU1_0 : list (reg * expr) := [(10%bv, EVar 32); (8%bv, EVar 33); (2%bv, EVar 34); (22%bv, EVar 35); (15%bv, EVar 36); (6%bv, EVar 42)].
    Lemma phaseD : forall A1 M1 A2 M3 model2 R3 p,
      rst (FC p) (opsB p) p A2 M3 model2 R3 -> getr R3 10%bv = Z_to_bv 64 p -> getr R3 15%bv = Z_to_bv 64 (2 ^ 64 - 1 - p) -> getr R3 6%bv = Z_to_bv 64 (2 ^ 60) ->
      umapx MI 32 (nval32 SEGS) A1 M1 obj bl bc ents ->
      agree_on M1 M3 (obj + 16) 24 ->
      (forall q k v, In (q, (k, v)) ents -> agree_on M1 M3 q 32 /\ In (q, 32) (live MI A2)) ->
      (forall i, 0 <= i < n -> cell8 SEGS M3 (p + 8 * i) 0) ->
      (ents = [] -> forall R4, dbase R4 -> getr R4 6%bv = Z_to_bv 64 (2 ^ 60) -> srealizes SEGS (cfg fxr R4 NT_AFTER M3 model2) K) ->
      (forall e S M4 R4 (pc : Z), ents = e :: S -> (pc = NT_AFTER /\ S = [] \/ pc = NT_LOOP /\ S <> []) ->
          lst p M1 [e] S (fun i => if i =? hh e then snt else 0) A2 M4 R4 ->
          (forall a : word, ~ Wloop p (bv_unsigned a) -> M4 a = M3 a) -> (forall a : word, M3 a <> None -> M4 a <> None) ->
          ainv MI A2 M4 model2 ->
          srealizes SEGS (cfg fxr R4 pc M4 model2) K) ->
      srealizes SEGS (cfg fxr R3 NT_D M3 model2) K.
    Proof using AC L MI ST NEW_STACK DEL_STACK fx A0 s R0 M0 model0 sp parser key bl bc w1 w2 w3 val ents K C fxr Ar Mr modelr pn AIr Ur FRr SPLr CONTD.
      ctx. intros A1 M1 A2 M3 model2 R3 p D G10 G15 G6 U1 AGh Hnodes Hz PEXIT PLOOP. change 1152921504606846976 with (2 ^ 60) in G6, PEXIT, PLOOP |- *.
      destruct SPF as (Hsp16' & Hsplo & Hsphi & Hn16 & HnN & HnD & Hs1 & Hpar). pose proof ceiling_lt as Hcl. pose proof ac_bounds_lit as Hcv.
      pose proof (u_obj_hi Ur) as Hh1.
      destruct n_facts as (HnB & Hbcn & Hn28 & Hncase).
      assert (Hbc0 : 0 <= bc) by (pose proof (u_bseq Ur) as HB; unfold BSEQ in HB; cbn in HB; lia).
      pose proof D as D'. destruct D' as [AI MS Hfs Hfds DB S6 DEF EFF LAP Hp0 Hpc Hpal Hpl Hpnew HFoff HDEF]. pose proof DB as DBx. destruct DBx as (B & HQ23 & HQ27 & HQ26). pose proof B as Bx. destruct Bx as (B2 & B3 & B4 & B8 & B18 & Bs).
      pose proof (u_obj_lo U1) as Hobjlo. pose proof (u_obj_hi U1) as Hobjhi.

      assert (Cp1 : cell8 SEGS M3 (obj + 16) (hdaddr ents)).
      { eapply cellw_agree; [exact (h_p1 (u_hdr U1)) | eapply agree_on_sub; [exact AGh | lia | cbn; lia] | lia | cbn; lia]. }
      unfold cell8 in Cp1. pose proof (proj1 Cp1) as Hhdr.
      assert (Hblc : bc <> 0 -> bl + 8 * bc <= alloc_ceiling).
      { intros Hnz. destruct (u_blive Ur) as [[? ?]|[_ Hin]]; [lia|]. destruct (live_facts' Ar Mr modelr bl (8 * bc) AIr Hin) as (_ & _ & Hc & _). exact Hc. }
      assert (HFCoff : forall a, FC p a -> ~ (sp <= a < sp + 264)) by (intros a [[Ha|[Ha|[Hnz Ha]]]|Ha]; unfold FA in *; [lia | lia | pose proof (Hblc Hnz); lia | lia]).
      pose proof (f2_via A2 M3 (FC p) EFF HFCoff) as F2. unfold cell8 in F2.
      destruct (frame_via A2 M3 (FC p) EFF HFCoff) as [(_ & _ & F56 & F64 & F72 & F80 & _ & _) _].
      assert (HKD : forall E, ev E 34 = Z_to_bv 64 sp -> know_ok SEGS E M3 KND).
      { intros E HE34. unfold KND. repeat apply Forall_cons; try apply Forall_nil;
          (eapply (kword_var _ _ _ _ sp); [ | apply N.le_refl | exact HE34 | lia | lia | cbn; lia | reflexivity]); [exact F80 | exact F72 | exact F64 | exact F56]. }
      destruct ents as [|e S] eqn:HE.
      -
        rewrite ?HE in Cp1. cbn [hdaddr] in Cp1. clear Hncase.
        pose (E := Eseed R3 [Z_to_bv 64 p; Z_to_bv 64 parser; Z_to_bv 64 sp; Z_to_bv 64 n; Z_to_bv 64 (2 ^ 64 - 1 - p); Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 snt; Z_to_bv 64 snt; Z_to_bv 64 (2 ^ 60)]).
        assert (HR : regs_ok E (srs sr_id HTHNtU1_0) R3).
        { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
        pose proof (HKD E ltac:(evs; reflexivity)) as HK.
        xruns HR HK 100%nat STOPSD (SCR [true] [EVar 40; EVar 37] []) 50%N; [split_scs; try sc_auto1; sc_rd F2|].
        (apply (PEXIT HE) || apply (PEXIT eq_refl)); [dbase_from HR' DB | let Q := fresh in rreg HR' 6%bv Q; exact Q].
      -
        destruct e as [q [k v]]. rewrite ?HE in U1, Hnodes, Cp1.
        destruct (u_node U1 q k v (or_introl eq_refl)) as (_ & Hq0 & Hq1 & Hqal & Chash & _ & Hk & _ & Hqobj & _).
        destruct (Hnodes q k v (or_introl eq_refl)) as [AGq Hlv].
        assert (Cqh : cell8 SEGS M3 (q + 8) k) by (eapply cellw_agree; [exact Chash | eapply agree_on_sub; [exact AGq | lia | cbn; lia] | lia | cbn; lia]).
        assert (Cqn : cell8 SEGS M3 q (hdaddr S)).
        { pose proof (u_chain U1) as CH. cbn in CH. eapply cellw_agree; [exact (proj1 CH) | eapply agree_on_sub; [exact AGq | lia | cbn; lia] | lia | cbn; lia]. }
        unfold cell8 in Cqh, Cqn. pose proof (proj1 Cqn) as HSr. cbn [hdaddr] in Cp1.
        assert (Hbc1 : bc <> 0) by (pose proof (u_load U1) as HL; unfold Zlength in HL; cbn [length] in HL; lia).
        destruct Hncase as [[? ?] | [Hn3 Hland]]; [lia|].
        assert (Hn0 : 0 < n) by lia.
        assert (Hlandr : 0 <= Z.land n (n - 1) < 2 ^ 64).
        { pose proof (Z.add_lor_land n (n - 1)). pose proof (Z.land_nonneg n (n - 1)). pose proof (Z.lor_nonneg n (n - 1)). lia. }
        set (h0 := hmod k n).
        assert (Hh0 : 0 <= h0 < n) by (unfold h0, hmod; apply Z.mod_pos_bound; lia).
        assert (Hh : k mod n = h0) by reflexivity.
        assert (Hpq : apart p (8 * n) q 32).
        { apply (ai_live_disjoint MI A2 M3 model2 p (8 * n) q 32 AI Hpl Hlv). intros <-. apply Hpnew.
          apply (in_map fst _ (p, 32)). exact (proj1 (u_node Ur p k v ltac:(first [rewrite ?HE; left; reflexivity | left; reflexivity]))). }
        assert (DEFp : defined M3 p (8 * n)) by (intros i Hi; destruct (live_facts' A2 M3 model2 p (8 * n) AI Hpl) as (_ & _ & _ & Hall); exact (proj2 (Hall (p + i) ltac:(lia)))).
        pose (E := Eseed R3 [Z_to_bv 64 p; Z_to_bv 64 parser; Z_to_bv 64 sp; Z_to_bv 64 n; Z_to_bv 64 (2 ^ 64 - 1 - p); Z_to_bv 64 q; Z_to_bv 64 k; Z_to_bv 64 (hdaddr S); Z_to_bv 64 snt; Z_to_bv 64 snt; Z_to_bv 64 (2 ^ 60)]).
        assert (HR : regs_ok E (srs sr_id HTHNtU1_0) R3).
        { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
        pose proof (HKD E ltac:(evs; reflexivity)) as HK.
        pose proof (popcD_ge2 bc (u_bseq Ur) Hbc1 Hlast) as Hpop.
        assert (Hpc' : forall b : bool, branch_taken BC_GEU (edenot E popcD) (edenot E (ELit 2)) = b ->
                       sc_denot SEGS M3 E (SCBr b BC_GEU popcD (ELit 2))) by (intros b Hb; exact Hb).
        assert (FIN : forall R' M4,
                  M4 = wbytes M3 (Z_to_bv 64 (p + 8 * h0)) (word_to_le_bytes 8 (Z_to_bv 64 snt)) ->
                  dbase R' ->
                  getr R' 10%bv = Z_to_bv 64 p -> getr R' 22%bv = Z_to_bv 64 n ->
                  getr R' 11%bv = Z_to_bv 64 q -> getr R' 15%bv = Z_to_bv 64 (hdaddr S) -> getr R' 12%bv = Z_to_bv 64 h0 ->
                  2 <= bv_unsigned (getr R' 13%bv) -> getr R' 14%bv = Z_to_bv 64 (n - 1) -> getr R' 6%bv = Z_to_bv 64 (2 ^ 60) ->
                  forall pc, (pc = NT_AFTER /\ S = [] \/ pc = NT_LOOP /\ S <> []) ->
                  srealizes SEGS (cfg fxr R' pc M4 model2) K).
        { intros R' M4 HM4 DB' Q10 Q22 Q11 Q15 Q12 QC13 QC14 QC6 pc Hpc2.
          assert (HMw : forall a : word, ~ (p + 8 * h0 <= bv_unsigned a < p + 8 * h0 + 8) -> M4 a = M3 a).
          { intros a Ha. pose proof (u64_range a). rewrite HM4, wbytes_outside; [reflexivity | ..]; rewrite ?length_N_to_le_bytes, ?u64_of_Z by lia; change (Z.of_nat 8) with 8; lia. }
          assert (HMg : forall a : word, M3 a <> None -> M4 a <> None) by (intros a Ha; rewrite HM4; apply wbytes_grows; exact Ha).
          assert (HMa : forall a kk, 0 <= a -> a + kk <= 2 ^ 47 -> apart a kk (p + 8 * h0) 8 -> agree_on M3 M4 a kk).
          { intros a kk Ha Hak H1 i Hi. apply HMw; rewrite u64_of_Z by lia; clear - H1 Hi; unfold apart in *; lia. }

          assert (HN : forall q' k' v', In (q', (k', v')) ((q, (k, v)) :: S) -> agree_on M1 M4 q' 32 /\ In (q', 32) (live MI A2) /\ 0 < q' /\ q' + 32 <= 2 ^ 47).
          { intros q' k' v' Hin. destruct (Hnodes q' k' v' Hin) as [AG' Hlv']. destruct (u_node U1 q' k' v' Hin) as (_ & Hq'0 & Hq'1 & _).
            assert (Hne : p <> q') by (intros <-; apply Hpnew; apply (in_map fst _ (p, 32)); exact (proj1 (u_node Ur p k' v' ltac:(first [rewrite ?HE; exact Hin | exact Hin])))).
            pose proof (ai_live_disjoint MI A2 M3 model2 p (8 * n) q' 32 AI Hpl Hlv' Hne) as Hap.
            split; [| split; [exact Hlv' | lia]].
            eapply agree_on_trans; [exact AG' | apply HMa; [lia | lia | clear - Hap Hh0; unfold apart in *; lia]]. }
          (apply (PLOOP (q, (k, v)) S M4 R' pc HE Hpc2) || apply (PLOOP (q, (k, v)) S M4 R' pc eq_refl Hpc2)); [| intros a Hn'; apply HMw; intros Ha; apply Hn'; left; lia | exact HMg |].
          - constructor.
            + exact DB'.
            + exact Q10. + exact Q22.
            + unfold HRehashModel.addr. cbn [last fst]. exact Q11.
            + exact Q15.
            + cbn [last]. unfold HRehashModel.hh, HRehashModel.hkey. cbn [fst snd]. exact Q12.
            + exact QC13. + exact QC14. + exact QC6.
            + rewrite ?HE. cbn [app]. apply Permutation_refl.
            + apply binv_start; lia.
            + discriminate.
            + cbn [app hdaddr]. eapply cellw_agree; [exact Cp1 | apply HMa; [lia | lia | unfold apart; lia] | lia | cbn; lia].
            + cbn [app]. eapply (chain_agree SEGS (Z * Z * Z)%type M1 M4); [exact (u_chain U1) |].
              intros q' k' v' Hin. destruct (HN q' k' v' Hin) as (AG4 & _ & Hr0 & Hr1). split; [eapply agree_on_sub; [exact AG4 | lia | lia] | lia].
            + intros e He. rewrite ?HE in He. destruct e as [q' [k' v']]. destruct (HN q' k' v' He) as (AG4 & _ & Hr0 & Hr1).
              destruct (u_node U1 q' k' v' He) as (_ & _ & _ & _ & Ch' & _). unfold HRehashModel.addr, HRehashModel.hkey. cbn [fst snd].
              eapply cellw_agree; [exact Ch' | eapply agree_on_sub; [exact AG4 | lia | cbn; lia] | lia | cbn; lia].
            + intros e He. rewrite ?HE in He. destruct e as [q' [k' v']]. destruct (HN q' k' v' He) as (AG4 & _ & Hr0 & Hr1). unfold HRehashModel.addr. cbn [fst].
              eapply agree_on_sub; [exact AG4 | lia | lia].
            + intros i Hi. unfold HRehashModel.hh, HRehashModel.hkey. cbn [fst snd]. fold h0. destruct (Z.eqb_spec i h0) as [->|Hne].
              * rewrite HM4. unfold cell8. cellpeel.
              * eapply cellw_agree; [exact (Hz i Hi) | apply HMa; [lia | lia | unfold apart; lia] | lia | cbn; lia].
            + intros i Hi. apply HMg. apply DEFp. exact Hi.
            + intros i Hi. apply HMg. apply HDEF. exact Hi.
            + intros e He i Hi. rewrite ?HE in He. destruct e as [q' [k' v']]. destruct (HN q' k' v' He) as (_ & Hlv' & _). unfold HRehashModel.addr. cbn [fst].
              apply HMg. destruct (live_facts' A2 M3 model2 q' 32 AI Hlv') as (_ & _ & _ & Hall). exact (proj2 (Hall (q' + i) ltac:(lia))).
            + intros e He. rewrite ?HE in He. destruct e as [q' [k' v']]. exact (proj1 (proj2 (HN q' k' v' He))).
            + exact Hpl.
          - eapply (ai_frame MI); [exact AI | | exact HMg | reflexivity | reflexivity].
            intros a Ho. pose proof (u64_range a). apply HMw. intros Ha.
            destruct (live_facts' A2 M3 model2 p (8 * n) AI Hpl) as (_ & _ & _ & Hall). exact (proj1 (Hall (bv_unsigned a) ltac:(lia)) Ho). }

        Ltac scD Hrm Hba Hr Hpc' :=
          split_scs;
          first [ lazymatch goal with
                  | |- sc_denot _ _ _ (SCBr true BC_GEU _ (ELit 2)) => apply Hpc'; rewrite popcD_env; evs; rewrite branch_geu_lit_r by lia; bool_lia
                  | |- sc_denot _ _ _ (SCBr false BC_LTU (EVar 36) _) =>
                      eapply sc_trap_notlt; [evs; reflexivity | evs; nrm Hrm Hba; rewrite w_mul by lia; reflexivity | lia | lia | lia]
                  end
                | scq Hrm Hba Hr ].
        Ltac finD Hrm Hba FIN HR' Hpop DB :=
          eapply FIN;
          [ evs; nrm Hrm Hba; rewrite ?w_mul, ?w_add, ?v_addi_Z by lia; rewrite ?Z.add_0_r; first [reflexivity | f_equal; lia]
          | dbase_from HR' DB
          | let Q := fresh in rreg HR' 10%bv Q; exact Q
          | let Q := fresh in rreg HR' 22%bv Q; exact Q
          | let Q := fresh in rreg HR' 11%bv Q; exact Q
          | let Q := fresh in rreg HR' 15%bv Q; rewrite Q; reflexivity
          | let Q := fresh in rreg HR' 12%bv Q; rewrite Q; nrm Hrm Hba; first [reflexivity | f_equal; lia]
          | lazymatch type of HR' with regs_ok ?E' _ _ => rewrite (eq_trans (HR' 13%bv) (popcD_env E')); evs; exact Hpop end
          | let Q := fresh in rreg HR' 14%bv Q; rewrite Q; rewrite ?w_add, ?w_addm, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]
          | let Q := fresh in rreg HR' 6%bv Q; exact Q
          | ].
        destruct (Z.lt_ge_cases k n) as [Hlt | Hge].
        + assert (Hxh : k = h0) by (rewrite <- Hh; symmetry; apply Z.mod_small; lia).
          assert (Hrm : mul_div M_REMU (Z_to_bv 64 k) (Z_to_bv 64 n) = Z_to_bv 64 h0) by (rewrite w_remu by lia; f_equal; exact Hh).
          assert (Hba : alu64 ALU_ADD (Z_to_bv 64 p) (mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 k)) = Z_to_bv 64 (p + 8 * h0)) by (rewrite w_mul, w_add by lia; f_equal; lia).
          destruct S as [|x' S''].
          * xruns HR HK 100%nat STOPSD (SCR [false; false; true; true; false; false] [EVar 40; EVar 37; EVar 38; EVar 40; EVar 39] []) 50%N; [scD Hrm Hba Hh0 Hpc'|].
            finD Hrm Hba FIN HR' Hpop DB. left. split; reflexivity.
          * destruct x' as [xa' xv']. destruct (u_node U1 xa' (fst xv') (snd xv') ltac:(right; left; destruct xv'; reflexivity)) as (_ & Hx'0 & Hx'1 & _). cbn [hdaddr fst] in *.
            xruns HR HK 100%nat STOPSD (SCR [false; false; true; true; false; true] [EVar 40; EVar 37; EVar 38; EVar 40; EVar 39] []) 50%N; [scD Hrm Hba Hh0 Hpc'|].
            finD Hrm Hba FIN HR' Hpop DB. right. split; [reflexivity | discriminate].
        + assert (Hrm : mul_div M_REMU (Z_to_bv 64 k) (Z_to_bv 64 n) = Z_to_bv 64 h0) by (rewrite w_remu by lia; f_equal; exact Hh).
          assert (Hba : alu64 ALU_ADD (Z_to_bv 64 p) (mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 h0)) = Z_to_bv 64 (p + 8 * h0)) by (rewrite w_mul, w_add by lia; reflexivity).
          destruct S as [|x' S''].
          * xruns HR HK 100%nat STOPSD (SCR [false; false; true; false; false; false] [EVar 40; EVar 37; EVar 38; EVar 40; EVar 39] []) 50%N; [scD Hrm Hba Hh0 Hpc'|].
            finD Hrm Hba FIN HR' Hpop DB. left. split; reflexivity.
          * destruct x' as [xa' xv']. destruct (u_node U1 xa' (fst xv') (snd xv') ltac:(right; left; destruct xv'; reflexivity)) as (_ & Hx'0 & Hx'1 & _). cbn [hdaddr fst] in *.
            xruns HR HK 100%nat STOPSD (SCR [false; false; true; false; false; true] [EVar 40; EVar 37; EVar 38; EVar 40; EVar 39] []) 50%N; [scD Hrm Hba Hh0 Hpc'|].
            finD Hrm Hba FIN HR' Hpop DB. right. split; [reflexivity | discriminate].
    Qed.

    Lemma relink : forall p A1 M1 A M3 model S P B M R (pc : Z),
      (pc = NT_AFTER /\ S = [] \/ pc = NT_LOOP /\ S <> []) ->
      ainv MI A M model -> mstd model -> umapx MI 32 (nval32 SEGS) A1 M1 obj bl bc ents ->
      lst p M1 P S B A M R ->
      0 < p -> p + 8 * n <= alloc_ceiling -> ~ In p (map fst (live MI Ar)) ->
      (forall a : word, ~ Wloop p (bv_unsigned a) -> M a = M3 a) -> (forall a : word, M3 a <> None -> M a <> None) ->
      (forall M' R' P' B',
          lst p M1 P' [] B' A M' R' ->
          (forall a : word, ~ Wloop p (bv_unsigned a) -> M' a = M3 a) -> (forall a : word, M3 a <> None -> M' a <> None) ->
          ainv MI A M' model ->
          srealizes SEGS (cfg fxr R' NT_AFTER M' model) K) ->
      srealizes SEGS (cfg fxr R pc M model) K.
    Proof using AC L MI ST NEW_STACK DEL_STACK fx A0 s R0 M0 model0 sp parser key bl bc w1 w2 w3 val ents K C fxr Ar Mr pn Ur.
      intros p A1 M1 A M3 model S. induction S as [|x S' IH]; intros P B M R pc Hpc AI MS U1 LS Hp0 Hpc8 Hpnew HM HG POST.
      - destruct Hpc as [[-> _] | [_ Hne]]; [| exfalso; exact (Hne eq_refl)].
        exact (POST M R P B LS HM HG AI).
      - destruct Hpc as [[_ Habs] | [-> _]]; [discriminate Habs|].
        eapply (loop_step p A1 M1 P (x :: S') B A M model R x S' eq_refl AI MS U1 LS Hp0 Hpc8 Hpnew).
        intros M' R' P' B' pc' Hpc' LS' HM' HG' AI'.
        apply (IH P' B' M' R' pc' Hpc' AI' MS U1 LS' Hp0 Hpc8 Hpnew); [| | exact POST].
        + intros a Ha. rewrite (HM' a Ha). exact (HM a Ha).
        + intros a Ha. apply HG'. apply HG. exact Ha.
    Qed.

    Lemma phaseE : forall A1 M1 A2 M3 model2 R3 p M' R',
      rst (FC p) (opsB p) p A2 M3 model2 R3 ->
      umapx MI 32 (nval32 SEGS) A1 M1 obj bl bc ents ->
      cell8 SEGS M3 obj p -> cell8 SEGS M3 (obj + 8) n -> agree_on M1 M3 (obj + 16) 24 ->
      (forall q k v, In (q, (k, v)) ents -> agree_on M1 M3 q 32 /\ In (q, 32) (live MI A2)) ->
      (forall i, 0 <= i < n -> cell8 SEGS M3 (p + 8 * i) 0) ->
      (forall a : word, ~ Wloop p (bv_unsigned a) -> M' a = M3 a) -> (forall a : word, M3 a <> None -> M' a <> None) ->
      ainv MI A2 M' model2 -> dbase R' -> getr R' 6%bv = Z_to_bv 64 (2 ^ 60) ->
      ((ents = [] /\ M' = M3) \/ (exists P' B', lst p M1 P' [] B' A2 M' R')) ->
      srealizes SEGS (cfg fxr R' NT_AFTER M' model2) K.
    Proof using AC L MI ST NEW_STACK DEL_STACK fx A0 s R0 M0 model0 sp parser key bl bc w1 w2 w3 val ents K C fxr Ar Mr pn Ur CONTD.
      ctx. intros A1 M1 A2 M3 model2 R3 p M' R' D U1 Cbl Cbc AGh Hnodes Hz HM HG AI' B' Q6' HFIN.
      destruct SPF as (Hsp16' & Hsplo & Hsphi & Hn16 & HnN & HnD & Hs1 & Hpar). pose proof ceiling_lt as Hcl. pose proof ac_bounds_lit as Hcv.
      pose proof (u_obj_hi Ur) as Hh1.
      destruct n_facts as (HnB & Hbcn & Hn28 & Hncase). clear Hncase.
      assert (Hbc0 : 0 <= bc) by (pose proof (u_bseq Ur) as HB; unfold BSEQ in HB; cbn in HB; lia).
      pose proof D as D'. destruct D' as [AI MS Hfs Hfds _ _ DEF EFF LAP Hp0 Hpc Hpal Hpl Hpnew HFoff HDEF].
      pose proof B' as DBx. destruct DBx as (B & HQ23 & HQ27 & HQ26). pose proof B as Bx. destruct Bx as (B2 & B3 & B4 & B8 & B18 & Bs).
      pose proof (u_obj_lo U1) as Hobjlo. pose proof (u_obj_hi U1) as Hobjhi.
      assert (Hn0 : 0 < n) by lia.

      assert (HMo : forall a k, 0 <= a -> a + k <= 2 ^ 47 -> (forall x, a <= x < a + k -> ~ Wloop p x) -> agree_on M3 M' a k).
      { intros a k Ha Hak Hno i Hi. apply HM. rewrite u64_of_Z by lia. apply Hno. lia. }
      assert (Hhdr_no : forall x, (obj <= x < obj + 16 \/ obj + 24 <= x < obj + 40) -> ~ Wloop p x).
      { intros x Hx [Hw|[Hw|(e & He & Hw)]]; [lia | lia |].
        destruct e as [q [k v]]. destruct (u_node U1 q k v He) as (_ & _ & _ & _ & _ & _ & _ & _ & Hap & _). unfold apart in Hap. cbn in Hw. lia. }
      assert (Hstk_no : forall x, sp - NTS <= x < sp -> ~ Wloop p x).
      { intros x Hx [Hw|[Hw|(e & He & Hw)]]; [lia | lia |].
        destruct e as [q [k v]]. destruct (Hnodes q k v He) as [_ Hlv]. destruct (live_facts' A2 M3 model2 q 32 AI Hlv) as (_ & _ & Hqc & _). cbn in Hw. lia. }

      assert (HU : exists ents', Permutation ents' ents /\ umapx MI 32 (nval32 SEGS) A2 M' obj p n ents').
      { destruct HFIN as [[HE HM'] | (P' & Bk & LS)].
        - exists (@nil lent). subst M'. split; [rewrite ?HE; apply Permutation_refl|].
          pose proof (u_hdr U1) as HD. rewrite ?HE in HD. destruct HD as [_ _ Cp1 Csz Cmlf _].
          constructor; try (intros; exfalso; assumption).
          + constructor; [exact Cbl | exact Cbc | | | | exact HDEF].
            * eapply cellw_agree; [exact Cp1 | eapply agree_on_sub; [exact AGh | lia | cbn; lia] | lia | cbn; lia].
            * eapply cellw_agree; [exact Csz | eapply agree_on_sub; [exact AGh | lia | cbn; lia] | lia | cbn; lia].
            * eapply cellw_agree; [exact Cmlf | eapply agree_on_sub; [exact AGh | lia | cbn; lia] | lia | cbn; lia].
          + exact (u_obj_al U1). + exact Hobjlo. + exact Hobjhi. + exact HnB.
          + unfold Zlength. cbn. lia.
          + right. split; [lia | exact Hpl].
          + exact Hpal. + intros _; exact Hp0. + lia. + intros _. unfold apart. lia.
          + intros i Hi. exists 0. split; [exact (Hz i Hi) | left; reflexivity].
          + constructor.
          + exact I.
        - exists P'. destruct LS as [_ _ _ _ _ _ _ _ _ PERM BI HP Cp1 CH HASH TAIL BK DEFp DEFh DEFn LIVE PLIVE].
          rewrite app_nil_r in PERM, Cp1, CH.
          assert (Hnoty : forall P1 y z P2, P' = P1 ++ y :: z :: P2 -> addr y <> snt).
          { intros P1 y z P2 HP' Heq. assert (Hin : In y ents) by (eapply Permutation_in; [exact PERM | rewrite HP'; apply in_app_iff; right; left; reflexivity]).
            destruct y as [q [k v]]. destruct (u_node U1 q k v Hin) as (_ & Hq0 & _ & _ & _ & _ & _ & _ & Hap & _). unfold apart in Hap. cbn in Heq. lia. }
          split; [exact PERM|].
          pose proof (u_hdr U1) as HD. destruct HD as [_ _ _ Csz Cmlf _].
          constructor.
          + constructor; [| | exact Cp1 | | | exact DEFh].
            * eapply cellw_agree; [exact Cbl | apply HMo; [lia | lia | intros x Hx; apply Hhdr_no; lia] | lia | cbn; lia].
            * eapply cellw_agree; [exact Cbc | apply HMo; [lia | lia | intros x Hx; apply Hhdr_no; lia] | lia | cbn; lia].
            * rewrite (Permutation_length PERM : length P' = length ents) || (unfold Zlength; rewrite (Permutation_length PERM)).
              eapply cellw_agree; [exact Csz | eapply agree_on_trans; [eapply agree_on_sub; [exact AGh | lia | cbn; lia] | apply HMo; [lia | cbn; lia | intros x Hx; apply Hhdr_no; cbn in Hx; lia]] | lia | cbn; lia].
            * eapply cellw_agree; [exact Cmlf | eapply agree_on_trans; [eapply agree_on_sub; [exact AGh | lia | cbn; lia] | apply HMo; [lia | cbn; lia | intros x Hx; apply Hhdr_no; cbn in Hx; lia]] | lia | cbn; lia].
          + exact (u_obj_al U1). + exact Hobjlo. + exact Hobjhi. + exact HnB.
          + unfold Zlength. rewrite (Permutation_length PERM). pose proof (u_load U1) as HL. unfold Zlength in HL. lia.
          + right. split; [lia | exact PLIVE].
          + exact Hpal. + intros _; exact Hp0. + lia. + intros _. unfold apart. lia.
          + intros i Hi. exists (Bk i). split; [exact (BK i Hi)|].
            destruct (binv_weak (Z * Z * Z)%type n snt P' Bk i BI Hi Hnoty) as [Hb | [Hb | [Hb (x & P'' & HP' & Hx)]]]; [left; exact Hb | right; left; exact Hb | right; right].
            split; [exact Hb|]. split; [rewrite HP'; discriminate|]. rewrite HP'. destruct x as [q [k v]]. cbn. symmetry. exact Hx.
          + apply (proj2 (base.NoDup_ListNoDup _)). exact (perm_nodup _ _ _ U1 PERM).
          + exact CH.
          + intros q k v Hin. assert (Hine : In (q, (k, v)) ents) by (eapply Permutation_in; [exact PERM | exact Hin]).
            destruct (u_node U1 q k v Hine) as (_ & Hq0 & Hq1 & Hqal & _ & C4 & Hk & Hnv & Hap & _).
            pose proof (TAIL _ Hine) as TL. cbn in TL.
            split; [exact (LIVE _ Hine)|]. split; [exact Hq0|]. split; [exact Hq1|]. split; [exact Hqal|].
            split; [exact (HASH _ Hine)|].
            split; [eapply cellw_agree; [exact C4 | eapply agree_on_sub; [exact TL | lia | cbn; lia] | lia | cbn; lia]|].
            split; [exact Hk|].
            split; [eapply nval32_agree; [exact Hnv | eapply agree_on_sub; [exact TL | lia | lia] | lia | lia]|].
            split; [exact Hap|].
            intros _. apply apart_sym. apply (p_node_apart p A2 M' model2 (q, (k, v)) AI' PLIVE Hpnew (LIVE _ Hine) Hine).
          + intros q q' Hq Hq' Hne. apply (u_napart U1); [| | exact Hne].
            * apply in_map_iff in Hq. destruct Hq as (e & <- & He). apply in_map. eapply Permutation_in; [exact PERM | exact He].
            * apply in_map_iff in Hq'. destruct Hq' as (e & <- & He). apply in_map. eapply Permutation_in; [exact PERM | exact He]. }
      destruct HU as (ents' & PERM' & U').

      assert (EFF' : eff MI Ar A2 Mr M' W (fun a => FC p a \/ Wloop p a)).
      { eapply eff_trans; [exact EFF | | intros a Ha; eapply hi_unowned'; [exact AI' | unfold W_of, Wnt in Ha; cbn in Ha; lia]].
        eapply eff_store; [| exact HG]. intros x HF _. apply HM. exact HF. }
      assert (FOFF' : forall a, FC p a \/ Wloop p a -> ~ in_ranges (ly_img L) a).
      { intros a [Ha | [Ha | [Ha | (e & He & Ha)]]] Himg; pose proof (HLimg_lo _ Himg).
        - exact (HFoff a Ha Himg). - exact (live_offimg' A2 M3 model2 p (8 * n) a AI Hpl Ha Himg). - lia.
        - destruct e as [q [k v]]. destruct (Hnodes q k v He) as [_ Hlv]. cbn in Ha.
          exact (live_offimg' A2 M3 model2 q 32 a AI Hlv ltac:(lia) Himg). }
      apply (CONTD A2 R' M' model2 p ents' AI' MS Hfs Hfds B').
      - exact U'.
      - exact PERM'.
      - exact LAP.
      - eapply eff_weaken; [exact EFF'|].
        intros a [[[Ha | [Ha | Ha]] | Ha] | [Ha | [Ha | (e & He & Ha)]]].
        + right. right. left. split; [lia | exact Ha].
        + left. left. lia.
        + left. right. left. exact Ha.
        + left. left. lia.
        + right. right. left. split; [lia | exact Ha].
        + left. left. lia.
        + left. right. right. exists (addr e). split; [apply in_map; exact He | lia].
      - eapply defined_agree; [exact DEF | apply HMo; [lia | lia | intros x Hx; apply Hstk_no; lia]].
      - exact Q6'.
    Qed.

    Theorem rehash_inl : srealizes SEGS (cfg fxr Rr NT_NEWE Mr modelr) K.
    Proof using AC L MI ST NEW_STACK DEL_STACK fx A0 s R0 M0 model0 sp parser key bl bc w1 w2 w3 val ents K C fxr Ar Mr modelr Rr pn AIr MSr Hfsr Hfdsr SXr RCr OSXr Br Q22r Q10r Q1r Ur DEFWr FRr SPLr ROOMr CONTD.
      apply phaseA. intros A1 M1 model1 R1 p AI1 MS1 Hfs1 Hfds1 SX1 B1 G10 G22 DEF1 Hp0 Hpc Hpal LADD EFF1 U1.
      assert (Hpl : In (p, 8 * n) (live MI A1)) by (rewrite (proj1 LADD); left; reflexivity).
      assert (D1 : rst (FA p) [LAdd p (8 * n)] p A1 M1 model1 R1).
      { constructor; try assumption.
        - exists (live MI A1). split; [exact LADD | reflexivity].
        - exact (proj2 LADD).
        - intros a Ha. exact (live_offimg' A1 M1 model1 p (8 * n) a AI1 Hpl Ha).
        - exact (h_def (u_hdr U1)). }
      apply (phaseB A1 M1 model1 R1 p D1 G10 U1). intros A2 M2 model2 R2 D2 G24 Cbl AG2 Hn2.
      apply (phaseC A1 M1 A2 M2 model2 R2 p D2 G24 U1 Cbl AG2 Hn2). intros M3 R3 D3 G10' G15' G6' Cbl3 Cbc3 AG3 Hn3 Hz3.
      apply (phaseD A1 M1 A2 M3 model2 R3 p D3 G10' G15' G6' U1 AG3 Hn3 Hz3).
      - intros HE R4 B4 Q64.
        apply (phaseE A1 M1 A2 M3 model2 R3 p M3 R4 D3 U1 Cbl3 Cbc3 AG3 Hn3 Hz3); [intros a _; reflexivity | intros a Ha; exact Ha | exact (r_ai _ _ _ _ _ _ _ D3) | exact B4 | exact Q64 |].
        left. split; [exact HE | reflexivity].
      - intros e S M4 R4 pc HE Hpc' LS HM4 HG4 AI4.
        apply (relink p A1 M1 A2 M3 model2 S [e] _ M4 R4 pc Hpc' AI4 (r_ms _ _ _ _ _ _ _ D3) U1 LS (r_p0 _ _ _ _ _ _ _ D3) (r_pc _ _ _ _ _ _ _ D3) (r_pnew _ _ _ _ _ _ _ D3) HM4 HG4).
        intros M' R' P' B' LS' HM' HG' AI'.
        apply (phaseE A1 M1 A2 M3 model2 R3 p M' R' D3 U1 Cbl3 Cbc3 AG3 Hn3 Hz3 HM' HG' AI' (l_regs _ _ _ _ _ _ _ _ LS') (l_c6 _ _ _ _ _ _ _ _ LS')).
        right. exists P', B'. exact LS'.
    Qed.

  End Reh.
  #[local] Abbreviation dbase := (HNtDU1C.dbase L R0 sp parser key w3).
End NtD.

Abbreviation loop_step := HNtDU1B.loop_step.

Abbreviation del_call := HNtDU1C.del_call.
Abbreviation dbase := HNtDU1C.dbase.
Abbreviation n_facts := HNtDU1C.n_facts.
Abbreviation iroc_r := HNtDU1C.iroc_r.
Abbreviation tbl_blocks_live := HNtDU1C.tbl_blocks_live.
Abbreviation foot_offimg := HNtDU1C.foot_offimg.
Abbreviation win_r := HNtDU1C.win_r.
Abbreviation phaseA := HNtDU1C.phaseA.
Abbreviation dbase_kept := HNtDU1C.dbase_kept.
Abbreviation rst := HNtDU1C.rst.
Abbreviation RST := HNtDU1C.RST.
Abbreviation r_ai := HNtDU1C.r_ai.
Abbreviation r_ms := HNtDU1C.r_ms.
Abbreviation r_fs := HNtDU1C.r_fs.
Abbreviation r_fds := HNtDU1C.r_fds.
Abbreviation r_regs := HNtDU1C.r_regs.
Abbreviation r_s6 := HNtDU1C.r_s6.
Abbreviation r_def := HNtDU1C.r_def.
Abbreviation r_eff := HNtDU1C.r_eff.
Abbreviation r_lap := HNtDU1C.r_lap.
Abbreviation r_p0 := HNtDU1C.r_p0.
Abbreviation r_pc := HNtDU1C.r_pc.
Abbreviation r_pal := HNtDU1C.r_pal.
Abbreviation r_plive := HNtDU1C.r_plive.
Abbreviation r_pnew := HNtDU1C.r_pnew.
Abbreviation r_Foff := HNtDU1C.r_Foff.
Abbreviation r_hdef := HNtDU1C.r_hdef.
Abbreviation FA := HNtDU1C.FA.
Abbreviation FB := HNtDU1C.FB.
Abbreviation opsB := HNtDU1C.opsB.
Abbreviation cell_via := HNtDU1C.cell_via.
Abbreviation frame_via := HNtDU1C.frame_via.
Abbreviation f2_via := HNtDU1C.f2_via.
Abbreviation p_apart := HNtDU1C.p_apart.
Abbreviation phaseB := HNtDU1C.phaseB.
Abbreviation FC := HNtDU1C.FC.
Abbreviation zloop := HNtDU1C.zloop.
Abbreviation phaseC := HNtDU1C.phaseC.
Abbreviation d0 := HNtDU1C.d0.
Abbreviation sc_disjZ := HNtDU1C.sc_disjZ.
Abbreviation lst := HNtDU1C.lst.
Abbreviation LST := HNtDU1C.LST.
Abbreviation l_regs := HNtDU1C.l_regs.
Abbreviation l_x10 := HNtDU1C.l_x10.
Abbreviation l_x22 := HNtDU1C.l_x22.
Abbreviation l_x11 := HNtDU1C.l_x11.
Abbreviation l_x15 := HNtDU1C.l_x15.
Abbreviation l_x12 := HNtDU1C.l_x12.
Abbreviation l_c13 := HNtDU1C.l_c13.
Abbreviation l_c14 := HNtDU1C.l_c14.
Abbreviation l_c6 := HNtDU1C.l_c6.
Abbreviation l_perm := HNtDU1C.l_perm.
Abbreviation l_binv := HNtDU1C.l_binv.
Abbreviation l_P := HNtDU1C.l_P.
Abbreviation l_p1 := HNtDU1C.l_p1.
Abbreviation l_chain := HNtDU1C.l_chain.
Abbreviation l_hash := HNtDU1C.l_hash.
Abbreviation l_tail := HNtDU1C.l_tail.
Abbreviation l_bkt := HNtDU1C.l_bkt.
Abbreviation l_defp := HNtDU1C.l_defp.
Abbreviation l_defh := HNtDU1C.l_defh.
Abbreviation l_defn := HNtDU1C.l_defn.
Abbreviation l_live := HNtDU1C.l_live.
Abbreviation l_plive := HNtDU1C.l_plive.
Abbreviation Wloop := HNtDU1C.Wloop.
Abbreviation ent_facts := HNtDU1C.ent_facts.
Abbreviation last_any := HNtDU1C.last_any.
Abbreviation hda := HNtDU1C.hda.
Abbreviation lnk := HNtDU1C.lnk.
Abbreviation lnk_chain := HNtDU1C.lnk_chain.
Abbreviation hd_app := HNtDU1C.hd_app.
Abbreviation hdaddr_hda := HNtDU1C.hdaddr_hda.
Abbreviation lnk_app := HNtDU1C.lnk_app.
Abbreviation last_app_ne := HNtDU1C.last_app_ne.
Abbreviation lnk_agree := HNtDU1C.lnk_agree.
Abbreviation perm_nodup := HNtDU1C.perm_nodup.
Abbreviation nodup_app_ne := HNtDU1C.nodup_app_ne.
Abbreviation last_in := HNtDU1C.last_in.
Abbreviation apart_sub := HNtDU1C.apart_sub.
Abbreviation apart_sym := HNtDU1C.apart_sym.
Abbreviation splice_facts := HNtDU1C.splice_facts.
Abbreviation nodes_apart := HNtDU1C.nodes_apart.
Abbreviation p_node_apart := HNtDU1C.p_node_apart.

Arguments rehash_inl {AC L MI ST NEW_STACK DEL_STACK fx A0 s R0 M0 model0 sp parser key bl bc w1 w2 w3 val ents K} C fxr Ar Mr modelr Rr pn.
Arguments dbase {L R0 sp parser key w3} pn R.
End HNtDU1.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac WalkTac StoreOk MemSplit Hoare ShapeAlg SRealizes MmapSim
  RefMemcpyLib LibIface LibEff LibBudget FPSteps SumMemsetLib SymExec3 SymExec3Sound SymRun3.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HLib HRepFacts HStmts HStmtsU1 HWord HUbsan HConstsU1 HCommonU1 HFpu HFpuU1 HFindU1 HBlkU1 HNtCtxU1. Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HNtAU1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HNtAU1.HNtSU1. From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HNtAU1 HNtFU1 HNtRU1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HNtU1.HNtDU1. From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import U1_code_689b8_69044.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition STOPSG : list Z := [NT_INS; NT_TRAP].

#[local] Notation ent := (Z * (Z * (Z * Z * Z)))%type.

Section Nt.
Context {AC : AllocCeiling}.

  Variables (L : Layout) (MI : MallocIface SEGS L) (ST : StaticsIface SEGS L) (NEW_STACK DEL_STACK : Z).
  Variables (fx : FPState) (A0 : AS MI) (s : LibIface.SX ST) (R0 : bvmap 5 word) (M0 : mem) (model0 : Model).
  Variables (sp parser key bl bc w1 w2 w3 : Z) (val : Z * Z * Z) (ents : list (Z * (Z * (Z * Z * Z)))) (K : TSet).
  Variable C : @ntctx AC L MI ST NEW_STACK DEL_STACK fx A0 s R0 M0 model0 sp parser key bl bc w1 w2 w3 val ents K.
  #[local] Abbreviation NTS := (NT_STACK NEW_STACK DEL_STACK).
  #[local] Abbreviation cfg fx R pc M model := (mkCfg (@mkst fx R (Z_to_bv 64 pc) M (seg_rom SEGS)) model).
  #[local] Abbreviation live_facts' := (live_facts L MI).
  #[local] Abbreviation live_offimg' := (live_offimg L MI).
  #[local] Abbreviation agree_above_via_eff' := (agree_above_via_eff L MI (c_HLimg_lo C) (c_HLrw_img C) (c_HLerr_rw C)).
  #[local] Abbreviation img_ro_clear_via_eff' := (img_ro_clear_via_eff L MI (c_HLimg_lo C) (c_HLerr_rw C)).
  #[local] Abbreviation sx_inv_via_eff' := (sx_inv_via_eff L MI ST (c_HLimg_lo C) (c_HLrw_img C) (c_HLrelro_img C) (c_HLrw_relro C) (c_HLerr_rw C)).
  #[local] Abbreviation ro_clear_via_eff' := (ro_clear_via_eff L MI (c_HLimg_lo C) (c_HLerr_rw C)).
  #[local] Abbreviation agree_block_via_eff' := (agree_block_via_eff L MI (c_HLrw_img C) (c_HLerr_rw C)).
  #[local] Abbreviation own_sx_via_eff' := (own_sx_via_eff L MI ST (c_HLrw_img C)).
  #[local] Abbreviation hi_unowned' := (hi_unowned L MI (c_HLimg_lo C) (c_HLrw_img C)).
  #[local] Abbreviation obj := (parser + 136).
  #[local] Abbreviation sent := (parser + 152).
  #[local] Abbreviation W := (Wnt NEW_STACK DEL_STACK sp).
  #[local] Abbreviation base_ok := (nt_base_ok L R0 sp parser).
  #[local] Abbreviation pframe := (nt_pframe sp parser key w1 w2).
  #[local] Abbreviation fbase := (nt_fbase fx).
  #[local] Abbreviation SPF := (sp_facts C).
  #[local] Abbreviation BCF := (bc_facts C).
  #[local] Abbreviation VF := (val_facts C).
  #[local] Ltac ctx := ntctx_pose C.

  #[local] Abbreviation core := (@HNtAU1.core AC L MI ST NEW_STACK DEL_STACK A0 s R0 model0 sp parser key w1 w2).
  #[local] Abbreviation nst := (@HNtAU1.nst AC L MI ST NEW_STACK DEL_STACK A0 s R0 M0 model0 sp parser key bl bc w1 w2 w3 ents).
  #[local] Abbreviation rcall := (@HNtRU1.rcall AC L MI ST NEW_STACK DEL_STACK A0 s R0 M0 model0 sp parser key bl bc w1 w2 w3 ents).
  #[local] Abbreviation dbase := (@HNtDU1.dbase L R0 sp parser key w3).

  Ltac scE Hland Hj DEFp HDEF DEFbl :=
    split_scs;
    lazymatch goal with
    | |- sc_denot _ _ _ (SCStoreOk _ _) =>
        eapply sc_storeok; [evs; nrw Hj; reflexivity | lia | cbn [a_off]; lia | cbn [a_off]; lia
                          | cbn [a_off]; rewrite ?Z.add_0_r;
                            first [ lazymatch goal with |- defined _ ?a _ => match goal with D : defined _ a _ |- _ => eapply (defined_sub _ _ _ _ _ D); lia end end
                                  | eapply (defined_sub _ _ _ _ _ HDEF); lia | eapply (defined_sub _ _ _ _ _ DEFp); lia | eapply (defined_sub _ _ _ _ _ DEFbl); lia] ]
    | |- sc_denot _ _ _ (SCFlat _ _) => eapply sc_flat; [evs; nrw Hj; reflexivity | lia | cbn [a_off]; lia | lia | cbn [a_off]; lia]
    | |- sc_denot _ _ _ (SCBr _ _ _ _) => cbn [sc_denot]; evs; nrw Hj; rewrite ?Hland; rewrite ?br_ne, ?br_eq, ?br_ltu, ?br_geu, ?br_eq_sxw, ?br_ne_sxw by lia; bool_lia
    | |- sc_denot _ _ _ (SCReadBase _ _ _ _) =>
        first [ match goal with H : cellw _ _ _ _ _ |- _ =>
                  eapply (sc_read_cellw _ _ _ _ _ _ _ _ H); [first [apply N.le_refl | cbn; lia] | evs; nrw Hj; first [reflexivity | f_equal; lia] | evs; reflexivity] end
              | sc_auto1 ]
    | |- _ => sc_auto1
    end.

  Lemma phaseR2 : forall (fx2 : FPState) p A M model R,
    fbase fx2 -> rcall p A M model R -> srealizes SEGS (cfg fx2 R NT_NEWE M model) K.
  Proof using AC L MI ST NEW_STACK DEL_STACK fx A0 s R0 M0 model0 sp parser key bl bc w1 w2 w3 val ents K C.
    ctx. intros fx2 p A M model R FB RCL.
    destruct SPF as (Hsp16' & Hsplo & Hsphi & Hn16 & HnN & HnD & Hs1 & Hpar). pose proof ceiling_lt as Hcl. pose proof ac_bounds_lit as Hcv.
    pose proof (u_obj_lo U0) as Hobjlo. pose proof (u_obj_hi U0) as Hobjhi.
    destruct BCF as (HbB & Hbcr & Hload & Hsz0). pose proof (proj1 (nu_key _ _ _ _ _ _ _ _ _ _ _ NF)) as Hkr. cbn in Hkr.
    destruct (bseq_next_facts bc HbB Hlast) as (HnB & Hbcn & Hn28 & Hncase).
    set (n := bseq_next bc) in *.
    destruct RCL as [AI MS Hfs Hfds SX B Q23 Q27 Q22 Q26 Q10 Q1 FR DEF0 DEFW SPILL Hp0 Hpc Hpal Hpl Hpnew Cnh Cnk DEFp EFF LADD U Hgrow RC].
    pose proof B as B'. destruct B' as (B2 & B3 & B4 & B8 & B18 & Bs).
    assert (FOFF : forall a, (p <= a < p + 32 \/ sp <= a < sp + 8) -> ~ in_ranges (ly_img L) a).
    { intros a [Ha | Ha] Hi; [exact (live_offimg' A M model p 32 a AI Hpl Ha Hi) | pose proof (HLimg_lo _ Hi); lia]. }
    pose proof (own_sx_via_eff' A0 A M0 M W _ EFF Hown_sx FOFF) as OSX.
    pose proof FR as FR0. destruct FR0 as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8).
    eapply (rehash_inl C fx2 A M model R p AI MS Hfs Hfds SX RC OSX (conj B (conj Q23 (conj Q27 Q26))) Q22 Q10 Q1 U DEFW FR SPILL).
    - pose proof (ROOM2 Hgrow) as RM. unfold roomL in RM |- *. rewrite (proj1 LADD). cbn [count_class_f big_bytes_f] in RM |- *.
      rewrite (ef_caps _ _ _ _ _ _ _ _ _ EFF), (ef_bigcap _ _ _ _ _ _ _ _ _ EFF). exact RM.
    -
      intros A' R' M' model' bl' ents' AI' MS' Hfs' Hfds' DB' U' PERM' LAP' EFF' DEFW' Q6'.
      destruct DB' as (BR & Q23' & Q27' & Q26'). pose proof BR as BR'. destruct BR' as (C2 & C3 & C4 & C8 & C18 & Cs).
      assert (Hlen : Zlength ents' = Zlength ents) by (unfold Zlength; rewrite (Permutation_length PERM'); reflexivity).
      pose proof (u_bseq U') as HnB'. pose proof (u_bl_lo U' ltac:(lia)) as Hbl'0. pose proof (u_bl_hi U') as Hbl'1.

      destruct LAP' as (lv1 & LADD' & LAP2).
      assert (Hpbl' : p <> bl') by (intros ->; apply (proj2 LADD'); apply (in_map fst _ (bl', 32)); exact Hpl).
      assert (Hpl' : In (p, 32) (live MI A')).
      { assert (H1 : In (p, 32) lv1) by (rewrite (proj1 LADD'); right; exact Hpl).
        destruct (Z.eqb_spec bc 0) as [Hb0|Hb1]; cbn [lapply] in LAP2.
        - rewrite LAP2. exact H1.
        - destruct LAP2 as (lv2 & DELb & ->). apply (proj2 (DELb p 32)). split; [exact H1|].
          intros ->. apply Hpnew. destruct (u_blive U0) as [[? ?]|[_ Hin]]; [lia|]. apply (in_map fst _ (bl, 8 * bc)). exact Hin. }
      assert (Hpa' : forall q m, In (q, m) (umap_blocks 32 bl' n ents') -> apart p 32 q m).
      { intros q m Hq. unfold umap_blocks in Hq. apply in_app_iff in Hq. destruct Hq as [Hq | Hq].
        - destruct (Z.eqb_spec n 0); [destruct Hq|]. destruct Hq as [Hq|[]]. injection Hq as <- <-.
          destruct (u_blive U') as [[? ?]|[_ Hin]]; [lia|].
          exact (ai_live_disjoint MI A' M' model' p 32 bl' (8 * n) AI' Hpl' Hin Hpbl').
        - apply in_map_iff in Hq. destruct Hq as ([q' [k v]] & Hq' & Hin). cbn in Hq'. injection Hq' as <- <-.
          assert (Hin0 : In (q', (k, v)) ents) by (eapply Permutation_in; [exact PERM' | exact Hin]).
          apply (ai_live_disjoint MI A' M' model' p 32 q' 32 AI' Hpl' (proj1 (u_node U' q' k v Hin))).
          intros <-. apply Hpnew. apply (in_map fst _ (p, 32)). exact (proj1 (u_node U0 p k v Hin0)). }
      assert (HFp : forall a, umap_foot 32 obj bl bc ents a \/ umap_foot 32 obj bl' n ents' a -> ~ (p <= a < p + 32)).
      { intros a [Ha | Ha]; [exact (foot_apart_new C A M model p 32 a AI LADD Ha)|].
        intros Hpa. destruct (umap_foot_hb 32 obj bl' n ents' a Ha) as [Hh | ([q m] & Hq & Hqa)]; [lia|]. cbn in Hqa.
        pose proof (Hpa' q m Hq) as Hap. unfold apart in Hap.
        assert (Hm : 0 < m).
        { unfold umap_blocks in Hq. apply in_app_iff in Hq. destruct Hq as [Hq|Hq].
          - destruct (Z.eqb_spec n 0); [destruct Hq|]. destruct Hq as [Hq|[]]. injection Hq as <- <-. lia.
          - apply in_map_iff in Hq. destruct Hq as (e & He & _). injection He as _ <-. lia. }
        lia. }
      assert (Hflh : forall a, umap_foot 32 obj bl bc ents a \/ umap_foot 32 obj bl' n ents' a -> a + 1 <= alloc_ceiling \/ obj <= a < obj + 40).
      { assert (FLH : forall Ax Mx modelx blx bcx entsx a, ainv MI Ax Mx modelx -> umapx MI 32 (nval32 SEGS) Ax Mx obj blx bcx entsx ->
                      umap_foot 32 obj blx bcx entsx a -> a + 1 <= alloc_ceiling \/ obj <= a < obj + 40).
        { intros Ax Mx modelx blx bcx entsx a AIx Ux [Hh | [[Hbc Hb] | (q & Hq & Hqa)]]; [right; exact Hh | left | left].
          - destruct (u_blive Ux) as [[? ?]|[_ Hin]]; [lia|]. destruct (live_facts' Ax Mx modelx blx (8 * bcx) AIx Hin) as (_ & _ & Hc & _). lia.
          - apply in_map_iff in Hq. destruct Hq as ([q' [k v]] & Hq' & Hin). cbn in Hq'. subst q'.
            destruct (live_facts' Ax Mx modelx q 32 AIx (proj1 (u_node Ux q k v Hin))) as (_ & _ & Hc & _). lia. }
        intros a [Hf | Hf]; [exact (FLH A M model bl bc ents a AI U Hf) | exact (FLH A' M' model' bl' n ents' a AI' U' Hf)]. }
      assert (AGp : agree_on M M' p 32).
      { eapply (agree_block_via_eff' A A' M M' model model'); [exact EFF' | exact AI | exact AI' | exact Hpl | exact Hpl' | | cbn; lia].
        intros a Ha Hf. exact (HFp a Hf Ha). }
      assert (AGa : forall a k, sp <= a -> a + k <= sp + 264 -> 0 <= k -> (forall i, 0 <= i < k -> ~ owned MI A (a + i)) -> defined M a k -> agree_on M M' a k).
      { intros a k Ha Hak Hk Hown Hdef. eapply (agree_above_via_eff' A A' M M' _ _ a k sp EFF'); [lia | cbn; lia | lia | lia | lia | exact Hown | exact Hdef |].
        intros i Hi Hf. destruct (Hflh _ Hf); lia. }
      assert (Hhiown : forall a k i, alloc_ceiling <= a -> 0 <= i < k -> ~ owned MI A (a + i)) by (intros a k i Ha Hi; eapply hi_unowned'; [exact AI | lia]).
      assert (AGc : forall a v, cell8 SEGS M a v -> sp <= a -> a + 8 <= sp + 264 -> cell8 SEGS M' a v).
      { intros a v F Ha1 Ha2. eapply cellw_agree; [exact F | | lia | cbn; lia].
        apply AGa; [lia | lia | lia | intros i Hi; apply (Hhiown a 8 i); lia | exact (cellw_high_defined M a 8 _ F ltac:(lia) ltac:(cbn; lia))]. }
      assert (FR' : pframe M').
      { split; [| split; [|split; [|split; [|split; [|split; [|split]]]]]]; try (apply AGc; [assumption | lia | lia]).
        eapply cellw_agree; [exact F1 | | lia | cbn; lia].
        apply AGa; [lia | lia | lia | intros i Hi; apply (Hhiown (sp + 260) 4 i); lia | exact (cellw_high_defined M (sp + 260) 4 _ F1 ltac:(lia) ltac:(cbn; lia))]. }
      assert (EFF2 : eff MI A0 A' M0 M' W (fun a => (p <= a < p + 32 \/ sp <= a < sp + 8) \/ (umap_foot 32 obj bl bc ents a \/ umap_foot 32 obj bl' n ents' a))).
      { eapply eff_trans; [exact EFF | exact EFF' | intros a Ha; eapply hi_unowned'; [exact AI' | unfold W_of, Wnt in Ha; cbn in Ha; lia]]. }
      assert (FOFF2 : forall a, (p <= a < p + 32 \/ sp <= a < sp + 8) \/ (umap_foot 32 obj bl bc ents a \/ umap_foot 32 obj bl' n ents' a) -> ~ in_ranges (ly_img L) a).
      { intros a [Ha | [Ha | Ha]]; [exact (FOFF a Ha) | exact (foot_offimg_gen C A M model bl bc ents a AI U Ha) | exact (foot_offimg_gen C A' M' model' bl' n ents' a AI' U' Ha)]. }
      assert (SX' : sx_inv ST s M').
      { eapply (sx_inv_via_eff' s A0 A' M0 M' model0 W _ SX0 AI0 EFF2 Hown_sx Herr_sx FOFF2). unfold Wnt; cbn; lia. }
      assert (Hch : 0 <= hmod key n < n) by (unfold hmod; apply Z.mod_pos_bound; lia).
      pose proof (h_bc (u_hdr U')) as Cbc'. unfold cell8 in Cbc'.

      assert (FINR : forall R5,
        base_ok R5 -> getr R5 23%bv = Z_to_bv 64 key -> getr R5 27%bv = Z_to_bv 64 p ->
        getr R5 24%bv = Z_to_bv 64 n -> getr R5 22%bv = Z_to_bv 64 (hmod key n) -> getr R5 15%bv = Z_to_bv 64 w3 -> getr R5 6%bv = Z_to_bv 64 (2 ^ 60) ->
        srealizes SEGS (cfg fx2 R5 NT_INS M' model') K).
      { intros R5 B5 Q23'' Q27'' Q24'' Q22'' Q15'' Q6''.
        assert (CO : core p A' M' model' R5).
        { constructor.
          - exact AI'. - exact MS'. - exact Hfs'. - exact Hfds'. - exact SX'.
          - exact B5. - exact Q23''. - exact Q27''.
          - exact FR'.
          - eapply defined_agree; [exact DEF0 | apply AGa; [lia | lia | lia | intros i Hi; apply (Hhiown sp 8 i); lia | exact DEF0]].
          - exact DEFW'.
          - exact Hp0. - exact Hpc. - exact Hpal. - exact Hpl'. - exact Hpnew.
          - eapply cellw_agree; [exact Cnh | eapply agree_on_sub; [exact AGp | lia | cbn; lia] | lia | cbn; lia].
          - eapply cellw_agree; [exact Cnk | eapply agree_on_sub; [exact AGp | lia | cbn; lia] | lia | cbn; lia].
          - eapply defined_agree; [exact DEFp | exact AGp]. }
        eapply (phaseF C fx2 p A' M' model' R5 bl' n ents' true _ CO FB ltac:(lia) ltac:(lia) Q24'' Q22'' Q15'' Q6'' U' PERM' Hpa').
        + intros HT. discriminate HT.
        + intros _. split; [exact Hgrow | reflexivity].
        + cbn [app]. exists (live MI A). split; [exact LADD|]. exists lv1. split; [exact LADD' | exact LAP2].
        + exact EFF2.
        + intros a [[Ha | Ha] | [Ha | Ha]]; [left; exact Ha | right; right; right; exact Ha | right; left; exact Ha | right; right; left; exact Ha].
        + exact FOFF2. }

      pose (E := Eseed R' [Z_to_bv 64 p; Z_to_bv 64 parser; Z_to_bv 64 sp; Z_to_bv 64 key; Z_to_bv 64 n; Z_to_bv 64 w3; Z_to_bv 64 (2 ^ 60)]).
      change 1152921504606846976 with (2 ^ 60) in Q6'.
      assert (HR : regs_ok E (srs sr_id [(27%bv, EVar 32); (8%bv, EVar 33); (2%bv, EVar 34); (23%bv, EVar 35); (26%bv, EVar 37); (6%bv, EVar 38)]) R').
      { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
      assert (HK : know_ok SEGS E M' []) by constructor.
      assert (Hlandr : 0 <= Z.land n (n - 1) <= 2 * n).
      { pose proof (Z.add_lor_land n (n - 1)). pose proof (Z.land_nonneg n (n - 1)). pose proof (Z.lor_nonneg n (n - 1)). lia. }
      assert (Hdummy : bl' = bl') by reflexivity.
      Ltac finR FINR HR' BR Hj Hd :=
        eapply FINR;
        [ nt_base_from HR' BR
        | let Q := fresh in rreg HR' 23%bv Q; exact Q
        | let Q := fresh in rreg HR' 27%bv Q; exact Q
        | let Q := fresh in rreg HR' 24%bv Q; exact Q
        | let Q := fresh in rreg HR' 22%bv Q; rewrite Q; nrw Hd; first [reflexivity | f_equal; first [exact Hj | lia]]
        | let Q := fresh in rreg HR' 15%bv Q; exact Q
        | let Q := fresh in rreg HR' 6%bv Q; exact Q ].
      pose proof (proj1 (proj2 (proj2 VF))) as Hv3.
      clear - HR HK FINR MS' BR Cbc' Hkr Hbl'0 Hbl'1 Hch Hobjlo Hobjhi Hsphi Hsplo Hn16 HnN HnD Hs1 Hpar Hp0 Hpc Hcl Hcv HnB Hbcn Hn28 Hlandr Hncase Hdummy Hv3.
      destruct Hncase as [[Hbc0 Hn2] | [Hn3 Hland]].
      +
        assert (Hland : Z.land n (n - 1) = 0) by (rewrite Hn2; reflexivity).
        assert (Hj : Z.land (n - 1) key = hmod key n) by (rewrite Hn2; change (2 - 1) with 1; rewrite Z.land_comm, land_1; reflexivity).
        xruns HR HK 100%nat STOPSG (SCR [false] [EVar 36] []) 50%N; [scE Hland Hdummy Hdummy Hdummy Hdummy|].
        finR FINR HR' BR Hj Hdummy.
      + destruct (Z.lt_ge_cases key n) as [Hlt | Hge].
        * assert (Hj : key = hmod key n) by (unfold hmod; rewrite Z.mod_small by lia; reflexivity).
          xruns HR HK 100%nat STOPSG (SCR [true; false] [EVar 36] []) 50%N; [scE Hland Hdummy Hdummy Hdummy Hdummy|].
          finR FINR HR' BR Hj Hdummy.
        * pose proof Hch as Hch'. unfold hmod in Hch'.
          assert (Hj : key mod n = hmod key n) by reflexivity.
          xruns HR HK 100%nat STOPSG (SCR [true; true] [EVar 36] []) 50%N; [scE Hland Hdummy Hdummy Hdummy Hdummy|].
          finR FINR HR' BR Hj Hdummy.
  Qed.

  Theorem nt_correct : srealizes SEGS (cfg fx R0 NT_ENTRY M0 model0) K.
  Proof using AC L MI ST NEW_STACK DEL_STACK fx A0 s R0 M0 model0 sp parser key bl bc w1 w2 w3 val ents K C.
    ctx. destruct SPF as (Hsp16' & Hsplo & Hsphi & Hn16 & HnN & HnD & Hs1 & Hpar). pose proof ac_bounds_lit as Hcv.
    destruct (pframe0 C) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8). destruct (base0 C) as (B2 & B3 & B4 & B8 & B18 & Bs).
    pose proof (nu_a5 _ _ _ _ _ _ _ _ _ _ _ NF) as B15.
    destruct (nsearch_correct L MI (seg_rom SEGS) A0 M0 parser sp bl bc key ents U0 F1 F3 F4 F5 F6 ltac:(lia) ltac:(lia) ltac:(lia) R0 B8 B2 B18)
      as (R1 & KEEP & SR & G22 & CASES).
    destruct SR as (T8 & T2 & T18 & T24 & T23).
    assert (B1 : base_ok R1).
    { unfold nt_base_ok. split; [exact T2|]. split; [rewrite (KEEP 3%bv) by (unfold nkeep_regs; inl); exact B3|]. split; [rewrite (KEEP 4%bv) by (unfold nkeep_regs; inl); exact B4|].
      split; [exact T8|]. split; [exact T18|].
      intros r Hr. rewrite KEEP; [reflexivity|]. clear - Hr. unfold nkeep_regs. cbn in Hr |- *. intuition congruence. }
    assert (Q15 : getr R1 15%bv = Z_to_bv 64 w3) by (rewrite (KEEP 15%bv) by (unfold nkeep_regs; inl); exact B15).
    destruct CASES as [(p & v0 & Hin & Hms & G27) | Hms].
    -
      eapply srz_msteps; [eapply ms_halt; exact MS0 | eapply ms_lazy; exact MS0 | exact Hms |].
      destruct (in_split _ _ Hin) as (l1 & l2 & HE).
      exact (phaseV C R1 p v0 l1 l2 B1 G27 Q15 HE).
    -
      eapply srz_msteps; [eapply ms_halt; exact MS0 | eapply ms_lazy; exact MS0 | exact Hms |].
      apply (phaseN C R1 B1 T24 T23 G22 Q15). intros p A2 M2 model2 R2 NS.
      apply (phaseI C p A2 M2 model2 R2 NS).
      +
        intros fx1 M' R' CO Q24 Q22 Q26 Q6 FB Hf14 Hf15 Hgrow EFF LADD U RC.
        apply (phaseR1 C fx1 p A2 M' model2 R' CO Q24 Q26 Q6 FB Hf14 Hf15 Hgrow EFF LADD U RC).
        intros fx2 M'' R'' FB2 RCL. exact (phaseR2 fx2 p A2 M'' model2 R'' FB2 RCL).
      +
        intros fx1 M' R' CO FB Hbc1 Hload Q24 Q22 Q15' Q6 EFF LADD U RC.
        destruct CO as [AI MS Hfs Hfds SX B Q23 Q27 FR DEF0 DEFW Hp0 Hpc Hpal Hpl Hpnew Cnh Cnk DEFp] eqn:HCO. clear HCO.
        eapply (phaseF C fx1 p A2 M' model2 R' bl bc ents false _ CO FB Hbc1 Hload Q24 Q22 Q15' Q6 U (Permutation_refl _)
                  (blocks_apart_p C p A2 M' model2 AI LADD)).
        * intros _. split; reflexivity.
        * intros HT. discriminate HT.
        * cbn [app]. exists (live MI A2). split; [exact LADD | reflexivity].
        * exact EFF.
        * intros a Ha. left. exact Ha.
        * intros a Ha. exact (live_offimg' A2 M' model2 p 32 a AI Hpl Ha).
  Qed.

End Nt.

Arguments nt_correct {AC L MI ST NEW_STACK DEL_STACK fx A0 s R0 M0 model0 sp parser key bl bc w1 w2 w3 val ents K} C.

Theorem emplace_nt_block_u1_spec {AC : AllocCeiling} :
  forall (L : Layout) (MI : MallocIface SEGS L) (ST : StaticsIface SEGS L) (NEW_STACK DEL_STACK : Z),
    0 <= NEW_STACK -> 0 <= DEL_STACK ->
    new_rule_stmt SEGS L MI ST NEW_STACK -> delete_rule_stmt SEGS L MI DEL_STACK ->
    next_prime_stmt SEGS L hc ->
    ly_new L = NT_NEWE -> ly_delete L = NT_DELETE ->
    (forall a, in_ranges (ly_img L) a -> a < alloc_ceiling) ->
    (forall a, in_ranges (ly_rw L) a -> in_ranges (ly_img L) a) ->
    (forall a, in_ranges (ly_relro L) a -> in_ranges (ly_img L) a) ->
    (forall a, in_ranges (ly_rw L) a -> ~ in_ranges (ly_relro L) a) ->
    (forall a, errno_win L a -> in_ranges (ly_rw L) a) ->
    emplace_nt_block_u1_stmt SEGS L MI ST NEW_STACK DEL_STACK hc.
Proof.
  intros L MI ST NEW_STACK DEL_STACK NSnn DSnn NEW DEL NP HLnew HLdel HL1 HL2 HL3 HL4 HL5.
  unfold emplace_nt_block_u1_stmt.
  intros fx A s R M model sp parser key bl bc w1 w2 w3 val ents K AI MS SX SXH Hsp16 Hceil Hroom Hwin Hosx Hesx FRM NF ASP0 ASP40 ASP56 ASP260 SO0 U ASPT HPAR Hw1 Hw2 Hw3 Hval ROC HSZ HNMAX Hlast ROOM1 ROOM2 CONT.
  change (hc_nt_entry hc) with NT_ENTRY.
  apply (@nt_correct AC L MI ST NEW_STACK DEL_STACK fx A s R M model sp parser key bl bc w1 w2 w3 val ents K).
  constructor; try assumption.
Qed.
