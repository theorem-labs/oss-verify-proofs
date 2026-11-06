(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SRealizes RefMemcpyLib FPSteps LibIface LibBudget LibEff.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContStmts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HStmts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsNeeds PrsInv.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Record prs_consts : Type := PRS_CONSTS {
  kc_parse        : Z;
  kc_parse_opts   : Z;
  kc_parse_module : Z;
  kc_set_numeric  : Z;
  kc_pm_stack     : Z;
  kc_po_stack     : Z
}.

Section Stmts.
Context {AC : AllocCeiling}.
Variable SEGS : list Segment.
Variable L : Layout.
Variable MI : MallocIface SEGS L.
Variable ST : StaticsIface SEGS L.
Variable kc : prs_consts.

#[local] Notation cfg fx R pc M model :=
  (mkCfg (@mkst fx R (Z_to_bv 64 pc) M (seg_rom SEGS)) model).
#[local] Abbreviation callB := (LibEff.callB MI ST).
#[local] Abbreviation retB := (LibEff.retB MI ST).
#[local] Abbreviation fld := (CRep.fld SEGS).
#[local] Abbreviation parser_rep := (PrsInv.parser_rep SEGS L MI).
#[local] Abbreviation words_ok := PrsInv.words_ok.
#[local] Abbreviation pm_budget := (PrsInv.pm_budget SEGS L MI).
#[local] Abbreviation pm_budgetL := (PrsInv.pm_budgetL SEGS L MI).
#[local] Abbreviation junk := (PrsNeeds.junk SEGS L MI).
#[local] Abbreviation ctx_rep := (CRep.ctx_rep MI).

Definition pm_foot (A : AS MI) (p : Z) (c c' : parserC) (a : Z) : Prop :=
  parser_foot p c a \/ parser_foot p c' a \/ junk A a.

Definition parse_module_stmt : Prop :=
  forall (fx : FPState) A (s : SX ST) R M model (sp ret p : Z) (c : parserC) (L0 : list (Z * Z)) (K : TSet),
    let STK := kc_pm_stack kc in
    let words := st_words (pc_state c) in let n := st_nwords (pc_state c) in
    callB A s R M model sp ret STK -> ro_clear L M -> frm_zero (@fp_csr fx) ->
    getr R 10%bv = Z_to_bv 64 p ->
    parser_rep A M p c -> above_sp MI A sp p PARSER_SIZE -> above_sp MI A sp (pc_cons c) 48 ->
    pc_cons c mod 16 = 0 ->
    fresh_state (pc_state c) words n ->
    (words <> 0 -> words_ok L0 sp M words n) ->
    (words <> 0 -> forall a, zwin words (words + 4 * n) a -> ~ zwin (sp - STK) sp a /\ ~ parser_foot p c a) ->

    Permutation (live MI A) (L0 ++ state_blocks (pc_state c)) ->
    pm_budgetL A L0 n ->
    (forall (fx' : FPState) A' R' M' model' (c' : parserC) (r : Z),
        retB A' s R R' M' model model' -> frm_zero (@fp_csr fx') ->
        getr R' 10%bv = Z_to_bv 64 r ->
        parser_rep A' M' p c' -> pc_cons c' = pc_cons c -> st_words (pc_state c') = words -> st_nwords (pc_state c') = n ->
        Permutation (live MI A') (L0 ++ state_blocks (pc_state c')) ->

        (forall b, In b (state_blocks (pc_state c')) -> 0 < snd b <= PM_BIG n) ->

        (forall cls, count_class_f (size_class MI) (BIG MI) (state_blocks (pc_state c')) cls <= (if cls <? 4 then PM_NODES n else 0) + 10) ->
        st_vsteps (pc_state c') ->
        eff MI A A' M M' (sp - STK, sp) (pm_foot A p c c') ->
        srealizes SEGS (cfg fx' R' ret M' model') K) ->
    srealizes SEGS (cfg fx R (kc_parse_module kc) M model) K.

Definition parse_opts_stmt (entry : Z) (needs_a7 : bool) : Prop :=
  forall (fx : FPState) A (s : SX ST) R M model (sp ret ctx env words n : Z) (K : TSet),
    let STK := kc_po_stack kc in
    callB A s R M model sp ret STK -> ro_clear L M -> frm_zero (@fp_csr fx) ->
    getr R 10%bv = Z_to_bv 64 ctx -> getr R 11%bv = Z_to_bv 64 0 -> getr R 12%bv = Z_to_bv 64 words ->
    getr R 13%bv = Z_to_bv 64 n -> getr R 14%bv = Z_to_bv 64 0 -> getr R 15%bv = Z_to_bv 64 0 ->
    getr R 16%bv = Z_to_bv 64 0 -> (needs_a7 = true -> getr R 17%bv = Z_to_bv 64 0) ->
    ctx_rep A M ctx env -> (forall a, zwin ctx (ctx + CTX_SZ) a -> ~ zwin (sp - STK) sp a) ->
    0 <= env < 32 ->
    (words <> 0 -> words_ok (live MI A) sp M words n) ->
    (forall a, zwin words (words + 4 * n) a -> ~ zwin (sp - STK) sp a) ->
    pm_budget A n ->
    (forall (fx' : FPState) A' R' M' model' (r : Z),
        retB A' s R R' M' model model' -> frm_zero (@fp_csr fx') ->
        getr R' 10%bv = Z_to_bv 64 r ->
        Permutation (live MI A') (live MI A) ->
        eff MI A A' M M' (sp - STK, sp) (junk A) ->
        srealizes SEGS (cfg fx' R' ret M' model') K) ->
    srealizes SEGS (cfg fx R entry M model) K.

Definition parse_with_options_stmt : Prop := parse_opts_stmt (kc_parse_opts kc) true.
Definition binary_parse_stmt : Prop := parse_opts_stmt (kc_parse kc) false.

Definition set_numeric_stmt (SN_STACK : Z) : Prop :=
  forall (fx : FPState) A (s : SX ST) R M model (sp ret p po tid : Z) (c : parserC) (K : TSet),
    callB A s R M model sp ret SN_STACK -> ro_clear L M ->
    getr R 10%bv = Z_to_bv 64 p -> getr R 11%bv = Z_to_bv 64 po -> getr R 12%bv = Z_to_bv 64 tid -> 0 <= tid < 2 ^ 32 ->
    parser_rep A M p c -> above_sp MI A sp p PARSER_SIZE -> above_sp MI A sp (pc_cons c) 48 ->
    above_sp MI A sp po OPND_SZ -> mdef M po OPND_SZ -> apart po OPND_SZ p PARSER_SIZE ->
    pm_budget A (st_nwords (pc_state c)) ->
    (forall A' R' M' model' (r nk bw enc nw : Z),
        retB A' s R R' M' model model' ->
        getr R' 10%bv = Z_to_bv 64 (r mod 2 ^ 64) -> (r = 0 \/ r = - 4) ->
        parser_rep A' M' p c -> live MI A' = live MI A ->
        (r = 0 -> exists node, In (node, (tid, (nk, bw, enc))) (t3c (st_m2 (pc_state c))) /\ nk <> 0 /\
                  fld M' (po + 8) 4 nk /\ fld M' (po + 12) 4 bw /\ fld M' (po + 16) 4 enc /\
                  nw = ((bw + 31) / 32) mod 2 ^ 16 /\ fld M' (po + 2) 2 nw) ->
        agree_on (fun a => po <= a < po + 2 \/ po + 4 <= a < po + 8) M M' ->
        eff MI A A' M M' (sp - SN_STACK, sp) (fun a => (po + 2 <= a < po + 4) \/ (po + 8 <= a < po + OPND_SZ) \/ junk A a) ->
        srealizes SEGS (cfg fx R' ret M' model') K) ->
    srealizes SEGS (cfg fx R (kc_set_numeric kc) M model) K.

End Stmts.
