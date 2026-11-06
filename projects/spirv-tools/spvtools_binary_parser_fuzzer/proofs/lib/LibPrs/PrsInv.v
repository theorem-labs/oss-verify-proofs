(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SRealizes RefMemcpyLib LibIface LibBudget LibEff.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContStmts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HStmts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsNeeds.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition PARSER_SIZE : Z := 288.
Definition ST_OFF : Z := 48.

Section Inv.
Context {AC : AllocCeiling}.
Variable SEGS : list Segment.
Variable L : Layout.
Variable MI : MallocIface SEGS L.
Variable ST : StaticsIface SEGS L.

#[local] Abbreviation fld := (CRep.fld SEGS).
#[local] Abbreviation state_rep := (@HStmts.state_rep AC SEGS L MI).

Record parserC : Type := PARSERC {
  pc_cons  : Z;
  pc_user  : Z;
  pc_state : stateC
}.

Record parser_rep (A : AS MI) (M : mem) (p : Z) (c : parserC) : Prop := PARSER_REP {
  pr_cons  : fld M (p + 8) 8 (pc_cons c);
  pr_user  : fld M (p + 16) 8 (pc_user c);
  pr_hdrfn : fld M (p + 24) 8 0;
  pr_insfn : fld M (p + 32) 8 0;
  pr_hunk  : fld M (p + 40) 1 0;
  pr_state : state_rep A M (p + ST_OFF) (pc_state c);
  pr_def   : mdef M p ST_OFF;
  pr_al    : p mod 16 = 0;
  pr_range : 0 < p /\ p + PARSER_SIZE <= 2 ^ 47;

  pr_consf : fld M (pc_cons c + 32) 8 0;
  pr_consm : mdef M (pc_cons c + 32) 8;
  pr_consd : apart p PARSER_SIZE (pc_cons c) 48
}.

Definition parser_foot (p : Z) (c : parserC) (a : Z) : Prop :=
  (p <= a < p + PARSER_SIZE) \/ state_foot (p + ST_OFF) (pc_state c) a.

Definition fresh_state (c : stateC) (words nwords : Z) : Prop :=
  st_words c = words /\ st_nwords c = nwords /\ st_widx c = 0 /\ st_icount c = 0 /\ st_flags c = 0 /\
  st_m1 c = (0, 0, []) /\ st_m2 c = (0, 0, []) /\ st_m3 c = (0, 0, []) /\
  t3a (st_v1 c) = t3b (st_v1 c) /\ t3a (st_v2 c) = t3b (st_v2 c) /\ t3a (st_v3 c) = t3b (st_v3 c) /\
  t3a (st_v1 c) <> 0 /\ t3a (st_v2 c) <> 0 /\ t3a (st_v3 c) <> 0 /\

  t3c (st_v1 c) = t3a (st_v1 c) + 500 /\ t3c (st_v2 c) = t3a (st_v2 c) + 100 /\ t3c (st_v3 c) = t3a (st_v3 c) + 100.

Definition st_vsteps (c : stateC) : Prop :=
  (exists n, 0 <= n /\ t3b (st_v1 c) = t3a (st_v1 c) + 20 * n) /\
  (exists n, 0 <= n /\ t3b (st_v2 c) = t3a (st_v2 c) + 4 * n) /\
  (exists n, 0 <= n /\ t3b (st_v3 c) = t3a (st_v3 c) + 4 * n).

Definition words_ok (L0 : list (Z * Z)) (sp : Z) (M : mem) (words n : Z) : Prop :=
  0 < words /\ words mod 4 = 0 /\ 0 <= n /\ words + 4 * n <= 2 ^ 47 /\ mdef M words (4 * n) /\
  (sp <= words \/ exists q k, In (q, k) L0 /\ q <= words /\ words + 4 * n <= q + k).

Definition PM_SMALL_SLACK : Z := 16.
Definition PM_BIG (n : Z) : Z := 24 * n + 2 ^ 30.
Definition PM_NODES (n : Z) : Z := n / 2 + n / 3 + 8.

Definition pm_budget (A : AS MI) (n : Z) : Prop :=
  caps MI A = lib_caps /\ bigcap MI A = LIB_BIGCAP /\ LIB_NMAX <= NMAX MI /\ 0 <= n < 2 ^ 24 /\
  (forall c, 4 <= c -> count_class_f (size_class MI) (BIG MI) (live MI A) c + PM_SMALL_SLACK <= CAP_SMALL) /\
  (forall c, 0 <= c < 4 -> count_class_f (size_class MI) (BIG MI) (live MI A) c + PM_NODES n + PM_SMALL_SLACK <= CAP_NODE) /\
  big_bytes_f (round_big MI) (BIG MI) (live MI A) + PM_BIG n <= LIB_BIGCAP.

Definition pm_budgetL (A : AS MI) (L0 : list (Z * Z)) (n : Z) : Prop :=
  caps MI A = lib_caps /\ bigcap MI A = LIB_BIGCAP /\ LIB_NMAX <= NMAX MI /\ 0 <= n < 2 ^ 24 /\
  (forall c, 4 <= c -> count_class_f (size_class MI) (BIG MI) L0 c + PM_SMALL_SLACK <= CAP_SMALL) /\
  (forall c, 0 <= c < 4 -> count_class_f (size_class MI) (BIG MI) L0 c + PM_NODES n + PM_SMALL_SLACK <= CAP_NODE) /\
  big_bytes_f (round_big MI) (BIG MI) L0 + PM_BIG n <= LIB_BIGCAP.

Record instrS : Type := INSTRS {
  is_offset : Z;
  is_wc     : Z;
  is_opcode : Z;
  is_expected : list Z;
  is_nops   : Z;
  is_typeid : Z; is_resultid : Z; is_exttype : Z
}.

Definition zw_stack_ok (xs : list Z) : Prop :=
  exists bot top, xs = bot ++ top /\ seed_free top /\
    (bot = [] \/ bot = [OT_TYPED_LITERAL_NUMBER] \/ bot = [OT_SPEC_CONSTANT_OP_NUMBER]
     \/ bot = [OT_VARIABLE_LITERAL_INTEGER_ID] \/ bot = [OT_VARIABLE_LITERAL_INTEGER_ID; OT_ID]
     \/ (bot = [OT_VARIABLE_LITERAL_INTEGER_ID; OT_ID; OT_OPTIONAL_TYPED_LITERAL_INTEGER] /\ top = [])).

Definition zw_next (xs : list Z) : Z :=
  if zw_seed (last xs 0) then 1 else 0.
Definition oper_measure (i : instrS) (widx : Z) : Z :=
  3 * Z.max 0 (is_offset i + is_wc i - widx) + zw_next (is_expected i).

End Inv.
