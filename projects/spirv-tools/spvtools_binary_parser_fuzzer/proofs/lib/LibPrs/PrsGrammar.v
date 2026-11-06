(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SRealizes RefMemcpyLib LibIface LibBudget LibEff.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContStmts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition OT_NONE : Z := 0.   Definition OT_ID : Z := 1.   Definition OT_TYPE_ID : Z := 2.
Definition OT_RESULT_ID : Z := 3.   Definition OT_LITERAL_INTEGER : Z := 6.
Definition OT_SPEC_CONSTANT_OP_NUMBER : Z := 8.   Definition OT_TYPED_LITERAL_NUMBER : Z := 9.
Definition OT_FPENCODING : Z := 34.   Definition OT_OPTIONAL_ID : Z := 42.
Definition OT_OPTIONAL_LITERAL_INTEGER : Z := 45.   Definition OT_OPTIONAL_TYPED_LITERAL_INTEGER : Z := 47.
Definition OT_OPTIONAL_FPENCODING : Z := 51.   Definition OT_VARIABLE_ID : Z := 52.
Definition OT_VARIABLE_LITERAL_INTEGER : Z := 53.   Definition OT_VARIABLE_LITERAL_INTEGER_ID : Z := 54.
Definition OT_VARIABLE_ID_LITERAL_INTEGER : Z := 55.   Definition OT_OPTIONAL_CAPABILITY : Z := 105.
Definition OT_VARIABLE_CAPABILITY : Z := 106.
Definition OP_TYPE_INT : Z := 21.   Definition OP_TYPE_FLOAT : Z := 22.

Record grammar : Type := GRAMMAR {
  g_op      : Z -> option (list Z);
  g_operand : Z -> Z -> option (list Z);
  g_ext     : Z -> Z -> option (list Z);
  g_specop  : Z -> bool;
  g_maxlen  : Z
}.

Definition zw_type (t : Z) : bool :=
  (t =? OT_TYPED_LITERAL_NUMBER) || (t =? OT_OPTIONAL_TYPED_LITERAL_INTEGER).

Definition zw_seed (t : Z) : bool :=
  zw_type t || (t =? OT_VARIABLE_LITERAL_INTEGER_ID) || (t =? OT_SPEC_CONSTANT_OP_NUMBER).

Definition seed_free (l : list Z) : Prop := forall t, In t l -> zw_seed t = false.

Definition op_list_ok (l : list Z) : Prop :=
  seed_free (removelast l) /\ (forall t, In t l -> t <> OT_OPTIONAL_TYPED_LITERAL_INTEGER).

Record grammar_ok (G : grammar) : Prop := GRAMMAR_OK {
  go_typeint   : forall l, g_op G OP_TYPE_INT = Some l -> l = [OT_RESULT_ID; OT_LITERAL_INTEGER; OT_LITERAL_INTEGER];
  go_typefloat : forall l, g_op G OP_TYPE_FLOAT = Some l -> l = [OT_RESULT_ID; OT_LITERAL_INTEGER; OT_OPTIONAL_FPENCODING];
  go_op_zw     : forall op l, g_op G op = Some l -> op_list_ok l;
  go_spec_zw   : forall op l, g_specop G op = true -> g_op G op = Some l -> seed_free (skipn 2 l);
  go_operand_zw : forall t v l, g_operand G t v = Some l -> seed_free l;
  go_ext_zw    : forall e v l, g_ext G e v = Some l -> seed_free l;
  go_len_op    : forall op l, g_op G op = Some l -> Zlength l <= g_maxlen G;
  go_len_operand : forall t v l, g_operand G t v = Some l -> Zlength l <= g_maxlen G;
  go_len_ext   : forall e v l, g_ext G e v = Some l -> Zlength l <= g_maxlen G;
  go_range     : forall l t, (exists op, g_op G op = Some l) \/ (exists a v, g_operand G a v = Some l)
                              \/ (exists e v, g_ext G e v = Some l) -> In t l -> 0 <= t < 2 ^ 31;
  go_maxlen    : 1 <= g_maxlen G <= 1024
}.

Definition push_types (l : list Z) (xs : list Z) : list Z :=
  xs ++ filter (fun t => negb (t =? OT_NONE)) (rev l).
Definition expand (t : Z) : option (list Z) :=
  if t =? OT_VARIABLE_ID then Some [OT_VARIABLE_ID; OT_OPTIONAL_ID]
  else if t =? OT_VARIABLE_LITERAL_INTEGER then Some [OT_VARIABLE_LITERAL_INTEGER; OT_OPTIONAL_LITERAL_INTEGER]
  else if t =? OT_VARIABLE_LITERAL_INTEGER_ID then Some [OT_VARIABLE_LITERAL_INTEGER_ID; OT_ID; OT_OPTIONAL_TYPED_LITERAL_INTEGER]
  else if t =? OT_VARIABLE_ID_LITERAL_INTEGER then Some [OT_VARIABLE_ID_LITERAL_INTEGER; OT_LITERAL_INTEGER; OT_OPTIONAL_ID]
  else if t =? OT_VARIABLE_CAPABILITY then Some [OT_VARIABLE_CAPABILITY; OT_OPTIONAL_CAPABILITY]
  else None.

Definition take_first (xs : list Z) : Z * list Z :=
  let t := last xs 0 in let r := removelast xs in
  match expand t with
  | None => (t, r)
  | Some e => (last e 0, r ++ removelast e)
  end.

Definition is_variable (t : Z) : bool :=
  match expand t with Some _ => true | None => false end.
Definition is_optional (t : Z) : bool :=
  existsb (Z.eqb t) [42; 43; 44; 45; 46; 47; 48; 49; 76; 78; 92; 50; 87; 51; 104; 105] || is_variable t.

Definition round_big_law {AC : AllocCeiling} {SEGS : list Segment} {L : Layout} (MI : MallocIface SEGS L) : Prop :=
  forall n, 0 <= n -> n <= round_big MI n <= n + 4116.

Section Vocab.
Context {AC : AllocCeiling}.
Variable SEGS : list Segment.
Variable L : Layout.
#[local] Abbreviation fld := (CRep.fld SEGS).

Definition ro_span (p : Z) (l : list Z) : Prop :=
  0x10000 <= p /\ p + 4 * Zlen l <= 2 ^ 47 /\
  forall M, ro_clear L M -> forall i, 0 <= i < Zlen l -> 0 <= Znth i l < 2 ^ 32 /\ fld M (p + 4 * i) 4 (Znth i l).

Definition ro_cstr (p n : Z) : Prop :=
  0x10000 <= p /\ 0 <= n /\ p + n + 8 <= 2 ^ 47 /\
  forall M, ro_clear L M ->
    (forall i, 0 <= i < n -> exists c, 0 < c < 256 /\ fld M (p + i) 1 c) /\ fld M (p + n) 1 0
    /\ (forall a, p - p mod 8 <= a < p + n + 1 + (8 - (p + n + 1) mod 8) mod 8 -> exists c, 0 <= c < 256 /\ fld M a 1 c).

Record tabl_consts : Type := TABL_CONSTS {
  tc_fixword : Z;  tc_is_host_endian : Z;  tc_binary_endianness : Z;  tc_opcode_split : Z;
  tc_lookup_opcode : Z;  tc_lookup_operand : Z;  tc_lookup_ext : Z;  tc_spec_lookup : Z;
  tc_idesc_operands : Z;  tc_idesc_name : Z;  tc_odesc_operands : Z;  tc_edesc_operands : Z;
  tc_operand_type_str : Z;  tc_generates_type : Z;  tc_is_ext_inst : Z;  tc_is_optional : Z;
  tc_is_nonsemantic : Z;  tc_fpenc : Z;  tc_import_type_get : Z;  tc_push_types : Z;  tc_take_first : Z;
  tc_strlen : Z;
  tc_lookup_stack : Z;
  tc_import_stack : Z;
  tc_pattern_stack : Z
}.

Definition sx32 (x : Z) : Z := if x <? 2 ^ 31 then x else x + 2 ^ 64 - 2 ^ 32.

Definition leafA (pc : Z) (PRE : bvmap 5 word -> mem -> Prop) (POST : bvmap 5 word -> bvmap 5 word -> Prop) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : mem) (ret : word),
    ro_clear L M -> PRE R M -> getr R 1%bv = ret -> ret_ok ret ->
    exists R',
      msteps SEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom SEGS)) (@mkst fx R' ret M (seg_rom SEGS))
      /\ kept R R' /\ POST R R'.

End Vocab.
