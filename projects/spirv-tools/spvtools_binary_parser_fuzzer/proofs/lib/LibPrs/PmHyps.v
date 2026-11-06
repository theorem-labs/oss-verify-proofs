(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SRealizes RefMemcpyLib FPSteps LibIface LibBudget LibEff.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContStmts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import ContStmts3.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HStmts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsNeeds PrsInv PrsStmts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import TablStmts.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Record cont_consts : Type := CONT_CONSTS {
  kv_ecw_pb  : vec_consts;
  kv_ecw_pb2 : vec_consts;
  kv_oty_pb  : vec_consts;
  kv_oty_pbo : vec_consts;
  kv_opnd_pb : vec_consts;
  kv_str     : str_consts;
  kv_del1    : Z;
  kv_del_stack : Z
}.

Section Hyps.
Context {AC : AllocCeiling}.
Variable SEGS : list Segment.
Variable L : Layout.
Variable MI : MallocIface SEGS L.
Variable ST : StaticsIface SEGS L.

Definition OP_EXT_INST_IMPORT : Z := 11.   Definition OT_LITERAL_STRING : Z := 11.
Definition MASK_TYPES : list Z := [35; 36; 37; 38; 39; 40; 43; 44; 56; 61; 77; 78; 87; 89; 90; 91; 92; 103; 104].

Record pm_callees (G : grammar) (tc : tabl_consts) (dc : ds_consts) (nfc : ntfind_consts)
       (hc : hconsts) (cc : cont_consts) (kc : prs_consts)
       (idesc : Z -> Z -> Prop) (odesc edesc : Z -> Z -> Z -> Prop)
       (generates_type is_ext_inst is_nonsemantic : Z -> bool)
       (ds_rep : AS MI -> mem -> Z -> Z -> Z -> list (Z * Z) -> Prop) : Prop := PM_CALLEES {

  cl_G : grammar_ok G;
  cl_maxlen : g_maxlen G <= 48;
  cl_mask_len : forall t v l, In t MASK_TYPES -> g_operand G t v = Some l -> Zlen l <= 3;
  cl_spec_len : forall op l, g_specop G op = true -> g_op G op = Some l -> 3 <= Zlen l;

  cl_gt_int : generates_type OP_TYPE_INT = true;
  cl_gt_float : generates_type OP_TYPE_FLOAT = true;
  cl_gt_rid : forall op l, generates_type op = true -> g_op G op = Some l -> exists r, l = OT_RESULT_ID :: r;
  cl_rid1 : (forall op l, g_op G op = Some l -> (count_occ Z.eq_dec l OT_RESULT_ID <= 1)%nat)
            /\ (forall t v l, g_operand G t v = Some l -> ~ In OT_RESULT_ID l)
            /\ (forall e v l, g_ext G e v = Some l -> ~ In OT_RESULT_ID l);
  cl_import : g_op G OP_EXT_INST_IMPORT = Some [OT_RESULT_ID; OT_LITERAL_STRING];
  cl_spec_rid : forall op l, g_specop G op = true -> g_op G op = Some l -> ~ In OT_RESULT_ID (skipn 2 l);
  cl_RB : round_big_law MI;

  cl_new : new_rule_stmt SEGS L MI ST (ContStmts.NEW_STACK SEGS L MI);
  cl_del1 : op_delete_stmt SEGS L MI (kv_del1 cc) (MALLOC_STACK MI);
  cl_mstack : 0 <= MALLOC_STACK MI <= 8192;
  cl_classes : size_class MI 24 <= 2 /\ (size_class MI 32 <= 2 /\ size_class MI 24 <> size_class MI 32) /\ 4096 <= BIG MI;

  cl_fixword : TablStmts.fixword_stmt SEGS L tc;
  cl_is_host_endian : TablStmts.is_host_endian_stmt SEGS L tc;
  cl_generates_type : TablStmts.generates_type_stmt SEGS L tc generates_type;
  cl_is_ext_inst : TablStmts.is_ext_inst_stmt SEGS L tc;
  cl_is_optional : TablStmts.is_optional_stmt SEGS L tc;
  cl_is_nonsemantic : TablStmts.is_nonsemantic_stmt SEGS L tc;
  cl_fpenc : TablStmts.fpenc_stmt SEGS L tc;
  cl_operand_type_str : TablStmts.operand_type_str_stmt SEGS L tc;
  cl_idesc_name : TablStmts.idesc_name_stmt SEGS L tc idesc;
  cl_idesc_operands : TablStmts.idesc_operands_stmt SEGS L G tc idesc;
  cl_odesc_operands : TablStmts.odesc_operands_stmt SEGS L G tc odesc;
  cl_edesc_operands : TablStmts.edesc_operands_stmt SEGS L G tc edesc;
  cl_odesc_value : TablStmts.odesc_value_stmt SEGS L odesc;
  cl_strlen : TablStmts.strlen_ro_stmt SEGS L tc;
  cl_opcode_split : TablStmts.opcode_split_stmt SEGS tc;
  cl_binary_endianness : TablStmts.binary_endianness_stmt SEGS L tc;
  cl_lookup_opcode : TablStmts.lookup_opcode_stmt SEGS L G tc idesc;
  cl_lookup_operand : TablStmts.lookup_operand_stmt SEGS L G tc odesc;
  cl_lookup_ext : TablStmts.lookup_ext_stmt SEGS L G tc edesc;
  cl_spec_lookup : TablStmts.spec_lookup_stmt SEGS L G tc;
  cl_import_type_get : TablStmts.import_type_get_stmt SEGS L MI tc;
  cl_push_types : TablStmts.push_types_stmt SEGS L MI ST G tc (kv_oty_pbo cc);
  cl_take_first : TablStmts.take_first_stmt SEGS L MI ST tc (kv_oty_pbo cc);
  cl_tc_stacks : 0 <= tc_lookup_stack tc <= 64 /\ 0 <= tc_import_stack tc <= 64 /\ 0 <= tc_pattern_stack tc <= 96;

  cl_ds_laws : ds_rep_laws SEGS L MI ST dc ds_rep;
  cl_ds_ctor : ds_ctor_stmt SEGS L MI ST dc ds_rep;
  cl_pdiag0 : pdiag0_stmt SEGS L MI ST dc ds_rep;
  cl_pdiagE : pdiagE_stmt SEGS L MI ST dc ds_rep;
  cl_put_cstr : put_cstr_stmt SEGS L MI ST dc ds_rep;
  cl_put_u16 : put_u16_stmt SEGS L MI ST dc ds_rep;
  cl_put_u32 : put_u32_stmt SEGS L MI ST dc ds_rep;
  cl_put_u64 : put_u64_stmt SEGS L MI ST dc ds_rep;
  cl_put_int : put_int_stmt SEGS L MI ST dc ds_rep;
  cl_put_string : put_string_stmt SEGS L MI ST dc ds_rep;
  cl_ds_dtor : ds_dtor_stmt SEGS L MI ST dc ds_rep;
  cl_exhausted : exhausted_stmt SEGS L MI ST dc;
  cl_dc_stack : 1024 <= dc_stack dc <= 12288 /\ dc_stack dc mod 16 = 0;

  cl_find_u32 : find_stmt SEGS L MI (hc_find_u32 hc) 24 Z (nval24 SEGS);
  cl_find_ext : find_stmt SEGS L MI (hc_find_nt hc) 24 Z (nval24 SEGS);
  cl_emplace_u32 : emplace24_stmt SEGS L MI ST (ContStmts.NEW_STACK SEGS L MI) (MALLOC_STACK MI) (hc_emplace_u32 hc);
  cl_emplace_ext : emplace24_stmt SEGS L MI ST (ContStmts.NEW_STACK SEGS L MI) (MALLOC_STACK MI) (hc_emplace_ext hc);
  cl_nt_block : emplace_nt_block_stmt SEGS L MI ST hc (ContStmts.NEW_STACK SEGS L MI) (MALLOC_STACK MI);
  cl_nt_find : nt_find_block_stmt SEGS L MI nfc;

  cl_ecw_pb : vec32_push_back_stmt SEGS L MI ST (kv_ecw_pb cc);
  cl_ecw_pb2 : vec32_push_back_stmt SEGS L MI ST (kv_ecw_pb2 cc);
  cl_oty_pb : vec32_push_back_stmt SEGS L MI ST (kv_oty_pb cc);
  cl_opnd_pb : vec_opnd_push_back_stmt SEGS L MI ST (kv_opnd_pb cc);
  cl_makestring : ContStmts3.makestring_stmt' SEGS L MI ST (kv_str cc)

}.

End Hyps.
