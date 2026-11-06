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
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContStmts ContStmts2.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HStmts HStmtsU1.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsNeeds PrsInv PrsStmts PmHyps.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import TablStmts TablStmtsHdr.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Record cont_constsU1 : Type := CONT_CONSTS_U1 {
  ku_ecw_pbs  : vec_consts;
  ku_ecw_pbs2 : vec_consts;
  ku_oty_pb   : vec_consts;
  ku_oty_pbs  : vec_consts;
  ku_opnd_pbs : vec_consts;
  ku_str      : str_consts;
  ku_idx_u32  : Z;
  ku_idx_ext  : Z;
  ku_del1     : Z;
  ku_del_stack : Z
}.

Section HypsU1.
Context {AC : AllocCeiling}.
Variable SEGS : list Segment.
Variable L : Layout.
Variable MI : MallocIface SEGS L.
Variable ST : StaticsIface SEGS L.

#[local] Notation cfg fx R pc M model := (mkCfg (@mkst fx R (Z_to_bv 64 pc) M (seg_rom SEGS)) model).

Definition pdiagP_stmt (dc : ds_consts) (ds_rep : AS MI -> mem -> Z -> Z -> Z -> list (Z * Z) -> Prop) (pc : Z) : Prop :=
  forall (fx : FPState) A (s : SX ST) R M model (sp ret ds p pcons icount err : Z) (K : TSet),
    callB MI ST A s R M model sp ret (dc_stack dc) -> ro_clear L M ->
    getr R 10%bv = Z_to_bv 64 ds -> getr R 11%bv = Z_to_bv 64 p -> getr R 12%bv = Z_to_bv 64 (err mod 2 ^ 64) ->
    - 2 ^ 31 <= err < 0 ->
    CRep.fld SEGS M (p + 8) 8 pcons -> CRep.fld SEGS M (p + 80) 8 icount -> 0 <= p -> p + 88 <= 2 ^ 47 -> p mod 8 = 0 ->
    (forall a, zwin p (p + 88) a -> ~ zwin (sp - dc_stack dc) sp a) ->
    0 <= icount < 2 ^ 63 ->
    above_sp MI A sp ds DS_SIZE -> ds mod 8 = 0 -> mdef M ds DS_SIZE ->
    obj_ok MI A sp (dc_stack dc) pcons 48 -> pcons + 48 <= 2 ^ 47 -> pcons mod 16 = 0 -> CRep.fld SEGS M (pcons + 32) 8 0 ->
    (forall a, zwin ds (ds + DS_SIZE) a -> ~ zwin pcons (pcons + 48) a) ->
    ds_room SEGS L MI A ->
    (forall A' R' M' model' B,
        retB MI ST A' s R R' M' model model' ->
        ds_rep A' M' ds err 0 B ->
        blk_xfer [] B (live MI A) (live MI A') ->
        eff MI A A' M M' (sp - dc_stack dc, sp) (ds_foot ds B) ->
        srealizes SEGS (cfg fx R' ret M' model') K) ->
    srealizes SEGS (cfg fx R pc M model) K.

Definition fpenc16_stmt (tc : tabl_consts) : Prop :=
  PrsGrammar.leafA SEGS L (tc_fpenc tc) (fun _ _ => True) (fun _ R' => exists r, 0 <= r < 16 /\ getr R' 10%bv = Z_to_bv 64 r).

Definition put_chars_stmt (dc : ds_consts) (ds_rep : AS MI -> mem -> Z -> Z -> Z -> list (Z * Z) -> Prop) : Prop :=
  forall (fx : FPState) A (s : SX ST) R M model (sp ret ds err len p m : Z) (B : list (Z * Z)) (K : TSet),
    callB MI ST A s R M model sp ret (dc_stack dc) -> ro_clear L M ->
    getr R 10%bv = Z_to_bv 64 ds -> getr R 11%bv = Z_to_bv 64 p -> getr R 12%bv = Z_to_bv 64 m ->
    ds_rep A M ds err len B -> above_sp MI A sp ds DS_SIZE ->
    0 <= m -> 0 < p -> p + m <= 2 ^ 47 -> mdef M p m ->
    (forall a, zwin p (p + m) a ->
       ~ zwin ds (ds + DS_SIZE) a /\
       (sp <= a \/ (exists q k, In (q, k) (live MI A) /\ q <= a < q + k /\ ~ In (q, k) B))) ->
    len + m <= DS_MAXLEN ->
    ds_room SEGS L MI A ->
    ds_op_post SEGS L MI ST dc ds_rep fx A s R M model sp ret ds err (len + m) B K (fun _ => False) true ->
    srealizes SEGS (cfg fx R (dc_put_cstr dc) M model) K.

Definition exhaustedU_stmt (dc : ds_consts) : Prop :=
  forall (fx : FPState) A (s : SX ST) R M model (sp ret this pcons nwords widx icount inst_offset opcode type : Z) (K : TSet),
    callB MI ST A s R M model sp ret (dc_stack dc) -> ro_clear L M ->
    getr R 10%bv = Z_to_bv 64 this -> getr R 11%bv = Z_to_bv 64 inst_offset ->
    getr R 12%bv = Z_to_bv 64 opcode -> getr R 13%bv = Z_to_bv 64 type ->
    0 <= inst_offset < 2 ^ 63 -> 0 <= opcode < 2 ^ 16 -> 0 <= type < 2 ^ 32 ->
    placed MI A this 288 -> this + 288 <= 2 ^ 47 -> (forall a, zwin this (this + 288) a -> ~ zwin (sp - dc_stack dc) sp a) ->
    CRep.fld SEGS M (this + 8) 8 pcons -> CRep.fld SEGS M (this + 56) 8 nwords -> CRep.fld SEGS M (this + 72) 8 widx -> CRep.fld SEGS M (this + 80) 8 icount ->
    0 <= nwords < 2 ^ 63 -> 0 <= widx < 2 ^ 63 -> 0 <= icount < 2 ^ 63 ->
    obj_ok MI A sp (dc_stack dc) pcons 48 -> pcons + 48 <= 2 ^ 47 -> pcons mod 16 = 0 -> CRep.fld SEGS M (pcons + 32) 8 0 ->
    ds_room1 SEGS L MI A ->
    (forall A' R' M' model' (J : Z -> Prop),
        retB MI ST A' s R R' M' model model' ->
        getr R' 10%bv = Z_to_bv 64 (2 ^ 64 - 4) ->
        Permutation (live MI A') (live MI A) ->
        junk_ok MI A J ->
        eff MI A A' M M' (sp - dc_stack dc, sp) (fun a => J a) ->
        srealizes SEGS (cfg fx R' ret M' model') K) ->
    srealizes SEGS (cfg fx R (dc_exhausted dc) M model) K.

Record pm_calleesU1 (G : grammar) (tc : tabl_consts) (dc : ds_consts) (nfc : ntfind_consts)
       (hc : hconsts) (cc : cont_constsU1) (kc : prs_consts)
       (idesc : Z -> Z -> Prop) (odesc edesc : Z -> Z -> Z -> Prop)
       (generates_type is_ext_inst is_nonsemantic : Z -> bool)
       (ds_rep : AS MI -> mem -> Z -> Z -> Z -> list (Z * Z) -> Prop) : Prop := PM_CALLEES_U1 {

  cu_G : grammar_ok G;
  cu_maxlen : g_maxlen G <= 48;
  cu_mask_len : forall t v l, In t MASK_TYPES -> g_operand G t v = Some l -> Zlen l <= 3;
  cu_spec_len : forall op l, g_specop G op = true -> g_op G op = Some l -> 3 <= Zlen l;
  cu_gt_int : generates_type OP_TYPE_INT = true;
  cu_gt_float : generates_type OP_TYPE_FLOAT = true;
  cu_gt_rid : forall op l, generates_type op = true -> g_op G op = Some l -> exists r, l = OT_RESULT_ID :: r;
  cu_rid1 : (forall op l, g_op G op = Some l -> (count_occ Z.eq_dec l OT_RESULT_ID <= 1)%nat)
            /\ (forall t v l, g_operand G t v = Some l -> ~ In OT_RESULT_ID l)
            /\ (forall e v l, g_ext G e v = Some l -> ~ In OT_RESULT_ID l);
  cu_import : g_op G OP_EXT_INST_IMPORT = Some [OT_RESULT_ID; OT_LITERAL_STRING];
  cu_spec_rid : forall op l, g_specop G op = true -> g_op G op = Some l -> ~ In OT_RESULT_ID (skipn 2 l);
  cu_RB : round_big_law MI;

  cu_new : new_rule_stmt SEGS L MI ST (ContStmts.NEW_STACK SEGS L MI);
  cu_del1 : op_delete_stmt SEGS L MI (ku_del1 cc) (MALLOC_STACK MI);
  cu_mstack : 0 <= MALLOC_STACK MI <= 8192;
  cu_classes : size_class MI 24 <= 2 /\ (size_class MI 32 <= 2 /\ size_class MI 24 <> size_class MI 32) /\ 4096 <= BIG MI;

  cu_fixword : TablStmts.fixword_stmt SEGS L tc;
  cu_is_host_endian : TablStmts.is_host_endian_stmt SEGS L tc;
  cu_generates_type : TablStmts.generates_type_stmt SEGS L tc generates_type;
  cu_is_ext_inst : TablStmts.is_ext_inst_stmt SEGS L tc;
  cu_is_optional : TablStmts.is_optional_stmt SEGS L tc;
  cu_is_nonsemantic : TablStmts.is_nonsemantic_stmt SEGS L tc;
  cu_fpenc : TablStmts.fpenc_stmt SEGS L tc;
  cu_fpenc16 : fpenc16_stmt tc;
  cu_operand_type_str : TablStmts.operand_type_str_stmt SEGS L tc;
  cu_idesc_name : TablStmts.idesc_name_stmt SEGS L tc idesc;
  cu_idesc_operands : TablStmts.idesc_operands_stmt SEGS L G tc idesc;
  cu_odesc_operands : TablStmts.odesc_operands_stmt SEGS L G tc odesc;
  cu_edesc_operands : TablStmts.edesc_operands_stmt SEGS L G tc edesc;
  cu_odesc_value : TablStmts.odesc_value_stmt SEGS L odesc;

  cu_idesc_ptr : forall d op, idesc d op -> 0x10000 <= d /\ d + 60 <= 2 ^ 40 /\ d mod 4 = 0;
  cu_odesc_ptr : forall d t v, odesc d t v -> 0x10000 <= d /\ d + 16 <= 2 ^ 40 /\ d mod 4 = 0;
  cu_edesc_ptr : forall d e v, edesc d e v -> 0x10000 <= d /\ d + 16 <= 2 ^ 40 /\ d mod 4 = 0;
  cu_strlen : TablStmts.strlen_ro_stmt SEGS L tc;
  cu_opcode_split : TablStmts.opcode_split_stmt SEGS tc;
  cu_binary_endianness : TablStmts.binary_endianness_stmt SEGS L tc;
  cu_lookup_opcode : TablStmts.lookup_opcode_stmt SEGS L G tc idesc;
  cu_lookup_operand : TablStmts.lookup_operand_stmt SEGS L G tc odesc;
  cu_lookup_ext : TablStmts.lookup_ext_stmt SEGS L G tc edesc;
  cu_spec_lookup : TablStmts.spec_lookup_stmt SEGS L G tc;
  cu_import_type_get : TablStmts.import_type_get_stmt SEGS L MI tc;
  cu_push_types : TablStmts.push_types_stmt SEGS L MI ST G tc (ku_oty_pbs cc);
  cu_take_first : TablStmts.take_first_stmt SEGS L MI ST tc (ku_oty_pbs cc);
  cu_tc_stacks : 0 <= tc_lookup_stack tc <= 64 /\ 0 <= tc_import_stack tc <= 64 /\ 0 <= tc_pattern_stack tc <= 96;

  cu_header_get : TablStmtsHdr.header_get_stmt SEGS L 0x66680 32;
  cu_peek_at : TablStmtsHdr.peek_at_stmt SEGS L 0x6a06c;

  cu_ds_laws : ds_rep_laws SEGS L MI ST dc ds_rep;
  cu_pdiagP : pdiagP_stmt dc ds_rep (dc_pdiag dc);
  cu_put_cstr : put_cstr_stmt SEGS L MI ST dc ds_rep;
  cu_put_u16 : put_u16_stmt SEGS L MI ST dc ds_rep;
  cu_put_u32 : put_u32_stmt SEGS L MI ST dc ds_rep;
  cu_put_u64 : put_u64_stmt SEGS L MI ST dc ds_rep;
  cu_put_int : put_int_stmt SEGS L MI ST dc ds_rep;
  cu_put_chars : put_chars_stmt dc ds_rep;
  cu_ds_dtor : ds_dtor_stmt SEGS L MI ST dc ds_rep;
  cu_exhausted : exhaustedU_stmt dc;
  cu_dc_stack : 1024 <= dc_stack dc <= 12288 /\ dc_stack dc mod 16 = 0;

  cu_find_u32 : find_stmt SEGS L MI (hc_find_u32 hc) 24 Z (nval24 SEGS);
  cu_find_ext : find_stmt SEGS L MI (hc_find_nt hc) 24 Z (nval24 SEGS);
  cu_find_nt : find_stmt SEGS L MI (hc_find_nt hc) 32 (Z * Z * Z) (nval32 SEGS);
  cu_index_u32 : index24_u1_stmt SEGS L MI ST (ContStmts.NEW_STACK SEGS L MI) (MALLOC_STACK MI) (ku_idx_u32 cc);
  cu_index_ext : index24_u1_stmt SEGS L MI ST (ContStmts.NEW_STACK SEGS L MI) (MALLOC_STACK MI) (ku_idx_ext cc);
  cu_nt_block : emplace_nt_block_u1_stmt SEGS L MI ST (ContStmts.NEW_STACK SEGS L MI) (MALLOC_STACK MI) hc;
  cu_nt_find : nt_find_block_u1_stmt SEGS L MI (nf_entry nfc) (nf_miss nfc) (nf_hit nfc);

  cu_ecw_pbs : TablStmts.vec32_pbslow_stmt SEGS L MI ST (2 ^ 32) (ku_ecw_pbs cc);
  cu_ecw_pbs2 : TablStmts.vec32_pbslow_stmt SEGS L MI ST (2 ^ 32) (ku_ecw_pbs2 cc);
  cu_oty_pb : vec32_push_backU_stmt SEGS L MI ST (2 ^ 31) (ku_oty_pb cc);
  cu_opnd_pbs : vec_opnd_pbslow_stmt SEGS L MI ST (ku_opnd_pbs cc);
  cu_makestring : makestringU_stmt SEGS L MI ST (ku_str cc)

}.

End HypsU1.
