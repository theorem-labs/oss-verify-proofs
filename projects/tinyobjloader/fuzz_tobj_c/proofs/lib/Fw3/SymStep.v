(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "SLit"; "sstate"; "sv_eqb"; "sobj"; "odefault"; "ss_facts"; "ss_pc"; "SAlu"; "ss_fcsr"; "tfact"; "ss_objs"; "ob_dflt"; "ss_lenient"; "mkSS"; "ss_fregs"; "ss_next"; "ss_regs"; "ss_resv"; "SPBranch"; "SVar"; "ob_cells"; "ob_lo"; "sfcsr"; "DUnknown"; "SPUle"; "ob_base"; "SMd"; "SPNot"; "cell"; "mkObj"; "ob_hi"; "SLBytes"; "SMdW"; "SAluW"; "SExt"; "dflt_writable"; "mkCell"; "SPUlt"; "c_off"; "c_width"; "ext_low"; "sprop_eqb"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@Corelib.Init.Datatypes"; "bool"; "prod"; "option"; "false"; "pair"; "andb"; "Some"; "list"; "fst"; "snd"; "true"; "None"; "cons"; "nat"; "negb"; "nil"; "orb"; "length"; "app"; "S"; "@LinuxProcessSemantics.Riscv.Instr"; "aluop"; "mulop"; "branch_cond"; "ffmt"; "instr"; "fcvt_ty"; "ALU_SUB"; "csrop"; "ALU_ADD"; "awidth"; "fmvdir"; "msize"; "ALU_SLL"; "BC_LT"; "BC_LTU"; "M_MUL"; "amoop"; "fariop"; "fcmpop"; "fmaop"; "fminmaxop"; "fsgnop"; "ALU_SRL"; "BC_EQ"; "BC_NE"; "Ecall"; "@Stdlib.ZArith.BinInt.Z"; "leb"; "add"; "sub"; "ltb"; "pow"; "eqb"; "modulo"; "min"; "max"; "mul"; "opp"; "div"; "shiftr"; "log2"; "land"; "to_nat"; "of_N"; "to_N"; "abs"; "shiftl"; "gcd"; "lnot"; "of_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "IF_range"; "IF_none"; "lin"; "top_itv"; "M64"; "ineq"; "decision"; "stop_itv"; "ifact"; "set_reg"; "DFalse"; "DTrue"; "zmod64"; "smin"; "itv_t"; "smax"; "mk_ext"; "DUnknown_"; "snorm"; "set_pc"; "M63"; "ctx0"; "i32_itv"; "mk_addk"; "mk_alu"; "same_atoms"; "uleq_d"; "linz"; "stv_t"; "MAXU"; "dg_facts"; "in_i32"; "lin_of0"; "mk_alu_f"; "mk_dig"; "atoms_of"; "as_addlit"; "fresh"; "itv_meet"; "lin_lo"; "lin_sub"; "lit_of"; "sitv_d"; "sleq_d"; "small_u_t"; "align_of"; "dg_srels"; "fdig"; "set_freg"; "tbl_entry"; "uleq_core"; "wnorm_t"; "cell_read"; "dg_urels"; "entry_norm"; "lin_exact_s"; "lin_exact_u"; "lin_geq"; "lin_hi"; "list_set"; "lit_is"; "mkDig"; "mk_ctx"; "smeet"; "tbl_get"; "tbl_upd"; "uleq"; "add_fact"; "addk_base"; "align_sum"; "and_lo"; "crel"; "decide_t"; "dg_bits"; "dg_cls"; "dg_nes"; "dg_tbl"; "get_reg"; "is_lit"; "itv_decide_t"; "lin_itv"; "lin_nil"; "lit_fold_t"; "mk_aluw"; "mk_aluw_f"; "mk_ext_f"; "mk_slt_f"; "remove_atoms"; "sadd32_itv"; "sadd_itv"; "sfacts_itv"; "sp_rel"; "strip_zext"; "tf_mentions"; "CDisj"; "CRNone"; "add_cancel"; "addlit_view"; "and_mask_fold2"; "bfact"; "bit_test"; "brels"; "classify_fact"; "dg_pool"; "dg_with_pool"; "endpoints"; "find_obj"; "find_obj_d"; "fld_index"; "get_freg"; "high_mask_j"; "i32max"; "i32min"; "in_bounds_d"; "ineqs_of_rels"; "is_selmask"; "itv"; "lin_add"; "lin_coef"; "lin_decomp"; "lin_eqb"; "lin_neg"; "lin_norm"; "lin_scale"; "lin_sub_negs"; "mk_alu_ln"; "mk_aluw_f_t"; "mk_bits"; "mk_cls"; "mk_ext_f_t"; "mk_md"; "mk_nes"; "mk_slt_f_t"; "pool_round"; "read_cells"; "regZ"; "rels_of"; "set_objs"; "set_resv"; "shr_arg"; "sitv_of_itv"; "small_u"; "split_addr"; "srels_of"; "sub_fold"; "sv_of_lin"; "sv_replace"; "xor_same_base";
"C3magic"; "CLit"; "CUnk"; "add_new"; "align_round"; "align_sv"; "aligned_tighten"; "and_lit"; "and_mask_fold"; "and_mask_gen"; "arr_after_store"; "arr_cells"; "atom_index"; "bits_refine_iter"; "cfact"; "cls_itv"; "cls_shift"; "dg_with_tbl"; "extsv"; "find_sel"; "fld_vars"; "flds_apart"; "instr_at"; "is_lit0"; "itv_body"; "itv_lin"; "itv_sum"; "lin_align"; "lin_constfold"; "lin_decomp_facts"; "lin_decomp_syn"; "lin_gcd"; "lin_lo_pool"; "lin_merge"; "lin_of"; "lin_pos_sum"; "lin_round"; "list_upd"; "lit_align"; "lit_cells"; "lit_rel_skip"; "mk_add_nn"; "mk_alu_nl"; "mk_alu_nn"; "mk_aluw_s"; "mk_ext_s"; "mk_md_1"; "mk_md_f"; "mk_md_f0"; "mk_mdw"; "mk_mdw_f"; "mk_op_f"; "mk_opw_f"; "mk_pool"; "mk_sub_nn"; "ne_pair"; "ne_tighten"; "neq_prim"; "neqs_of"; "nes_refine"; "obj_add_cell"; "obj_store"; "obj_store_d"; "opp_atom"; "prove_sprop"; "prover_decide"; "rel_offset"; "rel_offset0"; "remu_lt"; "roundup"; "same_atoms0"; "same_base_eq"; "sat_depth"; "saturate"; "sclassify_fact"; "sel_case"; "shr_mono"; "sitv_of"; "sleq_by_rel"; "sleq_lin"; "sleq_same"; "slt_retry"; "slt_xor_fold"; "snorm32"; "snormc"; "srels_itv"; "ssub32_itv"; "ssub_itv"; "store_cells"; "store_xs"; "strip_ext"; "stv_body"; "sub_atoms"; "sum_atoms"; "sum_of"; "tbl_find"; "tbl_init"; "tbl_iter"; "tbl_prop_s"; "tbl_prop_u"; "tbl_rounds"; "tbl_shift"; "tf_inst"; "tile_cells"; "tmpl_inst"; "tzb"; "u_of_s"; "uleq_by_rel"; "uleq_by_rel2"; "uleq_lin"; "uleq_same"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep.WithImage"; "load_res"; "step_out"; "LROk"; "StNext"; "load_fresh"; "StStop"; "sym_load"; "havoc_freg"; "image_bytes"; "sym_store"; "LRFail"; "RsUnsupported"; "addr_aligned"; "all_ro"; "amo_k"; "amo_log"; "fcvt_fty"; "fcvt_ity"; "havoc_reg"; "load_arr"; "mk_nanbox"; "msz"; "sym_csr"; "RsEcall"; "RsMem"; "RsNoCode"; "RsSymJump"; "StFork"; "decide_branch"; "fact_lookup"; "frm0b"; "havoc_reg_b"; "image_load"; "immI"; "load_dflt"; "rm_ok"; "ro_load"; "ro_span"; "ro_span_max"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "bv_signed"; "bv_concat"; "@Corelib.Lists.ListDef"; "map"; "nth"; "seq"; "@Stdlib.Lists.List"; "existsb"; "forallb"; "fold_left"; "combine"; "filter"; "@LinuxProcessSemantics.Riscv.Sem"; "low32"; "mul_div"; "alu32"; "alu64"; "branch_taken"; "is_x0"; "@Corelib.Init.Nat"; "add"; "@LinuxProcessSemantics.Riscv.Prelude"; "sext"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "ltb"; "@Stdlib.NArith.BinNat.N"; "mul"; "eqb"; "@LinuxProcessSemantics.LinuxProcessSem.BvBase"; "bytes_le_to_Z"; "@Stdlib.PArith.BinPos.Pos"; "of_nat"; "succ"; "to_nat"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "fetch_word"; "is_ecall"; "@LinuxProcessSemantics.Riscv.DecodeC"; "decode_any"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool.
From Stdlib Require Import PArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Notation "a ||| b" := (if a then true else b) (at level 50, left associativity).
Notation "a &&& b" := (if a then b else false) (at level 40, left associativity).

Import ListNotations.
Open Scope Z_scope.

Section Build.
  Variable segs : list Segment.

  Definition instr_at (pc : Z) : option instr :=
    match fetch_word segs (Z_to_bv 64 pc) with
    | Some w =>
        if is_ecall w then Some Ecall
        else match decode_any w with
             | Some (i, 4%Z) => match i with Ecall => None | _ => Some i end
             | _ => None
             end
    | None => None
    end.
End Build.

Definition lit_of (w : word) : sv := SLit (bv_unsigned w).

Definition M64 : Z := 2 ^ 64.
Definition M63 : Z := 2 ^ 63.
Definition MAXU : Z := 2 ^ 64 - 1.

Definition zmod64 (z : Z) : Z := ltac2:(tb__ "0|0|
S2fS2cL_;S2fS2fL_;S5dZ0Vz;A2S60Vz;S78A2S32X2fx2Vz;S63Vz;S78A2X2fx2").

Definition snormc (z : Z) : Z := ltac2:(tb__ "0|0|
S80Vz;A1S2cS2fS2cL_;S60R1S88A2R1S5fR1S78A2X2fx2Tm;").

Definition snorm (z : Z) : Z := ltac2:(tb__ "0|2|
S63Vz;S61Z2M0Z40A2M1A2S2cS2fS2cL_;S60R1S61G0Z3fA2A2R1S5fR1G1A2X2fx2Tm;").

Definition addk_base (b : sv) (s : Z) : sv := ltac2:(tb__ "0|0|
S86Vs;A1S2cS2fS0L_;S62R1Z0A2Vb;S9S4bVb;S2R1A1A3X2fx2Ts';").

Definition as_addlit (a : sv) : option (sv * Z) := ltac2:(tb__ "0|b|
S0S31S30S0S2cA2M0A1M1La;Va;S2cS3aG0A1M2Lz;S2dG2Li;M3S43S0S0S43G1Lop;R3S0G1Lb0;R1S2cS35G0S33S0S2cR3R1A4A2Lx;G3S43S0S0G2Lb1;La0;M4Lop0;M5G5S44G4Lop0;M6G6S2fS2eS0G2La0;Lw;Lsgn;M7S2dS0S2cG2Lk;Li;Ll;M8X0x8G2G2G2G2G2G2G2G2G2X43xaLb0;Lb;Lop;S43S0S0G2Lb;La0;M9Lop;S44G9Lop;MaGaG7G8X0x8").

Definition mk_addk (a : sv) (k : Z) : sv := ltac2:(tb__ "0|6|
S0S0La;Va;S2cS2S63S5eR1Vk;A2M0S61Z2Z40A2A2A1Lx;S2dS31S30S0S2cA2M1A1S0Lx;S98Va;A1G1G1S0Lp;R1S0S2cSb8R2G0A2Lx;Lb;X30x1Lp;Sb8Va;Vk;A2X31x2M2Li;S43S0S0G2Lb;La0;M3Lop;M4G4S44G3Lop;M5G5S2fS2eS0G2La0;Lw;Lsgn;S2dS0S2cG2Lk0;Li;Ll;X0x8").

Definition addlit_view (e : sv) : sv * Z := ltac2:(tb__ "0|1|
S31S30S0S2cA2M0A1G0Lx;S98Ve;A1G0G0G0Lp;R1S0S2cS33S0S2cR2R1A4Lk;Lb;X30x1Lp;S33S0S2cVe;Z0A4X31x2").

Definition mk_sub_nn (a b : sv) : sv := ltac2:(tb__ "0|1|
S30S0S2cA2S0Lx;M0Sd5Va;A1S0S2cG0Sd5Vb;A1S0S2cS2fS0L_;S4R4R2A2S2S63S5fR3R1A2S61Z2Z40A2A2A1S9S49Va;Vb;A3X2fx2Ly;Lbb;X30x1Lx;Lba;X30x1").

Definition add_cancel (a b : sv) : option sv := ltac2:(tb__ "0|4|
S0S31S0A1M0Lb;Vb;S2cS3aS0A1M1Lz;S2dG1Li;S43S0S0S43G0Lop;R3G1S2fG0L_;S4Va;R1A2S35S0R2A2G1X2fx2G1G1G1G1G1G1G1G1X43xaLa';Lb0;Lop;S43S0S0G1Lb0;La0;M2Lop;S44G2Lop;M3G3S2fS2eS0G1La0;Lw;Lsgn;S2dS0S2cG1Lk;Li;Ll;X0x8").

Definition mk_add_nn (a b : sv) : sv := ltac2:(tb__ "0|2|
S31S0A1S0Lx;M0Sd4Va;Vb;A2S0R1Lr;M1G0Sd4Vb;Va;A2G1S9S4bVa;Vb;A3X31x2X31x2").

Definition mk_alu_nl (op : aluop) (a : sv) (y : Z) : sv := ltac2:(tb__ "0|6|
S43S0Lop;Vop;S8bVa;Vy;A2S8bVa;S67Vy;A1A2S2fS0L_;M0S62S63Vy;Z40M1A2Z0M2A2Va;S9Vop;Va;S2Vy;A1A3M3X2fx2M4G3G3G0S62S63Vy;S61Z2G1A2A2G2A2Va;G3X2fx2M5G4G4G5G0S62S80Vy;A1S91A2Va;G3X2fx2X43xa").

Definition mk_alu_ln (op : aluop) (x : Z) (b : sv) : sv := ltac2:(tb__ "0|3|
S43S0Lop;Vop;S8bVb;Vx;A2S9Vop;S2Vx;A1Vb;A3M0G0G0G0S2fS0L_;M1S62S63Vx;S61Z2Z40A2A2Z0A2Vb;G0X2fx2M2G0G0G2G1S62S80Vx;A1S91A2Vb;G0X2fx2X43xa").

Definition mk_alu_nn (op : aluop) (a b : sv) : sv := ltac2:(tb__ "0|4|
S43S0Lop;Vop;S131Va;Vb;A2S13eVa;Vb;A2S9Vop;Va;Vb;A3M0G0G0S2fS0L_;M1S4Va;Vb;A2M2S2Z0A1G0X2fx2G0G0G1G2Va;G0X2fx2M3G3X43xa").

Definition mk_alu (op : aluop) (a b : sv) : sv := ltac2:(tb__ "0|1b|
S0S0La;Va;S2cS0S0Lb;M0Vb;S2cS9dS1aeVop;S19fQ40M1R2A2S19fG1R1A2A3A1Ly;S2dSf1Vop;R2Vb;A3Li;S43S0S0Sf1Vop;R4Vb;A3M2Lb0;La0;M3Lop0;M4G4S44G3Lop0;M5G5S2fS2eS0G2La0;Lw;Lsgn;S2dS0S2cG2Lk;Li;Ll;X0x8Lx;S2dG0Vb;S2cS132Vop;Va;R1A3Ly;M6S2dS133Vop;Va;Vb;A3M7Li0;M8S43S0S0G7Lb0;M9La0;MaLop0;MbGbS44GaLop0;McGcS2fS2eS0G7La0;Lw;Lsgn;MdS2dS0S2cG7Lk;MeLi0;Ll;X0x8Li;S43S0S0G0Vb;G6S2dG7Li;MfS43S0S0G7Lb1;La1;M10Lop1;M11G11S44G10Lop1;M12G12S2fS2eS0G7La1;M13Lw;Lsgn;S2dS0GeLi;Ll;M14X0x8Lb0;La0;M15Lop0;M16G16S44G15Lop0;M17G17S2fS2eS0G0Vb;G6GfS43S0G9La1;M18Lop0;M19G19S44G18Lop0;M1aG1aS2fS2eG13Lw0;Lsgn0;G14X0x8La0;Lw;Lsgn;S2dS0S2cG0Vb;G6G8GbGbGcGcGdS2dS0S2cG7Lk0;Li0;Ll0;X0x8Lk;Li;Ll;X0x8").

Fixpoint align_of (facts : list sprop) (i : positive) : Z :=
  match facts with
  | [] => 0
  | SPAlign j a :: rest => if Pos.eqb i j then Z.max a (align_of rest i) else align_of rest i
  | _ :: rest => align_of rest i
  end.

Definition high_mask_j (k : Z) : option Z := ltac2:(tb__ "0|1|
S5fS78S80Vk;A1A2S2cS2fS31S2cA1L_;S2fS2fL_;S60Z0R1A2S62R1S61Z2S6aR1A1M0A2A2S32X2fx2S35S2cG0A2S3aS2cA1X2fx2Td;").

Definition and_mask_fold (facts : list sprop) (e : sv) (k : Z) : option sv := ltac2:(tb__ "0|2a|
S2dS34S34S5dZ0M0Vk;A2S60Vk;S61Z2M1Sa1Vfacts;R1A2M2A2A2A2S5dG2Z40M3A2A2Li;S2dS2fFi;S2dS31S2cA1M4G4Lx;Se2Vk;A1S2cS2fG4L_;S34S34S5dG0R1A2S5dR1Sa1Vfacts;R2A2M5A2A2S5dG5G3A2A2S35S2cR1A2S3aS2cA1M6X2fx2Lj;G6X31x2Li;S2dG4Fi;S0S31S0A1M7Le;Ve;S2cS3aS0A1M8Lz;M9S2dS2fG7L_;MaR3R1A1S35S0S2G0A1A2G4G7Lx;MbR2R1A1S2cS35S0S15R2A1A2Lz;G8X31x2X2fx2Li;S43S0S0S43G7Lop;McR3S0G7La;MdR2G9S2dS0G7Lb;MeR2S2cGaR7R2A1MfS35S0S2S6bS63R1S61G1G3A2M10A2Vk;A2A1A2M11GbR6R2A1S2cS35S0Sb8S15R3A1S5fS63R2G10A2M12S63G12S61G1R1A2A2A2A2A2Lj;G8X31x2X2fx2Lc;S2dG8Li0;M13S43S0S0G8Lb0;La0;M14Lop0;M15G15S44G14Lop0;M16G16S2fS2eS0G8La0;Lw;Lsgn;M17S2dS0S2cG8Lk0;M18Li0;Ll;M19X0x8Li;G15G15G16G16G17S2dS0G18Li;Ll;M1aX0x8GdR2S2cGeR2G9S2dGaR7R1A1M1bS35S0S2S6bG12Vk;A2A1A2M1cG8X2fx2Li;S43S0S0S43G7Lop0;M1dR3S0G7La0;M1eR2G9S2dS0G7Lb0;M1fR2S2cGaRbR2A1M20S35S0S2S6bS63S5fR6R1A2G10A2Vk;A2A1A2M21G8X2fx2Lc;G13S43S0S0G8Lb1;La1;M22Lop1;M23G23S44G22Lop1;M24G24S2fS2eS0G8La1;Lw;Lsgn;M25G19X0x8Li;G23G23G24G24G25G1aX0x8G8G8G8G8G8G8G8G8G8X43xaLb0;La0;Lop0;G15G16G16G17G1aX0x8Lc0;S2dG8Li;M26G15G15G16G16G17G1aX0x8G8G8G8G8G8G8G8G8X43xaLb;La;Lop;S43S0S0GcR3GdR2G9S2dGeR2S2cGaS34GfS5dG5Z20M27A2M28A2G11G8X2fx2Lc;G13G15G15G16G16G17G19X0x8Li;G15G15G16G16G17G1aX0x8GdR2S2cGeR2G9S2dGaS34G1bS5dG2G27A2A2G1cG8X2fx2Li;S43S0S0G1dR3G1eR2G9S2dG1fR2S2cGaS34G20G28A2G21G8X2fx2Lc;G13G23G23G24G24G25G19X0x8Li;G23G23G24G24G25G1aX0x8G8G8G8G8G8G8G8G8G8X43xaLb0;La0;Lop0;G15G16G16G17G1aX0x8Lc0;G26G15G15G16G16G17G1aX0x8G8G8G8G8G8G8G8G8X43xaLb;La;Lop;S44S0S0G8Lb;La;Lop;M29G29S2fS2eS0G8La;Lw;Lsgn;G1aX0x8Thighj;Tlowok;").

Fixpoint tzb (fuel : nat) (m : Z) (i : Z) : Z :=
  match fuel with
  | O => 0
  | S f => if Z.testbit m i then 0 else 1 + tzb f m (i + 1)
  end.
Definition lit_align (z : Z) : Z := ltac2:(tb__ "0|1|
S80Vz;A1S2cS2fS2cL_;S62R1Z0M0A2Z40S171U40R1G0A3X2fx2Tm;").

Fixpoint align_sv (facts : list sprop) (e : sv) : Z :=
  match e with
  | SLit z => lit_align z
  | SVar j => Z.max 0 (Z.min 64 (align_of facts j))
  | SAlu ALU_ADD a b | SAlu ALU_SUB a b => Z.min (align_sv facts a) (align_sv facts b)
  | SAlu ALU_AND a b => Z.max (align_sv facts a) (align_sv facts b)

  | SAlu ALU_OR a b => Z.min (align_sv facts a) (align_sv facts b)
  | SAlu ALU_SLL a (SLit k) => Z.min 64 (align_sv facts a + k mod 64)
  | SAlu ALU_SRL a (SLit k) => Z.max 0 (align_sv facts a - k mod 64)
  | SMd M_MUL a b => Z.min 64 (align_sv facts a + align_sv facts b)

  | SAluW ALU_ADD a b | SAluW ALU_SUB a b => Z.min 32 (Z.min (align_sv facts a) (align_sv facts b))
  | _ => 0
  end.

Definition align_norm (p : Z * Z) : Z := ltac2:(tb__ "0|0|
S64S37S2cS2cVp;A3S12eS38S2cS2cVp;A3A1A2").
Fixpoint align_lin (facts : list sprop) (e : sv) : Z * Z :=
  match e with
  | SLit z => (64, z)
  | SAlu ALU_ADD a b =>
      let '(ja, ca) := align_lin facts a in let '(jb, cb) := align_lin facts b in (Z.min ja jb, ca + cb)
  | SAlu ALU_AND a b =>
      (Z.max (align_norm (align_lin facts a)) (align_norm (align_lin facts b)), 0)
  | _ => (align_sv facts e, 0)
  end.
Definition align_sum (facts : list sprop) (e : sv) : Z := align_norm (align_lin facts e).

Definition and_mask_gen (facts : list sprop) (e : sv) (k : Z) : option sv := ltac2:(tb__ "0|1|
S2fS31S0A1L_;S2fS2fL_;S5dZ0M0Vk;A2S60Vk;S61Z2S10dVfacts;Ve;A2A2A2S32X2fx2S35S0S2G0A1A2S3aS0A1X2fx2").

Definition and_mask_fold2 (facts : list sprop) (e : sv) (k : Z) : option sv := ltac2:(tb__ "0|1|
S31S0A1M0G0Lx;S110Vfacts;Ve;Vk;A3S0S35S0R1A2Lr;S111Vfacts;Ve;Vk;A3X31x2").

Definition mk_alu_f (facts : list sprop) (op : aluop) (a b : sv) : sv := ltac2:(tb__ "0|e|
S43S0Lop;Vop;S8cVop;Va;Vb;A3M0G0G0G0G0G0G0G0S0S0Lb;M1Vb;S2cS2fS0L_;S2fS2fL_;S5dZ0R1A2S60R1S61Z2Sb9Vfacts;Va;A2A2A2S32X2fx2S8cS4bVa;S2R1A1A3G0X2fx2Lk;S2dG0Li;M2S43S0S0G0Lb0;La0;M3Lop0;M4G4S44G3Lop0;M5G5S2fS2eS0G0La0;Lw;Lsgn;M6S2dS0S2cG0Lk;Li;Ll;M7X0x8G1Vb;S2cS31S0A1S0Lx;M8Sd6Vfacts;Va;R1A3S0R1Lr;M9G0X31x2Lk;S2dS0S0La;Va;S2cG8Sd6Vfacts;Vb;R1A3G9G0X31x2Lk;G2G4G4G5G5G6G7X0x8MaLi;S43S0S0GaLb0;La0;MbLop0;McGcS44GbLop0;MdGdS2fS2eS0GaLa0;Lw;Lsgn;S2dS0S2cGaLk;Li;Ll;X0x8X43xa").

Definition mk_aluw (op : aluop) (a b : sv) : sv := ltac2:(tb__ "0|8|
S0S0La;Va;S2cS0S0Lb;Vb;S2cS9dS1b2Q20Q40M0S1adVop;S1abS19fG0R2A2A1S1abS19fG0R1A2A1A3A3A1Ly;S2dS23Vop;Va;Vb;A3M1Li;M2S43S0S0G1Lb0;La0;M3Lop0;M4G4S44G3Lop0;M5G5S2fS2eS0G1La0;Lw;Lsgn;M6S2dS0S2cG1Lk;Li;Ll;M7X0x8Lx;G2G4G4G5G5G6G7X0x8").

Definition mk_md (op : mulop) (a b : sv) : sv := ltac2:(tb__ "0|8|
S0S0La;Va;S2cS0S0Lb;Vb;S2cS9dS1acQ40M0Vop;S19fG0R2A2S19fG0R1A2A4A1Ly;S2dS1cVop;Va;Vb;A3M1Li;M2S43S0S0G1Lb0;La0;M3Lop0;M4G4S44G3Lop0;M5G5S2fS2eS0G1La0;Lw;Lsgn;M6S2dS0S2cG1Lk;Li;Ll;M7X0x8Lx;G2G4G4G5G5G6G7X0x8").

Definition mk_mdw (op : mulop) (a b : sv) : sv := ltac2:(tb__ "0|9|
S0S0La;Va;S2cS0S0Lb;Vb;S2cS9dS1b2Q20M0Q40M1S1acG0Vop;S1abS19fG1R2A2A1S1abS19fG1R1A2A1A4A3A1Ly;S2dS22Vop;Va;Vb;A3M2Li;M3S43S0S0G2Lb0;La0;M4Lop0;M5G5S44G4Lop0;M6G6S2fS2eS0G2La0;Lw;Lsgn;M7S2dS0S2cG2Lk;Li;Ll;M8X0x8Lx;G3G5G5G6G6G7G8X0x8").

Definition mk_ext (sgn : bool) (w : N) (a : sv) : sv := ltac2:(tb__ "0|5|
S0S0La;Va;S2cS9dS2aVsgn;Vw;S19fQ40M0R1A2A3A1Lx;S2dS2fS0L_;S34S3fS3dVsgn;A1Vsgn;A2S1b6Vw;G0A2A2Va;S24Vsgn;Vw;Va;A3X2fx2M1Li;S43S0S0G1Lb;La0;M2Lop;M3G3S44G2Lop;M4G4S2fS2eS0G1La0;Lw0;Lsgn0;S2dS0S2cG1Lk;Li;Ll;X0x8").

Definition split_addr (e : sv) : sv * Z := ltac2:(tb__ "0|6|
S0S30S0S2cA2M0Le;Ve;S2cS33S0S2cS2Z0M1A1R1A4La;S2dS31G0A1G0Lx;S98Ve;A1G0G0G0Lp;R1S0S2cS33S0S2cR2R1A4Lk;Lb;X30x1Lp;S33S0S2cVe;G1A4X31x2M2Li;S43S0S0G2Lb;La;M3Lop;M4G4S44G3Lop;M5G5S2fS2eS0G2La;Lw;Lsgn;S2dS0S2cG2Lk;Li;Ll;X0x8").

Fixpoint atoms_of (e : sv) (acc : list sv) (c : Z) : list sv * Z :=
  match e with
  | SLit z => (acc, c + z)
  | SAlu ALU_ADD a b => let '(acc1, c1) := atoms_of a acc c in atoms_of b acc1 c1
  | _ => (e :: acc, c)
  end.

Fixpoint sum_atoms (atoms : list sv) : sv :=
  match atoms with
  | [] => SLit 0
  | [a] => a
  | a :: rest => SAlu ALU_ADD a (sum_atoms rest)
  end.

Definition sum_of (atoms : list sv) (c : Z) : sv := ltac2:(tb__ "0|1|
S36S0A1M0S0Latoms;Vatoms;S2S63Vc;S61Z2Z40A2A2A1S0G0S8bS165Vatoms;A1Vc;A2Ll;Ls;X36x2").

Fixpoint remove_atom (b : sv) (atoms : list sv) : option (list sv) :=
  match atoms with
  | [] => None
  | a :: rest => if sv_eqb a b then Some rest
                 else match remove_atom b rest with
                      | Some rest' => Some (a :: rest')
                      | None => None
                      end
  end.

Definition top_itv : Z * Z := ltac2:(tb__ "0|0|
S33S2cS2cZ0S5fS61Z2Z40A2Z1A2A4").

Definition itv_meet (p q : Z * Z) : Z * Z := ltac2:(tb__ "0|0|
S33S2cS2cS65S37S2cS2cVp;A3S37S2cS2cVq;A3A2S64S38S2cS2cVp;A3S38S2cS2cVq;A3A2A4").

Inductive ifact := IF_range (x : sv) (lo hi : Z) | IF_none.

Definition classify_fact (f : sprop) : ifact := ltac2:(tb__ "0|ba|
S2cS80R1A1Lx;S2cS2cFx;S91S2cS1S7cLf;Vf;S45S0S0S45S7cLc0;M0R3S0S7cLa;M1R2S2cG1R2S2cS74R4R7R1A1M2G2A3Lc;M3S2dS74R3R7R2A1M4G4A3Li;S43S0S0S74R5R9R4A1M5G5A3M6Lb;La0;M7Lop;M8G8S44G7Lop;M9G9S2fS2eS0G6La0;Lw;Lsgn;S2dS0S2cG6Lk;Li;Ll;X0x8Lc;S2dG1R2G3S2dS75Li0;MaS43S0S0S75Lb;MbLa0;McLop;MdGdS44GcLop;MeGeS2fS2eS0S75La0;Lw;Lsgn;MfS2dS0S2cS75Lk;M10Li0;Ll;M11X0x8Li;S43S0S0S43S7cLop;M12R3G1R4S2cS74R6R9R1A1M13G13A3Lc;M14S2dS75Li;M15S43S0GbLa1;M16Lop0;M17G17S44G16Lop0;M18G18S2fS2eS0S75La1;M19Lw;Lsgn;M1aS2dS0G10Li;Ll;M1bX0x8M1cG1cG1cG1cS0S7cLa0;M1dR2S2cS2cS7cLz;M1eR1G1R5S2cS2cS7cLc;M1fR1S74R3Z0M20G20A3M21S2dS74R8RbR2A1M22G22A3Lp;M23G23X2cx3Lc;G15G17G17G18G18G1aG1bX0x8S2dG1R6S2cS74R8RbR1A1M24G24A3Lc;G15G17G17G18G18G1aG1bX0x8Lp;M25G25X2cx3Lz;S2dG1R5S2cS74R7RaR1A1M26G26A3Lc;GaG17G17G18G18G1aG11X0x8Li;S43S0S0G1R7S2cS74R9RcR1A1M27G27A3Lc;M28G15S43S0S0S75Lb0;M29La2;M2aLop1;M2bG2bS44G2aLop1;M2cG2cS2fS2eS0S75La2;M2dLw;Lsgn;M2eG1bX0x8Lb;La1;M2fLop0;M30G30S44G2fLop0;M31G31S2fS2eS0G1R7G28G15S43S0GbLa2;M32Lop0;M33G33S44G32Lop0;M34G34S2fS2eG2dLw0;Lsgn0;M35G1bX0x8La1;Lw;Lsgn;S2dS0S2cG1R7G28GaG17G17G18G18G1aS2dS0S2cS75Lk0;Li0;Ll0;M36X0x8Lk;Li;Ll;X0x8G1cG1cG1cG1cG1cX43xaLa;La0;Lop;S43S0S0G1R4G14G15S43S0G29La1;M37Lop0;M38G38S44G37Lop0;M39G39G1aG1bX0x8Lb;La0;M3aLop;S44G3aLop;M3bG3bS2fS2eS0G1R4G14G15S43G16Lop;M3cG3cS44G16Lop;M3dG3dS2fS2eG19Lw0;Lsgn0;M3eG1bX0x8La0;Lw;Lsgn;S2dS0S2cG1R4G14GaGdGdGeGeGfG36X0x8Lk;Li;Ll;X0x8G1R2S2cG1eR1G1R2S2cS2cS7cLz0;M3fR1S74R4Z1M40R6A3M41S2dS74R4G40R7A3M42Lp;M43G43X2cx3Lz0;S2dS74R3G40R6A3Li;S43S0S0S74R5G40R8A3M44Lb;La0;M45Lop;M46G46S44G45Lop;M47G47S2fS2eS0G44La0;Lw;Lsgn;S2dS0S2cG44Lk;Li;Ll;X0x8S2dG1R3S2cG3fR1S74R5G40R7A3S2dS75Lp0;M48G48X2cx3Lz0;G15GdGdGeGeGfG1bX0x8Lp;M49G49X2cx3Lz;S2dG1R2S2cG1eR1G41S2dS75Lp;M4aG4aX2cx3Lz;GaGdGdGeGeGfG11X0x8Li;S43S0S0G12R3G1R4S2cG1eR1S74R6G40R8A3G4aG4aX2cx3Lz;M4bG15G17G17G18G18G1aG1bX0x8M4cG4cG4cG4cG1dR2S2cG1eR1G1R5S2cG3fR1S74R3G40R9A3G4aG4aX2cx3Lz0;G15G17G17G18G18G1aG1bX0x8S2dG1R6S2cG3fR1S74R8G40RaA3G48G48X2cx3Lz0;G15G17G17G18G18G1aG1bX0x8Lp;M4dG4dX2cx3Lz;S2dG1R5S2cG1eR1S74R7G40R9A3G4aG4aX2cx3Lz;GaG17G17G18G18G1aG11X0x8Li;S43S0S0G1R7S2cG1eR1S74R9G40RbA3G4aG4aX2cx3Lz;M4eG15G2bG2bG2cG2cG2eG1bX0x8Lb;La1;M4fLop0;M50G50S44G4fLop0;M51G51S2fS2eS0G1R7G4eG15G33G33G34G34G35G1bX0x8La1;Lw;Lsgn;S2dS0S2cG1R7G4eGaG17G17G18G18G1aG36X0x8Lk;Li;Ll;X0x8G4cG4cG4cG4cG4cX43xaLa;La0;Lop;S43S0S0G1R4G4bG15G38G38G39G39G1aG1bX0x8Lb;La0;M52Lop;S44G52Lop;M53G53S2fS2eS0G1R4G4bG15G3cG3cG3dG3dG3eG1bX0x8La0;Lw;Lsgn;S2dS0S2cG1R4G4bGaGdGdGeGeGfG36X0x8Lk;Li;Ll;X0x8G1R1S2cG1eR1S74R3S88R5A3G4aG4aX2cx3Lz;G15GdGdGeGeGfG1bX0x8G1R1S2cG1eR1S74R3G20S5fS88G40A2A3M54G4aG4aX2cx3Lz;G15GdGdGeGeGfG1bX0x8G1R2S2cG1R2S2cS74R4G20S5fG2G40A2A3Lc;M55S2dS74R3S5eG4G40A2R6A3Li;S43S0S0S74R5S5eG5G40A2R8A3M56Lb;La0;M57Lop;M58G58S44G57Lop;M59G59S2fS2eS0G56La0;Lw;Lsgn;S2dS0S2cG56Lk;Li;Ll;X0x8Lc;S2dG1R2G55GaGdGdGeGeGfG11X0x8Li;S43S0S0G1R4S2cS74R6G20S5fG13G40A2A3Lc;M5aG15G38G38G39G39G1aG1bX0x8Lb;La0;M5bLop;M5cG5cS44G5bLop;M5dG5dS2fS2eS0G1R4G5aG15G3cG3cG3dG3dG3eG1bX0x8La0;Lw;Lsgn;S2dS0S2c
G1R4G5aGaGdGdGeGeGfG36X0x8Lk;Li;Ll;X0x8G1R2S2cG1R2S2cS74R4G2R6A3Lc;M5eS2dS74R3G20G4A3Li;S43S0S0S74R5G20G5A3M5fLb;La0;M60Lop;M61G61S44G60Lop;M62G62S2fS2eS0G5fLa0;Lw;Lsgn;S2dS0S2cG5fLk;Li;Ll;X0x8Lc;S2dG1R2G5eGaGdGdGeGeGfG11X0x8Li;S43S0S0G1R4S2cS74R6G13R8A3Lc;M63G15G38G38G39G39G1aG1bX0x8Lb;La0;M64Lop;M65G65S44G64Lop;M66G66S2fS2eS0G1R4G63G15G3cG3cG3dG3dG3eG1bX0x8La0;Lw;Lsgn;S2dS0S2cG1R4G63GaGdGdGeGeGfG36X0x8Lk;Li;Ll;X0x8X45x6La;La;Lc0;S1S1S7cLp;R1S45S0S0G0R3G1R2S2cG1eR1G1R2S2cG3fR1G42S2dS74R4G40R8A3Lp0;M67G67X2cx3Lz0;S2dS74R3G40R7A3Li;S43S0S0S74R5G40R9A3M68Lb;La0;M69Lop;M6aG6aS44G69Lop;M6bG6bS2fS2eS0G68La0;Lw;Lsgn;S2dS0S2cG68Lk;Li;Ll;X0x8S2dG1R3S2cG3fR1G44S2dS75Lp1;M6cG6cX2cx3Lz0;G15GdGdGeGeGfG1bX0x8Lp0;M6dG6dX2cx3Lz;S2dG1R2S2cG1eR1G42G48G48X2cx3Lz;GaGdGdGeGeGfG11X0x8Li;S43S0S0G12R3G1R4S2cG1eR1S74R6G40R9A3G48G48X2cx3Lz;M6eG15G17G17G18G18G1aG1bX0x8M6fG6fG6fG6fG1dR2S2cG1eR1G1R5S2cG3fR1S74R3G40RaA3G48G48X2cx3Lz0;G15G17G17G18G18G1aG1bX0x8S2dG1R6S2cG3fR1S74R8G40RbA3G6cG6cX2cx3Lz0;G15G17G17G18G18G1aG1bX0x8Lp0;M70G70X2cx3Lz;S2dG1R5S2cG1eR1S74R7G40RaA3G48G48X2cx3Lz;GaG17G17G18G18G1aG11X0x8Li;S43S0S0G1R7S2cG1eR1S74R9G40RcA3G48G48X2cx3Lz;M71G15G2bG2bG2cG2cG2eG1bX0x8Lb;La1;M72Lop0;M73G73S44G72Lop0;M74G74S2fS2eS0G1R7G71G15G33G33G34G34G35G1bX0x8La1;Lw;Lsgn;S2dS0S2cG1R7G71GaG17G17G18G18G1aG36X0x8Lk;Li;Ll;X0x8G6fG6fG6fG6fG6fX43xaLa;La0;Lop;S43S0S0G1R4G6eG15G38G38G39G39G1aG1bX0x8Lb;La0;M75Lop;S44G75Lop;M76G76S2fS2eS0G1R4G6eG15G3cG3cG3dG3dG3eG1bX0x8La0;Lw;Lsgn;S2dS0S2cG1R4G6eGaGdGdGeGeGfG36X0x8Lk;Li;Ll;X0x8G1R2S2cG1R2S2cS74R4R8R1A1M77G77A3Lc;M78S2dS74R3R8R2A1M79G79A3Li;S43S0S0S74R5RaR4A1M7aG7aA3M7bLb;La0;M7cLop;M7dG7dS44G7cLop;M7eG7eS2fS2eS0G7bLa0;Lw;Lsgn;S2dS0S2cG7bLk;Li;Ll;X0x8Lc;S2dG1R2G78GaGdGdGeGeGfG11X0x8Li;S43S0S0G12R3G1R4S2cS74R6G26G26A3Lc;M7fG15G17G17G18G18G1aG1bX0x8M80G80G80G80G1dR2S2cG1eR1G1R5S2cG1fR1G21S2dS74R8RcR2A1M81G81A3Lp0;M82G82X2cx3Lc;G15G17G17G18G18G1aG1bX0x8S2dG1R6S2cS74R8G27G27A3Lc;G15G17G17G18G18G1aG1bX0x8Lp0;M83G83X2cx3Lz;S2dG1R5S2cS74R7G24G24A3Lc;GaG17G17G18G18G1aG11X0x8Li;S43S0S0G1R7S2cS74R9RdR1A1M84G84A3Lc;M85G15G2bG2bG2cG2cG2eG1bX0x8Lb;La1;M86Lop0;M87G87S44G86Lop0;M88G88S2fS2eS0G1R7G85G15G33G33G34G34G35G1bX0x8La1;Lw;Lsgn;S2dS0S2cG1R7G85GaG17G17G18G18G1aG36X0x8Lk;Li;Ll;X0x8G80G80G80G80G80X43xaLa;La0;Lop;S43S0S0G1R4G7fG15G38G38G39G39G1aG1bX0x8Lb;La0;M89Lop;S44G89Lop;M8aG8aS2fS2eS0G1R4G7fG15G3cG3cG3dG3dG3eG1bX0x8La0;Lw;Lsgn;S2dS0S2cG1R4G7fGaGdGdGeGeGfG36X0x8Lk;Li;Ll;X0x8G1R1S2cG1eR1G54G48G48X2cx3Lz;G15GdGdGeGeGfG1bX0x8G1R1S2cG1eR1S74R3S88R6A3G48G48X2cx3Lz;G15GdGdGeGeGfG1bX0x8G1R2S2cG1R2S2cS74R4G77R7A3Lc;M8bS2dS74R3G20G79A3Li;S43S0S0S74R5G20G7aA3M8cLb;La0;M8dLop;M8eG8eS44G8dLop;M8fG8fS2fS2eS0G8cLa0;Lw;Lsgn;S2dS0S2cG8cLk;Li;Ll;X0x8Lc;S2dG1R2G8bGaGdGdGeGeGfG11X0x8Li;S43S0S0G1R4S2cS74R6G26R9A3Lc;M90G15G38G38G39G39G1aG1bX0x8Lb;La0;M91Lop;M92G92S44G91Lop;M93G93S2fS2eS0G1R4G90G15G3cG3cG3dG3dG3eG1bX0x8La0;Lw;Lsgn;S2dS0S2cG1R4G90GaGdGdGeGeGfG36X0x8Lk;Li;Ll;X0x8G1R2S2cG1R2S2cS74R4G20S5fG77G40A2M94A3Lc;M95S2dS74R3S5eG79G40A2R7A3Li;S43S0S0S74R5S5eG7aG40
A2R9A3M96Lb;La0;M97Lop;M98G98S44G97Lop;M99G99S2fS2eS0G96La0;Lw;Lsgn;S2dS0S2cG96Lk;Li;Ll;X0x8Lc;S2dG1R2G95GaGdGdGeGeGfG11X0x8Li;S43S0S0G1R4S2cS74R6G20S5fG26G40A2A3Lc;M9aG15G38G38G39G39G1aG1bX0x8Lb;La0;M9bLop;M9cG9cS44G9bLop;M9dG9dS2fS2eS0G1R4G9aG15G3cG3cG3dG3dG3eG1bX0x8La0;Lw;Lsgn;S2dS0S2cG1R4G9aGaGdGdGeGeGfG36X0x8Lk;Li;Ll;X0x8X45x6La;La;Lc0;S1S75Lp0;S0GbLa;M9eG9eS0S0S0S7cLb;M9fR1S2cG1eR1S74R3G40R5A3G48G48X2cx3Lz;G15S43S0G29La0;Ma0Lop;Ma1Ga1S44Ga0Lop;Ma2Ga2GfG1bX0x8Lb;La;S75S2dS2cS75La;Li;Ma3X1x7Lp;S0S0G1R2S2cG1R2S2cS74R4G20S5fR6R1A1Ma4G40A2A3Lc;Ma5S2dS74R3S5eR6R2A1Ma6G40A2R5A3Li;S43S0S0S74R5S5eR8R4A1Ma7G40A2R7A3Ma8Lb;La0;Ma9Lop;MaaGaaS44Ga9Lop;MabGabS2fS2eS0Ga8La0;Lw;Lsgn;S2dS0S2cGa8Lk;Li;Ll;X0x8Lc;S2dG1R2Ga5GaGdGdGeGeGfG11X0x8Li;S43S0S0G1R4S2cS74R6G20G94A3Lc;MacG15G38G38G39G39G1aG1bX0x8Lb;La0;MadLop;MaeGaeS44GadLop;MafGafS2fS2eS0G1R4GacG15G3cG3cG3dG3dG3eG1bX0x8La0;Lw;Lsgn;S2dS0S2cG1R4GacGaGdGdGeGeGfG36X0x8Lk;Li;Ll;X0x8La;La;S0S0G1R2S2cG1R2S2cS74R4G20Ga4A3Lc;Mb0S2dS74R3Ga6R5A3Li;S43S0S0S74R5Ga7R7A3Mb1Lb;La0;Mb2Lop;Mb3Gb3S44Gb2Lop;Mb4Gb4S2fS2eS0Gb1La0;Lw;Lsgn;S2dS0S2cGb1Lk;Li;Ll;X0x8Lc;S2dG1R2Gb0GaGdGdGeGeGfG11X0x8Li;S43S0S0G1R4S2cS74R6G20G77A3Lc;Mb5G15G38G38G39G39G1aG1bX0x8Lb;La0;Mb6Lop;Mb7Gb7S44Gb6Lop;Mb8Gb8S2fS2eS0G1R4Gb5G15G3cG3cG3dG3dG3eG1bX0x8La0;Lw;Lsgn;S2dS0S2cG1R4Gb5GaGdGdGeGeGfG36X0x8Lk;Li;Ll;X0x8La;La;S0S0G9fR1S2cS74R3R5R1A1Mb9Gb9A3Lc;G15Ga1Ga1Ga2Ga2GfG1bX0x8Lb;La;S75Ga3X1x7Ttop;Tlit;").

Definition fact_itv (e : sv) (f : sprop) : Z * Z := ltac2:(tb__ "0|1|
S7cS30S2cS2cA2M0Lx;SdaVf;A1S0S2cS2cS2fG0L_;S4R3Ve;A2S33S2cS2cR2R1A4S77X2fx2Lhi;Llo;Lx;S77X7cx2").

Fixpoint facts_itv (facts : list sprop) (e : sv) : Z * Z :=
  match facts with
  | [] => top_itv
  | f :: rest => itv_meet (fact_itv e f) (facts_itv rest e)
  end.

Definition ne_pair (f : sprop) : option (sv * Z) := ltac2:(tb__ "0|21|
S1S31S30S0S2cA2M0A1M1Lf;Vf;S45S0S0S45G1Lc0;M2R3S3aG0A1M3S0G1La;M4R2S2cG4R2S2cS35G0S33S0S2cR4R1A4A2Lc;M5S2dS35G0S33S0S2cR3R2A4A2Li;S43S0S0S35G0S33S0S2cR5R4A4A2M6Lb;La0;M7Lop;M8G8S44G7Lop;M9G9S2fS2eS0G6La0;Lw;Lsgn;S2dS0S2cG6Lk;Li;Ll;X0x8Lc;S2dG4R2G5S2dG3Li0;MaS43S0S0G3Lb;MbLa0;McLop;MdGdS44GcLop;MeGeS2fS2eS0G3La0;Lw;Lsgn;MfS2dS0S2cG3Lk;M10Li0;Ll;X0x8Li;S43S0S0G4R4S2cS35G0S33S0S2cR6R1A4A2Lc;M11S2dG3Li;M12S43S0S0G3Lb0;La1;M13Lop0;M14G14S44G13Lop0;M15G15S2fS2eS0G3La1;M16Lw;Lsgn;S2dS0G10Li;Ll;M17X0x8Lb;La0;M18Lop;M19G19S44G18Lop;M1aG1aS2fS2eS0G4R4G11G12S43S0GbLa1;M1bLop;M1cG1cS44G1bLop;M1dG1dS2fS2eG16Lw0;Lsgn0;G17X0x8La0;Lw;Lsgn;S2dS0S2cG4R4G11GaGdGdGeGeGfS2dS0S2cG3Lk0;Li0;Ll0;X0x8Lk;Li;Ll;X0x8M1eG3G3G3G3X45x6La;La;Lc0;S1S1G1Lp;R1S45S0S0G2R3G1eG3G3G3G3G3X45x6La;La;Lc0;S1G3Lp0;S0GbLa;M1fG1fS0S0G1eLa;La;G3S2dS2cG3La;Li;M20X1x7Lp;G1fG1fG1fG3G20X1x7").

Definition ne_lit (e : sv) (f : sprop) : option Z := ltac2:(tb__ "0|3|
S31S30S0S2cA2M0A1S31S2cA1M1Lx;S13fVf;A1G0G0G1Lp;R1S0S2cS2fG1L_;S4R2Ve;A2S35S2cS80R1A1A2S3aS2cA1M2X2fx2Lc;La;X30x1Lp;G2X31x2").

Fixpoint ne_refine (facts : list sprop) (e : sv) (p : Z * Z) : Z * Z :=
  match facts with
  | [] => p
  | f :: rest =>
      let p1 := match ne_lit e f with
                | Some c => if c =? fst p then (fst p + 1, snd p)
                            else if c =? snd p then (fst p, snd p - 1) else p
                | None => p
                end in
      ne_refine rest e p1
  end.

Definition align_round (facts : list sprop) (e : sv) (p : Z * Z) : Z * Z := ltac2:(tb__ "0|7|
S0S30S2cS2cA2M0Le;Ve;S2cVp;Lz;S2dSa1Vfacts;R1A2S2cS2fG0L_;S34S60Z0R1A2S5dR1Z40A2A2S33S2cS2cS5eS37S2cS2cVp;A3M1S63S67G1A1S61Z2R1A2M2A2A2S5fS38S2cS2cVp;A3M3S63G3G2A2A2A4Vp;X2fx2TA;Lj;S43S0S0Vp;Lb;La;M4Lop;M5G5S44G4Lop;M6G6S2fS2eS0Vp;La;Lw;Lsgn;S2dS0S2cVp;Lk;Li;Ll;X0x8").

Definition and_lo (l m : Z) : Z := ltac2:(tb__ "0|0|
S31S2cA1S2cLx;Se2Vm;A1S2cS5fVl;S63Vl;S61Z2R1A2A2A2Lj;Z0X31x2").

Definition and_lit (e : sv) : option (sv * Z) := ltac2:(tb__ "0|a|
S0S31S30S0S2cA2M0A1M1Le;Ve;S2cS3aG0A1M2Lz;S2dG2Li;M3S43S0S0S43G1Lop;R3G2G2G2G2G2G2G2G2G2S0G1Lb;R1S2cS35G0S33S0S2cR3R1A4A2Lm;G3S43S0S0G2Lb0;La0;M4Lop0;M5G5S44G4Lop0;M6G6S2fS2eS0G2La0;Lw;Lsgn;S2dS0S2cG2Lk;Li;Ll;M7X0x8X43xaLb;La;Lop;S43S0S0G2Lb;La;M8Lop;S44G8Lop;M9G9S2fS2eS0G2La;Lw;Lsgn;G7X0x8").
Definition is_lit0 (e : sv) : bool := ltac2:(tb__ "0|3|
S0S2fLe;Ve;S2cS62S80R1A1Z0A2Lz;S2dS32Li;S43S0S0S32Lb;La;M0Lop;M1G1S44G0Lop;M2G2S2fS2eS0S32La;Lw;Lsgn;S2dS0S2cS32Lk;Li;Ll;X0x8").
Definition bit_test (pos : bool) (x y : sv) : option (sv * Z * bool) := ltac2:(tb__ "0|4|
S2fS31S30S30S0S2cA2M0S2fA2M1A1M2L_;S11fVy;A1S31G0A1G2Lx;S10fVx;A1G0G0G2Lp;R1S0S2cS35G1S33G0S2fS33S0S2cR2R1A4Vpos;A4A2Lm;La;X30x1Lp;S3aG1A1M3X31x2G3X2fx2").
Definition bit_pair (f : sprop) : option (sv * Z * bool) := ltac2:(tb__ "0|8|
S1S31S30S30S0S2cA2S2fA2M0A1M1Lf;Vf;S45S0S0S45G1Lc;M2R3Sd8S32R2R1A3M3Sd8S39R2R1A3M4S3aG0A1M5G5G5G5X45x6Ly;Lx;Lc;S1S1G1Lp;R1S45S0S0G2R3G4G3G5G5G5G5X45x6Ly;Lx;Lc;S1G5Lp0;S0S0G5Lb;La;M6G6S0S0G4Ly;Lx;G5S2dS2cG5La;Li;M7X1x7Lp;G6G6S0S0G3Ly;Lx;G5G7X1x7").

Definition pow2_j (m : Z) : option Z := ltac2:(tb__ "0|1|
S80Vm;A1S2cS2fS31S2cA1L_;S2fS2fL_;S60Z0R1A2S62R1S61Z2S6aR1A1M0A2A2S32X2fx2S35S2cG0A2S3aS2cA1X2fx2Tm';").

Definition bit_refine1 (j : Z) (b : bool) (p : Z * Z) : Z * Z := ltac2:(tb__ "0|9|
S61Z2M0S5eVj;Z1M1A2A2S2cS61G0Vj;A2S2cS37S2cS2cVp;A3S2cS38S2cS2cVp;A3S2cS2fS30S2cS2cA2Lb;Vb;S33S2cS2cS2fS2cL_;M2S60S63R2R4A2M3R3A2M4S5eS5fR2G3A2M5R3A2R2X2fx2G2S60S63R1R4A2M6R3A2M7S5fS5fR1G6A2M8G1A2R1X2fx2A4S33S2cS2cG2G4R2S5eG5R4A2X2fx2G2G7R1S5fS5eG8R3A2G1A2X2fx2A4X2fx2Th;Tl;TH;TP;").

Fixpoint bit_refine (facts : list sprop) (e : sv) (p : Z * Z) : Z * Z :=
  match facts with
  | [] => p
  | f :: rest =>
      let p1 := match bit_pair f with
                | Some (a, m, b) =>
                    if sv_eqb a e then match pow2_j m with Some j => bit_refine1 j b p | None => p end
                    else p
                | None => p
                end in
      bit_refine rest e p1
  end.

Fixpoint bit_refine_iter (fuel : nat) (facts : list sprop) (e : sv) (p : Z * Z) : Z * Z :=
  match fuel with
  | O => p
  | S fuel' =>
      let p' := bit_refine facts e p in
      if (fst p' =? fst p) && (snd p' =? snd p) then p else bit_refine_iter fuel' facts e p'
  end.

Definition shift_itv (c : Z) (pe : Z * Z) (p : Z * Z) : Z * Z := ltac2:(tb__ "0|5|
S86Vc;A1S2cS37S2cS2cVp;A3S2cS38S2cS2cVp;A3S2cS2fS30S2cS2cA2L_;M0S3dS5dR2R1A2A1S77G0S34S60R3Z0M1A2S3fS60S5fR1R3A2M2S61Z2Z40A2M3A2S5dG1S5eS37S2cS2cVpe;A3R3A2A2A2A2S33S2cS2cS5fR2R3A2G2A4M4G0S34S60G1R3A2S3fS5dR3R2A2S60S5eS38S2cS2cVpe;A3R3A2G3A2A2A2G4S77X2fx2X2fx2X2fx2Thi;Tlo;Tc';").

Definition shifted_of (e : sv) (f : sprop) : option (sv * Z) := ltac2:(tb__ "0|a|
S7cS31S30S0S2cA2M0A1M1Lx;SdaVf;A1S0S2cS2cS0G1Lx;R3S2cS3aG0A1M2Lz;S2dG2Li;M3S43S0S0S43G1Lop;R3S0G1Lb;R1S2cS2fG1L_;S4R3Ve;A2S35G0S33S0S2cS9S4bR3S2R1A1A3R1A4A2G2X2fx2Lc;G3S43S0S0G2Lb0;La0;M4Lop0;M5G5S44G4Lop0;M6G6S2fS2eS0G2La0;Lw;Lsgn;S2dS0S2cG2Lk;Li;Ll;M7X0x8G2G2G2G2G2G2G2G2G2X43xaLb;La;Lop;S43S0S0G2Lb;La;M8Lop;S44G8Lop;M9G9S2fS2eS0G2La;Lw;Lsgn;G7X0x8Lhi;Llo;Lx;G2X7cx2").

Fixpoint shift_refine (all facts : list sprop) (e : sv) (p : Z * Z) : Z * Z :=
  match facts with
  | [] => p
  | f :: rest =>
      let p1 := match shifted_of e f with
                | Some (x, c) => itv_meet p (shift_itv c p (facts_itv all x))
                | None => p
                end in
      shift_refine all rest e p1
  end.

Definition rels_of_fact (f : sprop) : list (sv * Z * sv) := ltac2:(tb__ "0|33|
S1S36S30S30S0S2cA2M0S0A2M1A1M2Lf;Vf;S45S0S0S45G2Lc;M3R3S0G2Lx;M4R2S2cS3bG1S33G0S0S33S0S2cR3Z0M5A4R2A4S3bG1S33G0S0S33S0S2cR2G5A4M6R3A4S3eG1A1M7A3M8A3M9Lz;MaS2dG9Li;MbS43S0S0S43G2Lop;McR3S3bG1S33G0S0S33S0S2cR5G5A4MdR4A4S3bG1S33G0S0S33S0S2cR4G5A4R5A4G7A3A3MeGeGeGeS0G2Ly;MfR4S2cS2cG2Lz;M10R1G8S2dS3bG1S33G0S0S33S0S2cR7G5A4M11R6A4S3bG1S33G0S0S33S0S2cR6G5A4M12R7A4G7A3A3M13Lp;M14G14X2cx3Lz;S2dS3bG1S33G0S0G12R5A4S3bG1S33G0S0GdR6A4G7A3A3Li;M15S43S0S0S3bG1S33G0S0S33S0S2cR8G5A4R7A4S3bG1S33G0S0G11R8A4G7A3A3M16Lb;La;M17Lop0;M18G18S44G17Lop0;M19G19S2fS2eS0G16La;Lw;Lsgn;M1aS2dS0S2cG16Lk;Li;Ll;M1bX0x8GeGeGeGeGeX43xaLy;Lx;Lop;S43S0S0GeLb;La;M1cLop;M1dS44G1cLop;M1eG1eS2fS2eS0GeLa;Lw;Lsgn;M1fS2dS0S2cGeLk;Li;Ll;M20X0x8G4R2S2cG7Lz;M21S2dG7Li;M22S43S0S0GcR3G7G7G7G7GfR4S2cG10R1S3bG1S33G0S0S33S0S2cR3Z1M23A4R2A4G7A3M24S2dG7Lp;M25G25X2cx3Lz;G22S43S0S0G7Lb;La;M26Lop0;M27G27S44G26Lop0;M28G28S2fS2eS0G7La;Lw;Lsgn;M29S2dS0S2cG7Lk;Li;Ll;M2aX0x8G7G7G7G7G7X43xaLy;Lx;Lop;S43G26Lop;M2bS44G26Lop;M2cG2cG29G2aX0x8G7G7S3bG1S33G0S0S33S0S2cR2G23A4R1A4G7A3M2dS3bG1S33G0S0S33S0S2cR1G5A4R2A4G7A3M2eX45x6Ly;Lx;Lc;S1S1G2Lp;R1S45S0S0G3R3G4R2G21G22S43S0S0GcR3G7G7G7G7GfR4S2cG10R1G24S2dG7Lp0;M2fG2fX2cx3Lz;G22G27G27G28G28G29G2aX0x8G7G7G7G7G7X43xaLy;Lx;Lop;G2bG2cG2cG29G2aX0x8G4R2GaGbS43S0S0GcR3GeGeGeGeGfR4S2cG10R1G8S2dG13Lp0;M30G30X2cx3Lz;G15G18G18G19G19G1aG1bX0x8GeGeGeGeGeX43xaLy;Lx;Lop;G1dG1eG1eG1fG20X0x8G7G7G2eG2dX45x6Ly;Lx;Lc;S1G7Lp0;G26G26G26G7S2dS2cG7La;Li;M31X1x7Lp;S0S0G2dLy;Lx;S0S0S3bG1S33G0S0G6R1A4M32G7A3Ly;Lx;S0S0S3bG1G32G2eA3Ly;Lx;G7G31X1x7").

Fixpoint boolish (e : sv) : bool :=
  match e with
  | SAlu ALU_SLTU _ _ | SAlu ALU_SLT _ _ => true
  | SAlu ALU_XOR a (SLit 1) => boolish a
  | SAlu ALU_AND a b | SAlu ALU_OR a b => boolish a && boolish b
  | _ => false
  end.
Fixpoint brels (pol : bool) (e : sv) : list (sv * Z * sv) :=
  match e with
  | SAlu ALU_OR a b => if pol then [] else brels false a ++ brels false b
  | SAlu ALU_AND a b => if pol && boolish a && boolish b then brels true a ++ brels true b else []
  | SAlu ALU_XOR a (SLit 1) => if pol then (if boolish a then brels false a else []) else brels true a
  | SAlu ALU_SLTU x y => if pol then [(x, 1, y)] else [(y, 0, x)]
  | _ => []
  end.
Definition bool_rels_of_fact (f : sprop) : list (sv * Z * sv) := ltac2:(tb__ "0|12|
S1S36S30S30S0S2cA2S0A2M0A1M1Lf;Vf;S45S0S0S45G1Lc;M2R3S0G1Lb;M3R1S2cS2cG1Lz;M4R1Sd9S32R3A2M5S2dS3eG0A1M6Lp;M7G7X2cx3Lz;S2dG6Li;M8S43S0S0G6Lb0;La;M9Lop;MaGaS44G9Lop;MbGbS2fS2eS0G6La;Lw;Lsgn;McS2dS0S2cG6Lk;Li;Ll;MdX0x8G3R1S2cG4R1Sd9S39R3A2MeG7G7X2cx3Lz;G8GaGaGbGbGcGdX0x8G6G6G6G6X45x6Lb;Le;Lc;S1S1G1Lp;R1S45S0S0G2R3G3R1S2cG4R1GeS2dG6Lp0;MfGfX2cx3Lz;G8GaGaGbGbGcGdX0x8G3R1S2cG4R1G5GfGfX2cx3Lz;G8GaGaGbGbGcGdX0x8G6G6G6G6X45x6Lb;Le;Lc;S1G6Lp0;S0S0G6Lb;La;M10G10G10G6S2dS2cG6La;Li;M11X1x7Lp;G10G10G10G6G11X1x7").

Fixpoint rels_of (facts : list sprop) : list (sv * Z * sv) :=
  match facts with
  | [] => []
  | f :: rest => (rels_of_fact f ++ bool_rels_of_fact f) ++ rels_of rest
  end.

Definition smin : Z := - 2 ^ 63.
Definition smax : Z := 2 ^ 63 - 1.
Definition stop_itv : Z * Z := ltac2:(tb__ "0|0|
S33S2cS2cS81S83A4").
Definition i32min : Z := - 2 ^ 31.
Definition i32max : Z := 2 ^ 31 - 1.
Definition i32_itv : Z * Z := ltac2:(tb__ "0|0|
S33S2cS2cSe4Se3A4").
Definition in_i32 (p : Z * Z) : bool := ltac2:(tb__ "0|0|
S34S5dSe4S37S2cS2cVp;A3A2S5dS38S2cS2cVp;A3Se3A2A2").

Definition snorm32 (z : Z) : Z := ltac2:(tb__ "0|2|
S63Vz;S61Z2M0Z20A2M1A2S2cS2fS2cL_;S60R1S61G0Z1fA2A2R1S5fR1G1A2X2fx2Tm;").

Definition smeet (p q : Z * Z) : Z * Z := ltac2:(tb__ "0|0|
S33S2cS2cS65S37S2cS2cVp;A3S37S2cS2cVq;A3A2S64S38S2cS2cVp;A3S38S2cS2cVq;A3A2A4").

Definition sitv_of_itv (p : Z * Z) : Z * Z := ltac2:(tb__ "0|5|
S30S2cS2cA2M0G0Lp;Vp;S2cS2cS2fG0L_;M1S3dS5dR2R1A2A1S7bG1S60R1S61Z2M2Z3fA2M3A2S33S2cS2cR2R1A4G1S5dG3R2A2S33S2cS2cS5fR2S61G2Z40A2M4A2S5fR1G4A2A4S7bX2fx2X2fx2X2fx2Lh;Ll;X30x1").

Definition sclassify_fact (f : sprop) : ifact := ltac2:(tb__ "0|6b|
S1S7cLf;Vf;S45S0S0S45S7cLc0;M0R3S0S7cLa;M1R2S2cS75Lz;M2S2dS75Li;M3S43S0S0S43S7cLop;M4R3S75S75S75G1R2S2cG1R2S2cG1R6S2cS2cS7cLz;M5R1S74R5S86R2A1M6S83A3M7S2dS75Lp;M8G8X2cx3Lz;M9G3S43S0S0S75Lb;MaLa0;MbLop0;McGcS44GbLop0;MdGdS2fS2eS0S75La0;Lw;Lsgn;MeS2dS0S2cS75Lk;MfLi;Ll;M10X0x8Lc;S2dG1R6S2cG5R1S74R4S81S86R3A1M11A3M12G8G8X2cx3Lz;S2dS75Li0;M13GcGcGdGdGeS2dS0GfLi0;Ll;M14X0x8Li;S43S0S0G1R8S2cG5R1S74R6S81S86R5A1M15A3M16G8G8X2cx3Lz;M17G3S43S0S0S75Lb0;La1;M18Lop1;M19G19S44G18Lop1;M1aG1aS2fS2eS0S75La1;M1bLw;Lsgn;M1cG10X0x8Lb;La0;M1dLop0;M1eG1eS44G1dLop0;M1fG1fS2fS2eS0G1R8G17G3S43S0GaLa1;M20Lop0;M21G21S44G20Lop0;M22G22S2fS2eG1bLw0;Lsgn0;M23G10X0x8La0;Lw;Lsgn;S2dS0S2cG1R8G17G13GcGcGdGdGeS2dS0S2cS75Lk0;Li0;Ll0;M24X0x8Lk;Li;Ll;X0x8Lc;S2dG1R2S2cG1R6G9G13GcGcGdGdGeG14X0x8Lc;G13GcGcGdGdGeG14X0x8Li;S43S0S0G1R4S2cG1R8S2cG5R1S74R7G6S83A3M25G8G8X2cx3Lz;M26G3G19G19G1aG1aG1cG10X0x8Lc;G3G19G19G1aG1aG1cG10X0x8Lb;La0;M27Lop0;M28G28S44G27Lop0;M29G29S2fS2eS0G1R4S2cG1R8G26G3G21G21G22G22G23G10X0x8Lc;G3G21G21G22G22G23G10X0x8La0;Lw;Lsgn;S2dS0S2cG1R4S2cG1R8G26G13GcGcGdGdGeG24X0x8Lc;G13GcGcGdGdGeG24X0x8Lk;Li;Ll;X0x8S75S75S75S75S75S75X43xaLa;La;Lop;S43GbLop;M2aS44GbLop;M2bG2bGeG10X0x8G1R2G2G3S43S0S0G4R3S75S75S75G1R2S2cG1R2S2cG1R6S2cG5R1S74R5S81S5fG6Z1M2cA2M2dA3M2eG8G8X2cx3Lz;M2fG3GcGcGdGdGeG10X0x8Lc;S2dG1R6S2cG5R1S74R4S5eG11G2cA2S83A3M30G8G8X2cx3Lz;G13GcGcGdGdGeG14X0x8Li;S43S0S0G1R8S2cG5R1S74R6S5eG15G2cA2S83A3M31G8G8X2cx3Lz;M32G3G19G19G1aG1aG1cG10X0x8Lb;La0;M33Lop0;M34G34S44G33Lop0;M35G35S2fS2eS0G1R8G32G3G21G21G22G22G23G10X0x8La0;Lw;Lsgn;S2dS0S2cG1R8G32G13GcGcGdGdGeG24X0x8Lk;Li;Ll;X0x8Lc;S2dG1R2S2cG1R6G2fG13GcGcGdGdGeG14X0x8Lc;G13GcGcGdGdGeG14X0x8Li;S43S0S0G1R4S2cG1R8S2cG5R1S74R7S81G2dA3M36G8G8X2cx3Lz;M37G3G19G19G1aG1aG1cG10X0x8Lc;G3G19G19G1aG1aG1cG10X0x8Lb;La0;M38Lop0;M39G39S44G38Lop0;M3aG3aS2fS2eS0G1R4S2cG1R8G37G3G21G21G22G22G23G10X0x8Lc;G3G21G21G22G22G23G10X0x8La0;Lw;Lsgn;S2dS0S2cG1R4S2cG1R8G37G13GcGcGdGdGeG24X0x8Lc;G13GcGcGdGdGeG24X0x8Lk;Li;Ll;X0x8S75S75S75S75S75S75X43xaLa;La;Lop;G2aG2bG2bGeG10X0x8G1R2S2cG1R2S2cS74R4S81S5fS86R1A1M3bG2cA2M3cA3Lc;M3dS2dS74R3S5eG6G2cA2S83A3Li;S43S0S0S74R5S5eS86R4A1M3eG2cA2S83A3M3fLb;La0;M40Lop;M41G41S44G40Lop;M42G42S2fS2eS0G3fLa0;Lw;Lsgn;S2dS0S2cG3fLk;Li;Ll;X0x8Lc;S2dG1R2G3dG13G2aG2aG2bG2bGeG14X0x8Li;S43S0S0G1R4S2cS74R6S81G3cA3Lc;M43G3S43G18Lop0;M44G44S44G18Lop0;M45G45G1cG10X0x8Lb;La0;M46Lop;M47G47S44G46Lop;M48G48S2fS2eS0G1R4G43G3S43G20Lop;M49G49S44G20Lop;M4aG4aG23G10X0x8La0;Lw;Lsgn;S2dS0S2cG1R4G43G13G2aG2aG2bG2bGeG24X0x8Lk;Li;Ll;X0x8M4bG1R2S2cG1R2S2cS74R4G3bS83A3Lc;M4cS2dS74R3S81G6A3Li;S43S0S0S74R5S81G3eA3M4dLb;La0;M4eLop;M4fG4fS44G4eLop;M50G50S2fS2eS0G4dLa0;Lw;Lsgn;S2dS0S2cG4dLk;Li;Ll;X0x8Lc;S2dG1R2G4cG13G2aG2aG2bG2bGeG14X0x8Li;S43S0S0G1R4S2cS74R6G3bS83A3Lc;M51G3G44G44G45G45G1cG10X0x8Lb;La0;M52Lop;M53G53S44G52Lop;M54G54S2fS2eS0G1R4G51G3G49G49G4aG4aG23G10X0x8La0;Lw;Lsgn;S2dS0S2cG1R4G51G13G2aG2aG2bG2bGeG24X0x8Lk;Li;Ll;X0x8M55S75S75X45x6La;La;Lc0;S1S1S7cLp;R1S45S0S0G0R3G1R2G2G3S43S0S0G4R3S75S75S75G1R2S2cG1R2S2cG1R6S2cG5R1G2eS2dS75Lp0;M56G56X2cx3Lz;
M57G3GcGcGdGdGeG10X0x8Lc;S2dG1R6S2cG5R1G30G56G56X2cx3Lz;G13GcGcGdGdGeG14X0x8Li;S43S0S0G1R8S2cG5R1G31G56G56X2cx3Lz;M58G3G19G19G1aG1aG1cG10X0x8Lb;La0;M59Lop0;M5aG5aS44G59Lop0;M5bG5bS2fS2eS0G1R8G58G3G21G21G22G22G23G10X0x8La0;Lw;Lsgn;S2dS0S2cG1R8G58G13GcGcGdGdGeG24X0x8Lk;Li;Ll;X0x8Lc;S2dG1R2S2cG1R6G57G13GcGcGdGdGeG14X0x8Lc;G13GcGcGdGdGeG14X0x8Li;S43S0S0G1R4S2cG1R8S2cG5R1G36G56G56X2cx3Lz;M5cG3G19G19G1aG1aG1cG10X0x8Lc;G3G19G19G1aG1aG1cG10X0x8Lb;La0;M5dLop0;M5eG5eS44G5dLop0;M5fG5fS2fS2eS0G1R4S2cG1R8G5cG3G21G21G22G22G23G10X0x8Lc;G3G21G21G22G22G23G10X0x8La0;Lw;Lsgn;S2dS0S2cG1R4S2cG1R8G5cG13GcGcGdGdGeG24X0x8Lc;G13GcGcGdGdGeG24X0x8Lk;Li;Ll;X0x8S75S75S75S75S75S75X43xaLa;La;Lop;G2aG2bG2bGeG10X0x8G1R2G2G3S43S0S0G4R3S75S75S75G1R2S2cG1R2S2cG1R6S2cG5R1G7G56G56X2cx3Lz;M60G3GcGcGdGdGeG10X0x8Lc;S2dG1R6S2cG5R1G12G56G56X2cx3Lz;G13GcGcGdGdGeG14X0x8Li;S43S0S0G1R8S2cG5R1G16G56G56X2cx3Lz;M61G3G19G19G1aG1aG1cG10X0x8Lb;La0;M62Lop0;M63G63S44G62Lop0;M64G64S2fS2eS0G1R8G61G3G21G21G22G22G23G10X0x8La0;Lw;Lsgn;S2dS0S2cG1R8G61G13GcGcGdGdGeG24X0x8Lk;Li;Ll;X0x8Lc;S2dG1R2S2cG1R6G60G13GcGcGdGdGeG14X0x8Lc;G13GcGcGdGdGeG14X0x8Li;S43S0S0G1R4S2cG1R8S2cG5R1G25G56G56X2cx3Lz;M65G3G19G19G1aG1aG1cG10X0x8Lc;G3G19G19G1aG1aG1cG10X0x8Lb;La0;M66Lop0;M67G67S44G66Lop0;M68G68S2fS2eS0G1R4S2cG1R8G65G3G21G21G22G22G23G10X0x8Lc;G3G21G21G22G22G23G10X0x8La0;Lw;Lsgn;S2dS0S2cG1R4S2cG1R8G65G13GcGcGdGdGeG24X0x8Lc;G13GcGcGdGdGeG24X0x8Lk;Li;Ll;X0x8S75S75S75S75S75S75X43xaLa;La;Lop;G2aG2bG2bGeG10X0x8G55G4bS75S75X45x6La;La;Lc0;S1S75Lp0;S0GaLa;M69G69G69S75S2dS2cS75La;Li;M6aX1x7Lp;G69G69G69S75G6aX1x7").

Definition sfact_itv (e : sv) (f : sprop) : Z * Z := ltac2:(tb__ "0|1|
S7cS30S2cS2cA2M0Lx;S152Vf;A1S0S2cS2cS2fG0L_;S4R3Ve;A2S33S2cS2cR2R1A4S7bX2fx2Lhi;Llo;Lx;S7bX7cx2").

Fixpoint sfacts_itv (facts : list sprop) (e : sv) : Z * Z :=
  match facts with
  | [] => stop_itv
  | f :: rest => smeet (sfact_itv e f) (sfacts_itv rest e)
  end.

Definition sadd_itv (p q : Z * Z) : Z * Z := ltac2:(tb__ "0|4|
S5eS37S2cS2cVp;A3M0S37S2cS2cVq;A3M1A2S2cS5eS38S2cS2cVp;A3M2S38S2cS2cVq;A3M3A2S2cS2fS30S2cS2cA2L_;S34S34S34S5dG0G2A2S5dG1G3A2A2S5dS81R2A2A2S5dR1S83A2A2S33S2cS2cR2R1A4S7bX2fx2Th;Tl;").
Definition ssub_itv (p q : Z * Z) : Z * Z := ltac2:(tb__ "0|4|
S5fS37S2cS2cVp;A3M0S38S2cS2cVq;A3M1A2S2cS5fS38S2cS2cVp;A3M2S37S2cS2cVq;A3M3A2S2cS2fS30S2cS2cA2L_;S34S34S34S5dG0G2A2S5dG3G1A2A2S5dS81R2A2A2S5dR1S83A2A2S33S2cS2cR2R1A4S7bX2fx2Th;Tl;").

Definition sadd32_itv (p q : Z * Z) : Z * Z := ltac2:(tb__ "0|5|
S5eS37S2cS2cVp;A3M0S37S2cS2cVq;A3M1A2S2cS5eS38S2cS2cVp;A3M2S38S2cS2cVq;A3M3A2S2cS2fS30S2cS2cA2L_;S34S34S34S34S5dG0G2A2S5dG1G3A2A2S93Vp;A1A2S93Vq;A1A2S93S33S2cS2cR2R1A4M4A1A2G4S8aX2fx2Th;Tl;").
Definition ssub32_itv (p q : Z * Z) : Z * Z := ltac2:(tb__ "0|5|
S5fS37S2cS2cVp;A3M0S38S2cS2cVq;A3M1A2S2cS5fS38S2cS2cVp;A3M2S37S2cS2cVq;A3M3A2S2cS2fS30S2cS2cA2L_;S34S34S34S34S5dG0G2A2S5dG3G1A2A2S93Vp;A1A2S93Vq;A1A2S93S33S2cS2cR2R1A4M4A1A2G4S8aX2fx2Th;Tl;").

Definition srels_of_fact (f : sprop) : list (sv * Z * sv) := ltac2:(tb__ "0|32|
S1S36S30S30S0S2cA2M0S0A2M1A1M2Lf;Vf;S45S0S0S45G2Lc;M3R3S0G2Lx;M4R2S2cS3bG1S33G0S0S33S0S2cR3Z0M5A4R2A4S3bG1S33G0S0S33S0S2cR2G5A4M6R3A4S3eG1A1M7A3M8A3M9Lz;MaS2dG9Li;MbS43S0S0S43G2Lop;McR3S3bG1S33G0S0S33S0S2cR5G5A4MdR4A4S3bG1S33G0S0S33S0S2cR4G5A4R5A4G7A3A3MeGeGeS0G2Ly;MfR4S2cS2cG2Lz;M10R1G8S2dS3bG1S33G0S0S33S0S2cR7G5A4M11R6A4S3bG1S33G0S0S33S0S2cR6G5A4M12R7A4G7A3A3M13Lp;M14G14X2cx3Lz;S2dS3bG1S33G0S0G12R5A4S3bG1S33G0S0GdR6A4G7A3A3Li;M15S43S0S0S3bG1S33G0S0S33S0S2cR8G5A4R7A4S3bG1S33G0S0G11R8A4G7A3A3M16Lb;La;M17Lop0;M18G18S44G17Lop0;M19G19S2fS2eS0G16La;Lw;Lsgn;M1aS2dS0S2cG16Lk;Li;Ll;M1bX0x8GeGeGeGeGeGeX43xaLy;Lx;Lop;S43S0S0GeLb;La;M1cLop;M1dS44G1cLop;M1eG1eS2fS2eS0GeLa;Lw;Lsgn;M1fS2dS0S2cGeLk;Li;Ll;M20X0x8G4R2S2cG7Lz;M21S2dG7Li;M22S43S0S0GcR3G7G7G7GfR4S2cG10R1S3bG1S33G0S0S33S0S2cR3Z1M23A4R2A4G7A3M24S2dG7Lp;M25G25X2cx3Lz;G22S43S0S0G7Lb;La;M26Lop0;M27G27S44G26Lop0;M28G28S2fS2eS0G7La;Lw;Lsgn;M29S2dS0S2cG7Lk;Li;Ll;M2aX0x8G7G7G7G7G7G7X43xaLy;Lx;Lop;S43G26Lop;M2bS44G26Lop;M2cG2cG29G2aX0x8S3bG1S33G0S0S33S0S2cR2G23A4R1A4G7A3M2dS3bG1S33G0S0S33S0S2cR1G5A4R2A4G7A3M2eG7G7X45x6Ly;Lx;Lc;S1S1G2Lp;R1S45S0S0G3R3G4R2G21G22S43S0S0GcR3G7G7G7GfR4S2cG10R1G24S2dG7Lp0;M2fG2fX2cx3Lz;G22G27G27G28G28G29G2aX0x8G7G7G7G7G7G7X43xaLy;Lx;Lop;G2bG2cG2cG29G2aX0x8G4R2GaGbS43S0S0GcR3GeGeGeGfR4S2cG10R1G8S2dG13Lp0;M30G30X2cx3Lz;G15G18G18G19G19G1aG1bX0x8GeGeGeGeGeGeX43xaLy;Lx;Lop;G1dG1eG1eG1fG20X0x8G2eG2dG7G7X45x6Ly;Lx;Lc;S1G7Lp0;G26G26G26G7S2dS2cG7La;Li;M31X1x7Lp;G26G26S0S0S3bG1S33G0S0G6R1A4G2eA3Ly;Lx;G7G31X1x7").

Fixpoint srels_of (facts : list sprop) : list (sv * Z * sv) :=
  match facts with
  | [] => []
  | f :: rest => srels_of_fact f ++ srels_of rest
  end.

Definition srel_itv1 (facts : list sprop) (e : sv) (r : sv * Z * sv) : Z * Z := ltac2:(tb__ "0|3|
S30S30S0S2cA2M0S0A2S30S2cS2cA2M1Lr;Vr;G0S0G0G1Lp;R2S0S2cS2fG1L_;M2S4R3Ve;A2S33S2cS2cS5eS37S2cS2cSceVfacts;R2A2A3R1A2S83A4G2S4R2Ve;A2S33S2cS2cS81S5fS38S2cS2cSceVfacts;R3A2A3R1A2A4S7bX2fx2X2fx2Ld;Lx;X30x1Ly;Lp;X30x1").

Fixpoint srels_itv (facts : list sprop) (rels : list (sv * Z * sv)) (e : sv) : Z * Z :=
  match rels with
  | [] => stop_itv
  | r :: t => smeet (srel_itv1 facts e r) (srels_itv facts t e)
  end.

Definition lin := list (Z * sv).
Definition ineq := (lin * Z)%type.

Definition tbl_entry : ltac2:(tb__ "0|0|
E") := ltac2:(tb__ "0|1|
S30S0S30S30S2cS2cA2M0G0A2A2").

Definition cfact : ltac2:(tb__ "0|0|
E") := ltac2:(tb__ "0|0|
S30S0S30S2cS2cA2A2").
Definition nfact := (sv * Z)%type.
Definition bfact := (sv * Z * bool)%type.

Fixpoint mk_cls (facts : list sprop) : list cfact :=
  match facts with
  | [] => []
  | f :: rest => match classify_fact f with
                 | IF_range x lo hi => (x, (lo, hi)) :: mk_cls rest
                 | IF_none => mk_cls rest
                 end
  end.

Fixpoint mk_nes (facts : list sprop) : list nfact :=
  match facts with
  | [] => []
  | f :: rest => match ne_pair f with
                 | Some (a, c) => (a, zmod64 c) :: mk_nes rest
                 | None => mk_nes rest
                 end
  end.

Fixpoint mk_bits (facts : list sprop) : list bfact :=
  match facts with
  | [] => []
  | f :: rest => match bit_pair f with
                 | Some (a, m, b) => match pow2_j m with
                                     | Some j => (a, j, b) :: mk_bits rest
                                     | None => mk_bits rest
                                     end
                 | None => mk_bits rest
                 end
  end.

Fixpoint cls_itv (cls : list cfact) (e : sv) : Z * Z :=
  match cls with
  | [] => top_itv
  | (x, p) :: rest => if sv_eqb x e then itv_meet p (cls_itv rest e) else cls_itv rest e
  end.

Fixpoint cls_shift (all cls : list cfact) (e : sv) (p : Z * Z) : Z * Z :=
  match cls with
  | [] => p
  | (SAlu ALU_ADD a (SLit c), _) :: rest =>
      cls_shift all rest e (if sv_eqb a e then itv_meet p (shift_itv c p (cls_itv all (SAlu ALU_ADD a (SLit c)))) else p)
  | _ :: rest => cls_shift all rest e p
  end.

Fixpoint nes_refine (nes : list nfact) (e : sv) (p : Z * Z) : Z * Z :=
  match nes with
  | [] => p
  | (a, c) :: rest =>
      let p1 := if sv_eqb a e then
                  (if c =? fst p then (fst p + 1, snd p)
                   else if c =? snd p then (fst p, snd p - 1) else p)
                else p in
      nes_refine rest e p1
  end.

Fixpoint bits_refine (bits : list bfact) (e : sv) (p : Z * Z) : Z * Z :=
  match bits with
  | [] => p
  | (a, j, b) :: rest => bits_refine rest e (if sv_eqb a e then bit_refine1 j b p else p)
  end.

Fixpoint bits_refine_iter (fuel : nat) (bits : list bfact) (e : sv) (p : Z * Z) : Z * Z :=
  match fuel with
  | O => p
  | S fuel' =>
      let p' := bits_refine bits e p in
      if (fst p' =? fst p) &&& (snd p' =? snd p) then p else bits_refine_iter fuel' bits e p'
  end.

Record fdig := mkDig {
  dg_facts : list sprop;
  dg_cls   : list cfact;
  dg_nes   : list nfact;
  dg_bits  : list bfact;
  dg_urels : list (sv * Z * sv);
  dg_srels : list (sv * Z * sv);
  dg_tbl   : list tbl_entry;
  dg_pool  : list ineq }.

Definition dg_with_tbl (dg : fdig) (tbl : list tbl_entry) : fdig := ltac2:(tb__ "0|0|
Sb1S92Vdg;A1SbeVdg;A1SbfVdg;A1SbdVdg;A1Sa9Vdg;A1Sa2Vdg;A1Vtbl;SdbVdg;A1A8").

Definition ctx0 (facts : list sprop) : fdig := ltac2:(tb__ "0|0|
Sb1Vfacts;Sf4Vfacts;A1Sf7Vfacts;A1Sf3Vfacts;A1SfcVfacts;A1S103Vfacts;A1S3eSa5A1S3eS79A1A8").

Fixpoint tbl_find (tbl : list tbl_entry) (e : sv) : option ((Z * Z) * (Z * Z)) :=
  match tbl with
  | [] => None
  | (x, v) :: rest => if sv_eqb x e then Some v else tbl_find rest e
  end.

Fixpoint tbl_shift (tbl : list tbl_entry) (e : sv) (p : Z * Z) : Z * Z :=
  match tbl with
  | [] => p
  | (SAlu ALU_ADD a (SLit c), (pu, _)) :: rest =>
      tbl_shift rest e (if sv_eqb a e then itv_meet p (shift_itv c p pu) else p)
  | _ :: rest => tbl_shift rest e p
  end.

Definition itv_body (rec : sv -> Z * Z) (dg : fdig) (e : sv) : Z * Z := ltac2:(tb__ "0|5f|
S92Vdg;A1S36S1A1S0S30S2cS2cA2M0Le;Ve;S2cS80R1A1M1S2cS33S2cS2cR1R1A4Tm;Lz;S2dS77Li;M2S43S0S0S43G0Lop;M3R3S0G0Lb;M4R1S2cG0G0Lx;M5Vrec;R3A1M6S2cS2cS15cR3A1S2cS2fG0L_;M7S5dZ0M8R1A2G7S60S5eR2R1A2M9S78A2S33S2cS2cS5eR3R1A2MaG9A4MbS77X2fx2G7S5dG8GaA2GbG7S34S5dR3R2A2McS60G9G8A2A2S33S2cS2cS5eGaS78A2S5eG9S78A2A4S77X2fx2X2fx2X2fx2Tc';Lh;Ll;X30x1Lc;S2dG5G6S2cS2cG5Vrec;R4A1MdS2cS2cG7S60GaS78A2MeS33S2cS2cS5eR4R2A2GaA4S77X2fx2Lhb;Llb;MfX30x1Lha;Lla;X30x1Li;S43S0S0G5Vrec;R5A1M10S2cS2cG5Vrec;R6A1M11GfX30x1Lha;Lla;X30x1M12Lb0;La0;M13Lop0;M14G14S44G13Lop0;M15G15S2fS2eS0G12La0;Lw;Lsgn;S2dS0S2cG12Lk;Li;Ll;X0x8G5Vrec;R2A1M16S2cS2cG5G6S2cS2cG7S5dR1R4A2M17S33S2cS2cS5fR4R1A2M18S5fR3R2A2M19A4G7S2fS2fL_;M1aS5dR4R3A2M1bG1aS5dR2R1A2M1cG1aS60R3R2A2M1dS60R1S78A2M1eS32X2fx2S32X2fx2S32X2fx2S33S2cS2cS5eG18S78A2S5eG19S78A2A4S77X2fx2X2fx2Lhb;Llb;X30x1Lha;Lla;X30x1G4R1S2cG5G6S2cS2cS63R3Z40M1fA2M20S2cG7S60S70R2R1A2M21S78A2S33S2cS2cS70R3R1A2G21A4S77X2fx2Tk';Lh;Ll;X30x1Lk;G2S43S0S0S77Lb0;La0;M22Lop0;M23G23S44G22Lop0;M24G24S2fS2eS0S77La0;Lw;Lsgn;M25S2dS0S2cS77Lk;Li;Ll;M26X0x8G5G16S2cS2cG5G6S2cS2cG7S3dS34S34S34G1bG1cA2M27S60R3S88A2M28A2S60R1S88A2M29A2A1S33S2cS2cG8Z1M2aA4M2bG7G1dS33S2cS2cG2aG2aA4G7G17S33S2cS2cG8G8A4G2bX2fx2X2fx2M2cX2fx2Lhb;Llb;X30x1Lha;Lla;X30x1G5G16S2cS2cG5G6S2cS2cG7S3dG27A1G2bG2cX2fx2Lhb;Llb;X30x1Lha;Lla;X30x1G4R1S2cG7S62G1S91A2G5G6S2cS2cS33S2cS2cS5fS91R1A2S5fS91R2A2A4Lh;Ll;X30x1G5G6S2cS2cG7G1aG1cS60S5eR1S80R3A1M2dA2M2eS78A2S32X2fx2S33S2cS2cG8S64G2eS5fS61Z2M2fS5eS6aS65G2aS65R1G2dA2A2A1G2aA2A2G2aA2A2A4S77X2fx2Lh;Ll;X30x1X2fx2Lm;S2dG5G6S2cS2cG5GdS2cS2cG7G1aG1bG1aG1cGeS32X2fx2S32X2fx2S33S2cS2cG8S64GaS5fS61G2fS5eS6aS65G2aS65R3R1A2A2A1G2aA2A2G2aA2A2A4S77X2fx2Lhb;Llb;M30X30x1Lha;Lla;X30x1Li;S43S0S0G5G10S2cS2cG5G11G30X30x1Lha;Lla;X30x1M31Lb0;La0;M32Lop0;M33G33S44G32Lop0;M34G34S2fS2eS0G31La0;Lw;Lsgn;S2dS0S2cG31Lk;Li;Ll;X0x8G4R1S2cG5G6S2cS2cG20S2cS33S2cS2cS69R3R1A2S69R2R1A2A4M35Tk';Lh;Ll;X30x1Lk;G2G23G23G24G24G25G26X0x8G4R1S2cG5G6S2cS2cG20S2cG7G1aGcS60R2S88A2S32X2fx2G35S77X2fx2Tk';Lh;Ll;X30x1Lk;G2G23G23G24G24G25G26X0x8G5G16S2cS2cG5G6S2cS2cS33S2cS2cS65R4R2A2S64GaS91A2A4Lhb;Llb;X30x1Lha;Lla;X30x1S0G0La;R2S2cG4R2S2cG5GdS2cS2cS33S2cS2cSbaR2R3A2S64R1G2dA2A4Lh;Ll;M36X30x1Lm;M37S2dG5G6S2cS2cS33S2cS2cSbaR2R4A2S64R1S80R4A1A2A4Lh;Ll;X30x1Li;S43S0S0G5G10S2cS2cS33S2cS2cSbaR2R6A2S64R1S80R6A1A2A4Lh;Ll;X30x1M38Lb0;La0;M39Lop0;M3aG3aS44G39Lop0;M3bG3bS2fS2eS0G38La0;Lw;Lsgn;S2dS0S2cG38Lk;Li;Ll;X0x8Lm;S2dG4R2G37S2dG5GdS2cS2cG5G10S2cS2cG7G1aG1bG1cS32X2fx2S33S2cS2cG8S64R3R1A2A4S77X2fx2Lhb;Llb;M3cX30x1Lha;Lla;X30x1Li0;S43S0S0G5G11S2cS2cG5Vrec;R7A1G3cX30x1Lha;Lla;X30x1M3dLb0;La0;M3eLop0;M3fG3fS44G3eLop0;M40G40S2fS2eS0G3dLa0;Lw;Lsgn;S2dS0S2cG3dLk;Li0;Ll;X0x8Li;S43S0S0G4R4S2cG5G11G36X30x1Lm;M41S2dG3dLi;M42S43S0S0G5Vrec;R8A1S2cS2cG5Vrec;R9A1G3cX30x1Lha;Lla;X30x1M43Lb1;La1;M44Lop1;M45G45S44G44Lop1;M46G46S2fS2eS0G43La1;M47Lw;Lsgn;S2dS0S2cG43Lk;Li;Ll;M48X0x8Lb0;La0;M49Lop0;M4aG4aS44G49Lop0;M4bG4bS2fS2eS0G4R4G41G42S43S0S0G43Lb0;M4cLa1;M4dLop0;M4eG4eS44G4dLop0;M4fG4fS2fS2eG47Lw0;Lsgn0;G48X0x8La0;Lw;Lsgn;S2dS0
S2cG4R4G41S2dG3dLi0;S43S0G4cLa0;M50Lop0;M51G51S44G50Lop0;M52G52S2fS2eS0G43La0;Lw;Lsgn;S2dS0S2cG43Lk0;Li0;Ll0;X0x8Lk;Li;Ll;X0x8X43xaLb;La;Lop;S43S0S0G3R3S77S77S77S77S77S77G4R1S2cG5G6S2cS2cG7G1aG1cG1aS60R1S61G2fZ20M53A2A2G1aS5dG2aR3A2S60R3G53A2S32X2fx2S32X2fx2S32X2fx2S33S2cS2cS69R2R3A2S69R1R3A2A4S77X2fx2Lh;Ll;X30x1Lk;G2G23G23G24G24G25G26X0x8S77S77S77X43xaLb;La;Lop;S44S0S0S44G0Lop;M54R3G5G16S2cS2cG5G6S2cS2cG7S60S66R3R1A2M55S78A2S33S2cS2cS66S65G8R4A2S65G8R2A2A2M56G55A4S77X2fx2Lhb;Llb;X30x1Lha;Lla;X30x1G5G16S2cS2cG5G6S2cS2cG7G1aG1bG1aG1cG1aG28G29S32X2fx2S32X2fx2S32X2fx2S33S2cS2cS69G56G1fA2S69G55G1fA2A4M57S77X2fx2Lhb;Llb;X30x1Lha;Lla;X30x1S77G4R1S2cG5G6S2cS2cG2dS2cR1S2cG7G1aG1bG1aG1cG1aS60R3S78A2G1eS32X2fx2S32X2fx2S32X2fx2G57S77X2fx2Thb;Tlb;Lha;Lla;X30x1Lc;G2G23G23G24G24G25G26X0x8S77S77S77G5G16S2cS2cG5G6S2cS2cG7G1aG1bS60G8R2A2M58S32X2fx2S33S2cS2cG8S64R3S5fR1G2aA2A2A4M59S77X2fx2Lhb;Llb;X30x1Lha;Lla;X30x1X44x8Lb;La;Lop;S44S0S0G54R3S77S77S77S77S77S77S77G5G16S2cS2cG5G6S2cS2cG7G1aG1bG1aG58S60R1S61G2fZ1fA2A2S32X2fx2S32X2fx2G59S77X2fx2Lhb;Llb;X30x1Lha;Lla;X30x1X44x8Lb;La;Lop;S2fS2eS0S2fG0Lsgn;R3G5Vrec;R1A1M5aS2cS2cG7G1aG1cG1aS60G8S6dR4A1M5bA2G1aS5dG5bG1fA2M5cS60R1S61G2fS5fG5bG2aA2A2A2S32X2fx2S32X2fx2S32X2fx2S33S2cS2cR2R1A4M5dS77X2fx2Lh;Ll;X30x1G5G5aS2cS2cG7S60R1S61G2fG5bA2M5eA2G5dG7G5cS33S2cS2cG8S5fG5eG2aA2A4S77X2fx2X2fx2Lh;Ll;X30x1X2fx2La;Lw;Lsgn;G26X0x8G0SbeVdg;A1S36S116A1SbdVdg;A1S36Sd7A1S10cR4Ve;S115S42S40Sd7R1A2A1R1Ve;S143SbfVdg;A1Ve;S16dSc0Vdg;A1Ve;S118R2R2Ve;S9aR3S117R2Ve;A2A2A4A3A3A4A3Tbits;Tcls;Tstructural;Tfacts;").

Fixpoint itv_t (dg : fdig) (e : sv) : Z * Z :=
  match tbl_find (dg_tbl dg) e with
  | Some v => fst v
  | None =>
      itv_body (fun a => itv_t dg a) dg e
  end.

Definition itv_node (dg : fdig) (e : sv) : Z * Z := ltac2:(tb__ "0|0|
S120S0S82Vdg;R1A2La;Vdg;Ve;A3").

Definition stv_body (rec : sv -> Z * Z) (dg : fdig) (e : sv) : Z * Z := ltac2:(tb__ "0|23|
S92Vdg;A1S36S1A1S0S30S2cS2cA2M0Le;Ve;S2cS33S2cS2cS86R1A1M1G1A4M2Lz;S2dS7bLi;M3S43S0S0S43G0Lop;M4R3S0G0Lb;M5R1S2cScdVrec;R3A1M6G2A2Lc;S2dScdG6Vrec;R2A1M7A2Li;S43S0S0ScdVrec;R5A1M8Vrec;R4A1M9A2MaLb0;La0;MbLop0;McGcS44GbLop0;MdGdS2fS2eS0GaLa0;Lw;Lsgn;S2dS0S2cGaLk;Li;Ll;X0x8S15fG7Vrec;R1A1MeA2S7bS7bS7bS7bS7bG5R1S2cG6G0S63R2Z40MfA2S2cS2fG0L_;M10S5dS37S2cS2cR2A3M11S38S2cS2cR2A3M12A2S33S2cS2cS69G11R1A2S69G12R1A2A4S7bX2fx2Tk';Tp;Lk;G3S43S0S0S7bLb0;La0;M13Lop0;M14G14S44G13Lop0;M15G15S2fS2eS0S7bLa0;Lw;Lsgn;S2dS0S2cS7bLk;Li;Ll;M16X0x8S7bS7bX43xaLb;La;Lop;S43S0S0G4R3G5R1S2cSccG6S33S2cS2cS15bR1A1M17G17A4A2Lc;S2dSccG6G7A2Li;S43S0S0SccG8G9A2M18Lb0;La0;M19Lop0;M1aG1aS44G19Lop0;M1bG1bS2fS2eS0G18La0;Lw;Lsgn;S2dS0S2cG18Lk;Li;Ll;X0x8S15eG7GeA2S8aS8aS8aS8aS8aS8aS8aS8aX43xaLb;La;Lop;S44S0S0S7bLb;La;Lop;S44S0S0S8aLb;La;Lop;S2fS2eS0S2fG0Lsgn;R3S6dR2A1M1cS2cG10S34S60Z0M1dR1A2S5dR1GfA2A2S33S2cS2cS67S61Z2M1eS5fR1Z1M1fA2A2M20A1S5fG20G1fA2A4G0G6G0G10S34S34S5dS37S2cS2cR1A3M21S38S2cS2cR1A3M22A2S5dG11G21A2A2S5dG22G12A2A2R1R2X2fx2Tp;Tr;S7bX2fx2Twz;G1cS2cG10S34S5dG1dR1A2S60R1GfA2A2S33S2cS2cG1dS5fS61G1eR1A2G1fA2A4S7bX2fx2Twz;X2fx2La;Lw;Lsgn;G16X0x8G0Sb3Sb3Sb3R1S100S82Vdg;Ve;A2A1A2SceR2Ve;A2A2S15dR2Sa2Vdg;A1Ve;A3A2Tstructural;Tfacts;").

Fixpoint stv_t (dg : fdig) (e : sv) : Z * Z :=
  match tbl_find (dg_tbl dg) e with
  | Some v => snd v
  | None => stv_body (fun a => stv_t dg a) dg e
  end.

Definition stv_node (dg : fdig) (e : sv) : Z * Z := ltac2:(tb__ "0|0|
S163S0S90Vdg;R1A2La;Vdg;Ve;A3").

Definition is_lit (e : sv) : bool := match e with SLit _ => true | _ => false end.

Definition add_endpoint (e : sv) (l : list sv) : list sv := ltac2:(tb__ "0|1|
S2fS36S0A1L_;M0Sc2Ve;A1Vl;G0S1a6S0S4Ve;A1Vl;A3Vl;S41S0Vl;S3bS0Ve;S3eS0A1A3A3X2fx2X2fx2").

Fixpoint endpoints (rels : list (sv * Z * sv)) (acc : list sv) : list sv :=
  match rels with
  | [] => acc
  | (x, _, y) :: rest => endpoints rest (add_endpoint y (add_endpoint x acc))
  end.

Definition u_of_s (p : Z * Z) : Z * Z := ltac2:(tb__ "0|3|
S30S2cS2cA2M0G0Lp;Vp;S2cS2cS2fG0L_;M1S3dS5dR2R1A2A1S77G1S5dZ0M2R2A2S33S2cS2cR2R1A4G1S60R1G2A2S33S2cS2cS5eR2S78A2S5eR1S78A2A4S77X2fx2X2fx2X2fx2Lh;Ll;X30x1").

Fixpoint tbl_init (dg : fdig) (es : list sv) : fdig :=
  match es with
  | [] => dg
  | e :: rest =>
      let pu := itv_node dg e in
      let dg1 := dg_with_tbl dg ((e, (pu, stop_itv)) :: dg_tbl dg) in
      let ps := stv_node dg1 e in
      tbl_init (dg_with_tbl dg ((e, (itv_meet pu (u_of_s ps), smeet ps (sitv_of_itv pu))) :: dg_tbl dg)) rest
  end.

Fixpoint tbl_upd (tbl : list tbl_entry) (e : sv) (f : (Z * Z) * (Z * Z) -> (Z * Z) * (Z * Z)) : list tbl_entry :=
  match tbl with
  | [] => []
  | (x, v) :: rest => if sv_eqb x e then (x, f v) :: rest else (x, v) :: tbl_upd rest e f
  end.

Definition tbl_get (tbl : list tbl_entry) (e : sv) : (Z * Z) * (Z * Z) := ltac2:(tb__ "0|2|
S31S30S30S2cS2cA2M0G0A2M1A1G1Lx;S167Vtbl;Ve;A2G1R1Lv;S33G0G0S77S7bA4X31x2").

Definition entry_norm (v : (Z * Z) * (Z * Z)) : (Z * Z) * (Z * Z) := ltac2:(tb__ "0|2|
S9aS37S30S2cS2cA2M0G0Vv;A3S172S38G0G0Vv;A3M1A1A2G0S33G0G0R1Sb3G1S100R1A1A2A4Tpu;").

Definition tbl_prop_u (tbl : list tbl_entry) (r : sv * Z * sv) : list tbl_entry := ltac2:(tb__ "0|8|
S30S30S0S2cA2M0S0A2S36Sa5A1M1Lr;Vr;G0S0G0G1Lp;R2S0S2cS38S2cS2cS37S30S2cS2cA2M2G2Sb4Vtbl;R3A2A3A3S2cSb5Vtbl;R3S30G2G2A2M3SaaS33G2G2S33S2cS2cS37S2cS2cS37G2G2R1A3M4A3M5S64S38S2cS2cG4A3M6S5fR2R3A2A2A4S38G2G2R1A3M7A4A1Lv;A3G1S37S2cS2cS37G2G2Sb4R1R4A2A3A3S2cSb5R2R6G3SaaS33G2G2S33S2cS2cS65G5S5eR2R5A2A2G6A4G7A4A1Lv;A3Tlx;Ttbl1;Thy;Ld;Lx;X30x1Ly;Lp;X30x1").

Definition tbl_prop_s (tbl : list tbl_entry) (r : sv * Z * sv) : list tbl_entry := ltac2:(tb__ "0|8|
S30S30S0S2cA2M0S0A2S36Sa5A1M1Lr;Vr;G0S0G0G1Lp;R2S0S2cS38S2cS2cS38S30S2cS2cA2M2G2Sb4Vtbl;R3A2A3A3S2cSb5Vtbl;R3S30G2G2A2M3SaaS33G2G2S37G2G2R1A3M4S33S2cS2cS37S2cS2cS38G2G2R1A3M5A3M6S64S38S2cS2cG5A3M7S5fR2R3A2A2A4A4A1Lv;A3G1S37S2cS2cS38G2G2Sb4R1R4A2A3A3S2cSb5R2R6G3SaaS33G2G2G4S33S2cS2cS65G6S5eR2R5A2A2G7A4A4A1Lv;A3Tlx;Ttbl1;Thy;Ld;Lx;X30x1Ly;Lp;X30x1").

Definition tbl_round (urels srels : list (sv * Z * sv)) (tbl : list tbl_entry) : list tbl_entry := ltac2:(tb__ "0|2|
S1a8S36Sa5A1M0S30S30S0S2cA2S0A2M1S16aVsrels;S1a8G0G1S16bVurels;Vtbl;A5A5").

Fixpoint tbl_iter (n : nat) (urels srels : list (sv * Z * sv)) (tbl : list tbl_entry) : list tbl_entry :=
  match n with
  | O => tbl
  | S n' => tbl_iter n' urels srels (tbl_round urels srels tbl)
  end.

Definition tbl_rounds : nat := 3%nat.

Definition mk_ctx (facts : list sprop) : fdig := ltac2:(tb__ "0|2|
SfcVfacts;A1S36S30S30S0S2cA2S0A2A1M0S103Vfacts;A1G0Sb1Vfacts;Sf4Vfacts;A1Sf7Vfacts;A1Sf3Vfacts;A1R2R1S3eSa5A1S3eS79A1A8Sa3S36S0A1M1Sa3Lx;SddR2SddR3S3eS0A1A2A2R1S0G1S168R3S3bS0R2R1A3A2Sa3S119R1S169S16cR6R5Sc0R1A1A4A2Tdg1;Ll;Ls;X36x2Tdg0;Tsrels;Turels;").

Definition itv_ok (p : Z * Z) : bool := (fst p <=? snd p).

Inductive decision := DTrue | DFalse | DUnknown_.

Definition itv_decide_t (dg : fdig) (c : branch_cond) (a b : sv) : decision := ltac2:(tb__ "0|9|
S30S2cS2cA2S7aLx;M0S82Vdg;Va;A2S2cS2cG0S82Vdg;Vb;A2S2cS2cS2fS7aL_;M1S3dS34S5dR4R3A2S5dR2R1A2A2A1S85S45S7aLc;Vc;G1S3fS60R3R2A2M2S60R1R4A2A2M3S7eG1S34S34S62R4R3A2S62R2R1A2A2S62R4R2A2A2M4S7fS85X2fx2X2fx2G1G3S7fG1G4S7eS85X2fx2X2fx2G1S3dS34S60R3S88A2S60R1S88A2A2A1M5S85G1G2S7fG1S5dR1R4A2M6S7eS85X2fx2X2fx2M7X2fx2G1G5S85G1G2S7eG1G6S7fS85X2fx2X2fx2M8X2fx2G7G8X45x6X2fx2Lhb;Llb;X30x1Lha;Lla;X30x1").
Definition itv_decide (facts : list sprop) (c : branch_cond) (a b : sv) : decision := ltac2:(tb__ "0|0|
Sc3S89Vfacts;A1Vc;Va;Vb;A4").

Definition same_base_eq (a b : sv) : option bool := ltac2:(tb__ "0|2|
S30S0S2cA2S31S2fA1M0Lx;M1S102Va;A1S0S2cG1S102Vb;A1S0S2cS2fG0L_;S4R4R2A2S35S2fS62S63S5fR3R1A2S61Z2Z40A2A2Z0A2A2S3aS2fA1X2fx2Ly;Lbb;X30x1Lx;Lba;X30x1").

Definition small_u_t (dg : fdig) (e : sv) (w : Z) : bool := ltac2:(tb__ "0|0|
S30S2cS2cA2S2fLx;S82Vdg;Ve;A2S2cS2cS34S5dR2R1A2S60R1S61Z2Vw;A2A2A2Lh;Ll;X30x1").

Definition small_u (facts : list sprop) (e : sv) (w : Z) : bool := ltac2:(tb__ "0|0|
S2fS2fL_;Sa0S89Vfacts;A1Ve;Vw;A3S39Sa0Sb2Vfacts;A1Ve;Vw;A3X2fx2").

Definition mk_ext_f_t (dg : fdig) (sgn : bool) (w : N) (a : sv) : sv := ltac2:(tb__ "0|1|
S2fS0L_;S34S34S60Z0S6dVw;A1M0A2S5dG0Z40A2A2Sa0Vdg;Va;S2fS2cLsgn;Vsgn;S5fG0Z1A2G0X2fx2A3A2Va;S84Vsgn;Vw;Va;A3X2fx2").

Definition mk_ext_s (dg : fdig) (sgn : bool) (w : N) (a : sv) : sv := ltac2:(tb__ "0|2|
S2fS0L_;M0S34Vsgn;S1b6Vw;Q20A2A2S90Vdg;Va;A2S30S2cS2cA2G0S34S5dS37S2cS2cR1A3S38S2cS2cR1A3A2S93R1A1A2Va;S84Vsgn;Vw;Va;A3M1X2fx2Tp;G1X2fx2").
Definition mk_ext_f (facts : list sprop) (sgn : bool) (w : N) (a : sv) : sv := ltac2:(tb__ "0|9|
S0S0Lx;M0Sf5S89Vfacts;A1Vsgn;Vw;Va;A4S2cS2R1A1Lz;M1S2dS15R1A1Li;M2S43S0S0S9R3R2R1A3Lb;La0;Lop;M3S43S0S0S23R3R2R1A3Lb;La0;Lop;M4S44S0S0S1cR3R2R1A3Lb;La0;Lop;M5S44S0S0S22R3R2R1A3Lb;La0;Lop;M6S2fS2eS0G0Sf5Sb2Vfacts;A1M7Vsgn;Vw;Va;A4G1G2G3G4G5G6S2fS2eS0S135G7Vsgn;Vw;Va;A4La0;Lw0;Lsgn0;S2dS0S2cS21R3R2R1A3Lk;Li;Ll;M8X0x8La0;Lw0;Lsgn0;G8X0x8").

Definition lit_fold_t (dg : fdig) (e : sv) : sv := ltac2:(tb__ "0|4|
S0S0Le;Ve;S2cVe;Lz;S2dS30S2cS2cA2S0Lx;S82Vdg;Ve;A2S2cS2cS2fS0L_;S62R2R1A2S2R2A1Ve;X2fx2Lh;Ll;X30x1M0Li;S43S0S0G0Lb;La;M1Lop;M2G2S44G1Lop;M3G3S2fS2eS0G0La;Lw;Lsgn;S2dS0S2cG0Lk;Li;Ll;X0x8").

Definition mk_aluw_f_t (dg : fdig) (op : aluop) (a b : sv) : sv := ltac2:(tb__ "0|3|
Sc6Vdg;S43S0Lop;Vop;S2fS0L_;M0S43S2fLop;Vop;S32S4Va;Vb;A2S32S32S32S32S32S32S32S32X43xaS2Z0A1S8cVop;Va;Vb;A3S0G0Sa0Vdg;R1Z1fA3R1Sc7Vop;Va;Vb;A3M1X2fx2Tr;X2fx2M2G2G1G1G1G1G1G1G1G1X43xaA2").

Definition mk_aluw_s (dg : fdig) (op : aluop) (a b : sv) : sv := ltac2:(tb__ "0|2|
S43S0Lop;Vop;S8cVop;Va;Vb;A3S0S90Vdg;R1A2S30S2cS2cA2S2fS0L_;S34S5dS37S2cS2cR1A3S38S2cS2cR1A3A2S93R1A1A2R2Sc7Vop;Va;Vb;A3M0X2fx2Tp;Tr;M1G1G0G0G0G0G0G0G0G0X43xa").
Definition mk_aluw_f (facts : list sprop) (op : aluop) (a b : sv) : sv := ltac2:(tb__ "0|9|
S0S0Lx;M0Sf2S89Vfacts;A1Vop;Va;Vb;A4S2cS2R1A1Lz;M1S2dS15R1A1Li;M2S43S0S0S9R3R2R1A3Lb0;La0;Lop0;M3S43S0S0G0Sf2Sb2Vfacts;A1M4Vop;Va;Vb;A4G1G2G3S43S0S0S134G4Vop;Va;Vb;A4Lb0;La0;Lop0;S44S0S0S1cR3R2R1A3Lb0;La0;Lop0;M5S44S0S0S22R3R2R1A3Lb0;La0;Lop0;M6S2fS2eS0S24R3R2R1A3La0;Lw;Lsgn;M7S2dS0S2cS21R3R2R1A3Lk;Li;Ll;M8X0x8Lb0;La0;Lop0;G5G6G7G8X0x8").

Definition xor_same_base (e : sv) : option bool := ltac2:(tb__ "0|c|
S0S31S2fA1M0Le;Ve;S2cS3aS2fA1M1Lz;S2dG1Li;S43S0S0S43G0Lop;R3G1G1G1G1G1S31S30S0S2cA2M2A1G0Lx;M3S98R2A1G2G2G0Lp;M4R1S0S2cG3S98R4A1G2G2G0Lp0;R1S0S2cS2fG0L_;M5S4R5R2A2M6S35S2fS62S63S5fR4R1A2S61Z2Z40A2M7A2Z0M8A2A2G1X2fx2Lky;Lby_;X30x1Lp0;G5S4R2R4A2S35S2fS62S63R1G7A2G8A2A2M9G1X2fx2X31x2Lkx;Lbx;X30x1Lp;G3S98R1A1G2G4R1S0S2cG5G6G9G1X2fx2Lky;Lby_;X30x1Lp;G1X31x2X31x2G1G1G1G1X43xaLy;Lx;Lop;S43S0S0G1Lb;La;MaLop;S44GaLop;MbGbS2fS2eS0G1La;Lw;Lsgn;S2dS0S2cG1Lk;Li;Ll;X0x8").

Definition slt_xor_fold (a b : sv) : option sv := ltac2:(tb__ "0|10|
S0S31S0A1M0La;Va;S2cS2cG0Lz;M1R1S31S2fA1G0Lx;M2S107Vb;A1S2fS35S0S2S2fS2cLiszero;M3R1Z0M4Z1M5X2fx2A1A2Liszero;S3aS0A1M6X31x2S2dS0G0Lb;Vb;S2cG1R1G6S2dS2dG0Lp;R1S2dG6Lp0;M7G7G2S107Va;A1S2fS35S0S2G3R1G5G4X2fx2A1A2Liszero;G6X31x2X2dx3Lp;S2dG6Lp;X2cx3Lz;S2dG6Li;S43S0S0G6Lb0;La0;M8Lop;M9G9S44G8Lop;MaGaS2fS2eS0G6La0;Lw;Lsgn;S2dS0S2cG6Lk;Li;Ll;X0x8MbLp;McGcX2cx3Lz;S2dGbLi;S43S0S0GbLb0;La0;MdLop;MeGeS44GdLop;MfGfS2fS2eS0GbLa0;Lw;Lsgn;S2dS0S2cGbLk;Li;Ll;X0x8").

Fixpoint list_set {A} (l : list A) (n : nat) (x : A) : list A :=
  match l, n with
  | [], _ => []
  | _ :: t, O => x :: t
  | h :: t, S n' => h :: list_set t n' x
  end.

Definition regZ (r : reg) : Z := bv_unsigned r.

Definition get_reg (S : sstate) (r : reg) : sv := reg_sv S (regZ r).

Definition set_reg (S : sstate) (r : reg) (v : sv) : sstate := ltac2:(tb__ "0|1|
S2fS3L_;S62SfbVr;A1M0Z0A2VS;SfS8VS;A1SafS0S12VS;A1S6cG0A1Vv;A4S10VS;A1SaVS;A1S13VS;A1ScVS;A1S7VS;A1S11VS;A1SeVS;A1A9X2fx2").

Definition get_freg (S : sstate) (r : reg) : sv := freg_sv S (regZ r).

Definition set_freg (S : sstate) (r : reg) (v : sv) : sstate := ltac2:(tb__ "0|0|
SfS8VS;A1S12VS;A1SafS0S10VS;A1S6cSfbVr;A1A1Vv;A4SaVS;A1S13VS;A1ScVS;A1S7VS;A1S11VS;A1SeVS;A1A9").

Definition set_pc (S : sstate) (pc : Z) : sstate := ltac2:(tb__ "0|0|
SfVpc;S12VS;A1S10VS;A1SaVS;A1S13VS;A1ScVS;A1S7VS;A1S11VS;A1SeVS;A1A9").

Definition add_fact (S : sstate) (p : sprop) : sstate := ltac2:(tb__ "0|0|
SfS8VS;A1S12VS;A1S10VS;A1SaVS;A1S13VS;A1ScVS;A1S3bS1Vp;S7VS;A1A3S11VS;A1SeVS;A1A9").

Definition set_objs (S : sstate) (objs : list sobj) : sstate := ltac2:(tb__ "0|0|
SfS8VS;A1S12VS;A1S10VS;A1SaVS;A1S13VS;A1Vobjs;S7VS;A1S11VS;A1SeVS;A1A9").

Definition set_resv (S : sstate) (r : option sv) : sstate := ltac2:(tb__ "0|0|
SfS8VS;A1S12VS;A1S10VS;A1SaVS;A1Vr;ScVS;A1S7VS;A1S11VS;A1SeVS;A1A9").

Definition fresh (S : sstate) : sv * sstate := ltac2:(tb__ "0|1|
S33S0S3S15S11VS;A1M0A1SfS8VS;A1S12VS;A1S10VS;A1SaVS;A1S13VS;A1ScVS;A1S7VS;A1S1b9G0A1SeVS;A1A9A4").

Fixpoint remove_atoms (bs atoms : list sv) : option (list sv) :=
  match bs with
  | [] => Some atoms
  | b :: bs' => match remove_atom b atoms with
                | Some atoms' => remove_atoms bs' atoms'
                | None => None
                end
  end.

Definition same_atoms0 (a x : sv) : option Z := ltac2:(tb__ "0|6|
S30S36S0A1M0S2cA2S31S2cA1M1Lx;M2S97Va;S3eS0A1M3Z0M4A3G0S2cG2S97Vx;G3G4A3G0S2cS31G0A1G1Lx;ScbR2R4A2G0G0G1Ll;R1S35S2cS5fR4R2A2A2S0G0S3aS2cA1M5Ll0;Ls;X36x2Ll;G5X31x2Lcx;Lxa;X30x1Lca;Laa;X30x1").

Definition rel_offset0 (base ae : sv) : option sv := ltac2:(tb__ "0|5|
S30S36S0A1M0S2cA2S31S0A1M1Lx;M2S97Vae;S3eS0A1M3Z0M4A3G0S2cG2S97Vbase;G3G4A3G0S2cS31G0A1G1Lx;ScbR2R4A2G0G0G1Lrest;R1S35S0S2S86S5fR4R2A2A1A1A2S0G0S35S0S166R3S5fR6R4A2A2A2Ll;Ls;X36x2Lrest;S3aS0A1X31x2Lcb;Lba;X30x1Lca;Laa;X30x1").

Fixpoint lin_of (e : sv) (k : Z) (acc : lin) (c : Z) : lin * Z :=
  match e with
  | SLit z => (acc, c + k * z)
  | SAlu ALU_ADD a b => let '(acc1, c1) := lin_of a k acc c in lin_of b k acc1 c1
  | SAlu ALU_SUB a b => let '(acc1, c1) := lin_of a k acc c in lin_of b (- k) acc1 c1
  | SAlu ALU_SLL a (SLit s) => lin_of a (k * 2 ^ (s mod 64)) acc c
  | SMd M_MUL a (SLit m) => lin_of a (k * snorm m) acc c
  | SMd M_MUL (SLit m) b => lin_of b (k * snorm m) acc c
  | _ => ((k, e) :: acc, c)
  end.

Fixpoint lin_add1 (k : Z) (a : sv) (l : lin) : lin :=
  match l with
  | [] => [(k, a)]
  | (k', a') :: rest => if sv_eqb a' a then (k' + k, a') :: rest else (k', a') :: lin_add1 k a rest
  end.

Fixpoint lin_merge (l acc : lin) : lin :=
  match l with
  | [] => acc
  | (k, a) :: rest => lin_merge rest (lin_add1 k a acc)
  end.

Definition lin_norm (l : lin) : lin := ltac2:(tb__ "0|1|
S1aaS30S2cS0A2M0G0S3dS62S37S2cS0R1A3Z0A2A1Lka;S129Vl;S3eG0A1A2A3").

Definition lin_neg (l : lin) : lin := ltac2:(tb__ "0|1|
S1a3S30S2cS0A2M0G0G0S33S2cS0S67S37S2cS0R1A3A1S38S2cS0R1A3A4Lka;Vl;A4").
Definition lin_scale (m : Z) (l : lin) : lin := ltac2:(tb__ "0|1|
S1a3S30S2cS0A2M0G0G0S33S2cS0S66Vm;S37S2cS0R1A3A2S38S2cS0R1A3A4Lka;Vl;A4").
Definition lin_add (l1 l2 : lin) : lin := lin_norm (l1 ++ l2).
Definition lin_sub (l1 l2 : lin) : lin := ltac2:(tb__ "0|0|
SeeS41S30S2cS0A2Vl1;SedVl2;A1A3A1").
Definition lin_nil (l : lin) : bool := match l with [] => true | _ => false end.

Fixpoint lin_coef (l : lin) (a : sv) : Z :=
  match l with
  | [] => 0
  | (k, a') :: rest => if sv_eqb a' a then k + lin_coef rest a else lin_coef rest a
  end.

Definition lin_term (k : Z) (a : sv) : sv := ltac2:(tb__ "0|2|
S6fVk;A1S2cS2fS0L_;M0S62R1Z1A2Va;G0S2fS2fL_;S62R1S61Z2S6aR1A1M1A2A2S60G1Z40A2S32X2fx2S9S4fVa;S2G1A1A3S1cS52Va;S2R1A1A3X2fx2X2fx2Tm;").

Fixpoint lin_pos_sum (l : lin) : option sv :=
  match l with
  | [] => None
  | (k, a) :: rest =>
      if 0 <? k then match lin_pos_sum rest with
                     | Some s => Some (SAlu ALU_ADD (lin_term k a) s)
                     | None => Some (lin_term k a)
                     end
      else lin_pos_sum rest
  end.

Fixpoint lin_sub_negs (acc : sv) (l : lin) : sv :=
  match l with
  | [] => acc
  | (k, a) :: rest => lin_sub_negs (if k <? 0 then SAlu ALU_SUB acc (lin_term k a) else acc) rest
  end.

Definition sv_of_lin (l : lin) (c : Z) : sv := ltac2:(tb__ "0|0|
S31S0A1S0Lx;S12bVl;A1S0S8bSf0R1Vl;A2Vc;A2Ls;Sf0S2S80Vc;A1A1Vl;A2X31x2").

Definition lin_of0 (e : sv) : lin * Z := ltac2:(tb__ "0|1|
S30S76S2cA2M0G0Lx;S12aVe;Z1S3eS30S2cS0A2A1Z0A4S76S2cS33S76S2cSeeR2A1R1A4Lc;Ll;X30x1").

Definition same_atoms (a x : sv) : option Z := ltac2:(tb__ "0|2|
S31S2cA1M0G0Lx;S14eVa;Vx;A2S2cS35S2cR1A2Ld;S30S76S2cA2G0Lx;M1S94Va;A1S76S2cG1S94Vx;A1S76S2cS2fG0L_;Sc5S9cR4R2A2A1S35S2cS5fR3R1A2A2S3aS2cA1X2fx2Lcx;Llx;X30x1Lca;Lla;X30x1X31x2").

Definition rel_offset (base ae : sv) : option sv := ltac2:(tb__ "0|3|
S31S0A1M0G0Lx;S14bVbase;Vae;A2S0S35S0R1A2Loff;S30S76S2cA2G0Lx;M1S94Vae;A1S76S2cG1S94Vbase;A1S76S2cS9cR4R2A2S76S2fG0L_;S34S3dSc5R3A1A1S1a7S30S2cS0A2M2G2S62SeaR2S38S2cS0R1A3A2Z0A2Lka;R3A3A2S35S0S105R1S5fR4R2A2A2A2S3aS0A1X2fx2Td;Lcb;Llb;X30x1Lca;Lla;X30x1X31x2").

Definition sv_equiv (a b : sv) : bool := ltac2:(tb__ "0|0|
S3fS4Va;Vb;A2S31S2cA1S2fLx;S8dVa;Vb;A2S2cS62S63R1S61Z2Z40A2A2Z0A2Ld;S32X31x2A2").

Fixpoint wnorm_t (dg : fdig) (e : sv) : sv :=
  match e with
  | SAluW ALU_ADD a (SLit c) =>
      let a' := wnorm_t dg a in
      let p := stv_t dg a' in let c' := snorm32 c in
      if (fst p <=? snd p) && in_i32 p && in_i32 (fst p + c', snd p + c')
      then SAlu ALU_ADD a' (SLit c') else e
  | SAluW ALU_ADD a b =>
      let a' := wnorm_t dg a in let b' := wnorm_t dg b in
      let p := stv_t dg a' in let q := stv_t dg b' in
      if (fst p <=? snd p) && (fst q <=? snd q) && in_i32 p && in_i32 q && in_i32 (fst p + fst q, snd p + snd q)
      then SAlu ALU_ADD a' b' else e
  | SAluW ALU_SUB a b =>
      let a' := wnorm_t dg a in let b' := wnorm_t dg b in
      let p := stv_t dg a' in let q := stv_t dg b' in
      if (fst p <=? snd p) && (fst q <=? snd q) && in_i32 p && in_i32 q && in_i32 (fst p - snd q, snd p - fst q)
      then SAlu ALU_SUB a' b' else e
  | SExt true 32%N a =>
      let a' := wnorm_t dg a in
      let p := stv_t dg a' in
      if (fst p <=? snd p) && in_i32 p then a' else e

  | SExt false w a =>
      let a' := wnorm_t dg a in
      if (0 <? Z.of_N w) &&& ((Z.of_N w <=? 64) &&& small_u_t dg a' (Z.of_N w)) then a' else e

  | SAlu ALU_SRL a (SLit sh) =>
      match wnorm_t dg a with
      | SAlu ALU_SLL x (SLit k) =>
          if (0 <=? sh) &&& ((sh <=? k) &&& ((k <? 64) &&& small_u_t dg x (64 - k))) then mk_alu ALU_SLL x (SLit (k - sh)) else e
      | _ => e
      end

  | SAlu ALU_ADD a b => SAlu ALU_ADD (wnorm_t dg a) (wnorm_t dg b)
  | SAlu ALU_SUB a b => SAlu ALU_SUB (wnorm_t dg a) (wnorm_t dg b)
  | SAlu ALU_SLL a (SLit k) => SAlu ALU_SLL (wnorm_t dg a) (SLit k)
  | SMd M_MUL a (SLit k) => SMd M_MUL (wnorm_t dg a) (SLit k)
  | _ => e
  end.

Fixpoint lin_itv (dg : fdig) (l : lin) : Z * Z :=
  match l with
  | [] => (0, 0)
  | (k, a) :: rest =>
      let '(lo, hi) := itv_t dg a in
      let '(l2, h2) := lin_itv dg rest in
      if 0 <=? k then (k * lo + l2, k * hi + h2) else (k * hi + l2, k * lo + h2)
  end.

Definition lin_div (d : lin) (g : ineq) : option Z := ltac2:(tb__ "0|5|
S36S30S2cS0A2M0A1M1S31S2cA1M2Lx;S37S76S2cVg;A3S3aS2cA1M3G0G1G0G2Lp;R2S2cS0SeaVd;R1A2S2cS2fG2L_;S34S60Z0M4S66R1R3A2A2S62S63R1R3A2G4A2A2S35S2cS68R1R3A2A2G3X2fx2Tkd;La;Lkg;X30x1Ll;Lp;X36x2").

Fixpoint lin_lo_pool (dg : fdig) (d : lin) (pool : list ineq) (acc : Z) : Z :=
  match pool with
  | [] => acc
  | g :: rest =>
      let acc1 := match lin_div d g with
                  | Some m => Z.max acc (fst (lin_itv dg (lin_sub d (lin_scale m (fst g)))) - m * snd g)
                  | None => acc
                  end in
      lin_lo_pool dg d rest acc1
  end.

Definition lin_lo (dg : fdig) (d : lin) : Z := ltac2:(tb__ "0|0|
S128Vdg;Vd;SdbVdg;A1S37S2cS2cSc4Vdg;Vd;A2A3A4").
Definition lin_hi (dg : fdig) (d : lin) : Z := ltac2:(tb__ "0|0|
S67S9bVdg;SedVd;A1A2A1").

Definition lin_geq (dg : fdig) (d : lin) (c : Z) : bool := ltac2:(tb__ "0|0|
S5dZ0S5eS9bVdg;Vd;A2Vc;A2A2").

Definition lin_exact_u (dg : fdig) (l : lin) (c : Z) : bool := ltac2:(tb__ "0|1|
S30S2cS2cA2S2fLx;Sc4Vdg;Vl;A2S2cS2cS2fS2fL_;M0G0S5dZ0S5eR2Vc;A2A2S39SadVdg;Vl;Vc;A3X2fx2S60S5eR1Vc;A2S78A2S32X2fx2Lhi;Llo;X30x1").
Definition lin_exact_s (dg : fdig) (l : lin) (c : Z) : bool := ltac2:(tb__ "0|1|
S30S2cS2cA2S2fLx;Sc4Vdg;Vl;A2S2cS2cS2fS2fL_;M0G0S5dS81S5eR2Vc;A2A2S39SadVdg;Vl;S5fVc;S81A2A3X2fx2S5dS5eR1Vc;A2S83A2S32X2fx2Lhi;Llo;X30x1").

Fixpoint lin_constfold (dg : fdig) (l : lin) : lin * Z :=
  match l with
  | [] => ([], 0)
  | (k, a) :: rest =>
      let '(l', c') := lin_constfold dg rest in
      let '(lo, hi) := itv_t dg a in
      if lo =? hi then (l', c' + k * lo) else ((k, a) :: l', c')
  end.

Definition linz (dg : fdig) (e : sv) : lin * Z := ltac2:(tb__ "0|2|
S30S76S2cA2M0G0Lx;M1S94Sa7Vdg;Ve;A2A1S76S2cG1S124Vdg;R2A2S76S2cS33S76S2cR2S5eR3R1A2A4Lc';Ll';X30x1Lc;Ll;X30x1").

Definition lit_rel_skip (dg : fdig) (x y : sv) : bool := ltac2:(tb__ "0|2|
S3fS34Sc2Vx;A1S1b4S40S30S2cS0A2M0S37S76S2cS8fVdg;Vy;A2A3A2U2M1A2A2S34Sc2Vy;A1S1b4S40G0S37S76S2cS8fVdg;Vx;A2A3A2G1A2A2A2").
Definition ineq_of_rel (dg : fdig) (sgn : bool) (r : sv * Z * sv) : option ineq := ltac2:(tb__ "0|5|
S30S30S0S2cA2M0S0A2S31S79A1M1Lr;Vr;G0S0G0G1Lp;R2S0S2cS2fG1L_;S130Vdg;R2R3A3S3aS79A1M2S30S76S2cA2M3G1Lx;M4S8fVdg;R2A2S76S2cG4S8fVdg;R5A2S76S2cS2fS2fLsgn;Vsgn;S34SabVdg;R4R3A3SabVdg;R2R1A3A2S34SacVdg;R4R3A3SacVdg;R2R1A3A2X2fx2S2fS2fG1Lok;R1S35G3S33S76S2cS9cR3R5A2S5fS5fR2R4A2R6A2A4A2G2X2fx2Tok;Lcy;Lly;X30x1Lcx;Llx;X30x1X2fx2Ld;Lx;X30x1Ly;Lp;X30x1").

Fixpoint ineqs_of_rels (dg : fdig) (sgn : bool) (rels : list (sv * Z * sv)) : list ineq :=
  match rels with
  | [] => []
  | r :: rest => match ineq_of_rel dg sgn r with
                 | Some g => g :: ineqs_of_rels dg sgn rest
                 | None => ineqs_of_rels dg sgn rest
                 end
  end.

Definition neq_of_fact (f : sprop) : option (sv * sv) := ltac2:(tb__ "0|7|
S1S31S30S0S0A2M0A1M1Lf;Vf;S45S0S0S45G1Lc;M2R3S3aG0A1M3S35G0S33S0S0R2R1A4A2M4G3G3G3G3X45x6Ly;Lx;Lc;S1S1G1Lp;R1S45S0S0G2R3G4G3G3G3G3G3X45x6Ly;Lx;Lc;S1G3Lp0;S0S0G3Lb;La;M5G5S0S0G4Ly;Lx;G3S2dS2cG3La;Li;M6X1x7Lp;G5G5G5G3G6X1x7").

Fixpoint neqs_of (dg : fdig) (all : list sprop) : list ineq :=
  match all with
  | [] => []
  | f :: rest =>
      let tl := neqs_of dg rest in
      match neq_of_fact f with
      | Some (x, y) =>
          let '(lx, cx) := linz dg x in
          let '(ly, cy) := linz dg y in
          if (lin_exact_u dg lx cx && lin_exact_u dg ly cy)
             || (lin_exact_s dg lx cx && lin_exact_s dg ly cy)
          then (lin_sub ly lx, cy - cx) :: tl else tl
      | None => tl
      end
  end.

Definition lin_eqb (l1 l2 : lin) : bool := lin_nil (lin_sub l1 l2).

Definition ne_tighten1 (neqs : list ineq) (g : ineq) : ineq := ltac2:(tb__ "0|3|
S30S76S2cA2M0S79Lg;Vg;S76S2cS2fS79L_;S1a6G0G0S3fS34SecR3S37S76S2cR1A3M1A2S62R2S38S76S2cR1A3M2A2A2S34Sc5Se9R3G1A2A1S62R2S67G2A1A2A2A2Lh;Vneqs;A3S33S76S2cR2S5fR1Z1A2A4Vg;X2fx2Lc;Ll;X30x1").

Fixpoint ne_tighten (n : nat) (neqs : list ineq) (g : ineq) : ineq :=
  match n with
  | O => g
  | S n' => let g' := ne_tighten1 neqs g in
            if snd g' =? snd g then g else ne_tighten n' neqs g'
  end.

Fixpoint opp_atom (l1 l2 : lin) : option (Z * Z) :=
  match l1 with
  | [] => None
  | (k1, a) :: rest =>
      let k2 := lin_coef l2 a in
      if k1 * k2 <? 0 then Some (Z.abs k1, Z.abs k2) else opp_atom rest l2
  end.

Definition ineq_combine (g1 g2 : ineq) : option ineq := ltac2:(tb__ "0|4|
S31S30S2cS2cA2M0A1S31S79A1M1Lx;S147S37S76S2cVg1;A3M2S37S76S2cVg2;A3M3A2G0G0G1Lp;R1S2cS2cS71R2R1A2S2cS68R2R1A2S2cS68R4R2A2S2cS35S30S76S2cA2S33S76S2cSe9SefR2G2A2SefR1G3A2A2S5eS66R2S38S76S2cVg1;A3A2S66R1S38S76S2cVg2;A3A2A2A4A2Tn2;Tn1;Tg;Lm2;Lm1;X30x1Lp;S3aS79A1X31x2").

Fixpoint combine_all (news base : list ineq) : list ineq :=
  match news with
  | [] => []
  | g1 :: rest =>
      fold_right (fun g2 acc => match ineq_combine g1 g2 with
                                | Some g => if lin_nil (fst g) then acc else g :: acc
                                | None => acc
                                end) (combine_all rest base) base
  end.

Definition ineq_subsumed (pool : list ineq) (g : ineq) : bool := ltac2:(tb__ "0|1|
S1a6S30S76S2cA2M0G0S34SecS37S76S2cVg;A3S37S76S2cR1A3A2S5dS38S76S2cR1A3S38S76S2cVg;A3A2A2Lh;Vpool;A3").

Fixpoint add_new (pool fresh : list ineq) : list ineq :=
  match fresh with
  | [] => []
  | g :: rest => if ineq_subsumed pool g then add_new pool rest
                 else g :: add_new (g :: pool) rest
  end.

Definition pool_cap : nat := 48%nat.

Fixpoint saturate (n : nat) (neqs : list ineq) (news pool : list ineq) (base : list ineq) : list ineq :=
  match n with
  | O => pool
  | S n' => let fresh := firstn pool_cap (add_new pool (map (ne_tighten (length neqs) neqs) (combine_all news base))) in
            saturate n' neqs fresh (pool ++ fresh) base
  end.

Definition sat_depth : nat := 2%nat.

Definition dg_with_pool (dg : fdig) (pool : list ineq) : fdig := ltac2:(tb__ "0|0|
Sb1S92Vdg;A1SbeVdg;A1SbfVdg;A1SbdVdg;A1Sa9Vdg;A1Sa2Vdg;A1Sc0Vdg;A1Vpool;A8").

Fixpoint lin_align (facts : list sprop) (l : lin) : Z :=
  match l with
  | [] => 64
  | (k, a) :: rest => Z.min (lin_align facts rest) (Z.min 64 (align_sum facts a + lit_align k))
  end.
Definition roundup (x m : Z) : Z := ltac2:(tb__ "0|0|
S66S68S5fS5eVx;Vm;A2Z1A2Vm;A2Vm;A2").
Definition lin_round (facts : list sprop) (g : ineq) : ineq := ltac2:(tb__ "0|0|
S30S76S2cA2S79Lg;Vg;S76S2cS123Vfacts;R2A2S2cS2fS79L_;S2fS2fL_;S5dZ1R1A2S5dR1Z40A2S32X2fx2S33S76S2cR3S67S14dS67R2A1S61Z2R1A2A2A1A4Vg;X2fx2Tj;Lc;Ll;X30x1").

Fixpoint lin_gcd (l : lin) (acc : Z) : Z :=
  match l with [] => acc | (k, _) :: rest => lin_gcd rest (Z.gcd k acc) end.
Definition neq_prim (h : ineq) : ineq := ltac2:(tb__ "0|1|
S30S76S2cA2S79Lh;Vh;S76S2cS127R2S6fR1A1A2S2cS2fS79L_;S60Z1R1A2S33S36S30S2cS0A2M0A1S2cS1a3G0G0G0S33S2cS0S68S37S2cS0R1A3R2A2S38S2cS0R1A3A4Lka;R3A4S68R2R1A2A4Vh;X2fx2Tg;Lc;Ll;X30x1").

Definition pool_round (dg : fdig) : list ineq := ltac2:(tb__ "0|3|
S1a3S79S79S141S142Vdg;S92Vdg;A1M0A2A4S36S79A1M1S10bS3eS79A1S1a3S79S79S12cG0A1M2S1a3S79S79S140S40S79R1A2R1A2S1a3S79S79G2S41S79Se6Vdg;S32Sa9Vdg;A1A3Se6Vdg;S39Sa2Vdg;A1A3A3A4A4A4A2G1S1a3S79S79G2S151S150R2R1R1R1A5A4Tbase;Tneqs;").

Definition mk_pool (dg : fdig) : list ineq := ltac2:(tb__ "0|0|
Sf9Vdg;A1S36S79A1Sf9SdcVdg;R1A2A1Tp1;").

Definition mk_dig (facts : list sprop) : fdig := ltac2:(tb__ "0|0|
Sb2Vfacts;A1Sa3SdcR1S13dR1A1A2Tdg;").

Definition itv_lin (dg : fdig) (e : sv) : Z * Z := ltac2:(tb__ "0|7|
S82Vdg;Ve;A2S30S2cS2cA2M0S30S76S2cA2G0Lx;S8fVdg;Ve;A2S76S2cS36S30S2cS0A2M1A1M2G0Ll;R2R3G1G2G1G0Lp0;R2S2cS0S2cG0Lz;R2S5eS9bVdg;R6A2R5A2S2cS5eSaeVdg;R7A2R6A2S2cS2fG0L_;M3S2fS2fL_;S5dZ0R2A2S60R1S78A2S32X2fx2M4S9aR9S33S2cS2cR2R1A4M5A2R9X2fx2Thi;Tlo;S2dS2dG0Lp1;R1S2dS5eS9bVdg;R8A2R7A2S2cS5eSaeVdg;R9A2R8A2S2cG3G4S9aRbG5A2RbX2fx2Thi;Tlo;Lp2;M6G6G2G0Ll0;R4R8G1G2S5eS9bVdg;R9A2R8A2S2cS5eSaeVdg;RaA2R9A2S2cG3G4S9aRcG5A2RcX2fx2Thi;Tlo;Ll1;Lp2;X36x2X2dx3Lp1;S2dS5eS9bVdg;R7A2R6A2S2cS5eSaeVdg;R8A2R7A2S2cG3G4S9aRaG5A2RaX2fx2Thi;Tlo;Lp1;X2cx3Ls;Lz;X30x1Ll0;Lp0;X36x2Lc;Ll;X30x1Tp;").

Definition itv (facts : list sprop) (e : sv) : Z * Z := itv_lin (mk_dig facts) e.
Definition stv (facts : list sprop) (e : sv) : Z * Z := stv_t (mk_ctx facts) e.

Definition itv0 (facts : list sprop) (e : sv) : Z * Z := itv_t (ctx0 facts) e.

Definition uleq_lin (dg : fdig) (a : sv) (k : Z) (b : sv) : bool := ltac2:(tb__ "0|2|
S30S76S2cA2S2fLx;M0S8fVdg;Va;A2S76S2cG0S8fVdg;Vb;A2S76S2cS2fS2fL_;M1SacVdg;R4R3A3G1SacVdg;R2R1A3SadVdg;S9cR2R4A2S5fS5fR1R3A2Vk;A2A3S32X2fx2S32X2fx2Lcb;Llb;X30x1Lca;Lla;X30x1").

Definition sleq_lin (dg : fdig) (a : sv) (k : Z) (b : sv) : bool := ltac2:(tb__ "0|2|
S30S76S2cA2S2fLx;M0S8fVdg;Va;A2S76S2cG0S8fVdg;Vb;A2S76S2cS2fS2fL_;M1SabVdg;R4R3A3G1SabVdg;R2R1A3SadVdg;S9cR2R4A2S5fS5fR1R3A2Vk;A2A3S32X2fx2S32X2fx2Lcb;Llb;X30x1Lca;Lla;X30x1").

Definition uleq_by_rel (dg : fdig) (a : sv) (k : Z) (b : sv) (r : sv * Z * sv) : bool := ltac2:(tb__ "0|4|
S30S30S0S2cA2M0S0A2S2fLr;Vr;G0S0G0S2fLp;R2S0S2cS31S2cA1S2fLx;M1S8dVa;R2A2S2cG1S8dVb;R4A2S2cS30S2cS2cA2S2fLx;M2S82Vdg;R4A2S2cS2cG2S82Vdg;R7A2S2cS2cS34S34S34S34S34S34S5dR4R3A2S5dR2R1A2A2S5dZ0M3S5eR4R6A2A2A2S60S5eR3R6A2S78A2A2S5dG3S5eR2R5A2A2A2S60S5eR1R5A2S78A2A2S5dS5eR6Vk;A2S5eR5R7A2A2A2Lhy;Lly;X30x1Lhx;Llx;X30x1Ldb;S32X31x2Lda;S32X31x2Ld;Lx;X30x1Ly;Lp;X30x1").

Definition uleq_same (dg : fdig) (a : sv) (k : Z) (b : sv) : bool := ltac2:(tb__ "0|1|
S31S2cA1S2fLx;S8dVa;Vb;A2S2cS86R1A1S2cS30S2cS2cA2S2fLx;S82Vdg;Vb;A2S2cS2cS34S34S34S5dR2R1A2S5dZ0M0S5eR2R3A2A2A2S60S5eR1R3A2S78A2A2S5dS5eR3Vk;A2G0A2A2Lhb;Llb;X30x1Td;Ld0;S32X31x2").

Definition sub_atoms (a x : sv) : option (Z * list sv) := ltac2:(tb__ "0|6|
S30S36S0A1M0S2cA2S31S30S2cG0A2M1A1M2Lx;M3S97Va;S3eS0A1M4Z0M5A3G0S2cG3S97Vx;G4G5A3G0S2cS31G0A1G2Lx;ScbR4R2A2G0S35G1S33S2cG0S5fR4R2A2R1A4A2Lextra;S3aG1A1X31x2Lcx;Lxa;X30x1Lca;Laa;X30x1").

Fixpoint itv_sum (dg : fdig) (l : list sv) : Z * Z :=
  match l with
  | [] => (0, 0)
  | e :: rest => let '(l1, h1) := itv_t dg e in
                 let '(l2, h2) := itv_sum dg rest in (l1 + l2, h1 + h2)
  end.

Definition uleq_by_rel2 (dg : fdig) (a : sv) (k : Z) (b : sv) (r : sv * Z * sv) : bool := ltac2:(tb__ "0|6|
S30S30S0S2cA2M0S0A2S2fLr;Vr;G0S0G0S2fLp;R2S0S2cS31S30S2cS36S0A1M1A2M2A1S2fLx;S164Va;R2A2G2G2S2fLp;R1S2cG1S30S2cS2cA2S2fLx;M3S82Vdg;Va;A2S2cS2cG3S122Vdg;R3A2S2cS2cG3S82Vdg;RaA2S2cS2cS34S34S34S34S34S5dR6R5A2S5dR4R3A2A2S5dZ0M4S5fS5eR6R4A2R8A2A2A2S60S5fS5eR5R3A2R8A2S78A2A2S5dR2R1A2M5A2S31S2cA1S2fLx;S8dVb;RcA2S2cS34S34S5dG4S5eR3R1A2A2S60S5eR2R1A2S78A2A2S5dS5eS5fR9R5A2Vk;A2S5eR1RbA2A2A2Ldb;G3S82Vdg;Vb;A2S2cS2cS34G5S5dS5eS5fS5eS5fR3RcA2RaA2R6A2Vk;A2R2A2A2Lhb;Llb;X30x1X31x2A2Lhy;Lly;X30x1Leh;Lel;X30x1Lha;Lla;X30x1Lextra;Lda;X30x1Lp;S32X31x2Ld;Lx;X30x1Ly;Lp;X30x1").

Fixpoint strip_zext (dg : fdig) (e : sv) : sv :=
  match e with
  | SExt false w e' => if (Z.of_N w <=? 64) &&& small_u_t dg e' (Z.of_N w) then strip_zext dg e' else e
  | _ => e
  end.

Definition remu_lt (dg : fdig) (e b : sv) : bool := ltac2:(tb__ "0|6|
S0S2fLe;Ve;S2cS32Lz;S2dS32Li;S43S0S0S32Lb0;La;Lop;M0G0S44S0S0S44S2fLop;M1R3S32S32S32S32S32S32S32S2fS2fL_;M2S4R1Vb;A2M3S60Z0S37S2cS2cS82Vdg;Vb;A2M4A3A2M5S32X2fx2X44x8Lb';La;Lop;S44S0S0G1R3S32S32S32S32S32S32S32G2G3G2G5S60S38S2cS2cG4A3S61Z2Z1fA2A2S32X2fx2S32X2fx2X44x8Lb';La;Lop;S2fS2eS0S32La;Lw;Lsgn;S2dS0S2cS32Lk;Li;Ll;X0x8").

Definition uleq_core (dg : fdig) (a : sv) (k : Z) (b : sv) : bool := ltac2:(tb__ "0|4|
S30S2cS2cA2S2fLx;M0S82Vdg;Va;A2S2cS2cG0S82Vdg;Vb;A2S2cS2cS2fS2fL_;M1S34S34S5dR4R3A2S5dR2R1A2A2S5dS5eR3Vk;A2R2A2A2S39G1S176Vdg;Va;Vk;Vb;A4S39G1S175Vdg;Va;Vk;Vb;A4S39G1S1a6S30S30S0S2cA2S0A2M2S173Vdg;Va;Vk;Vb;A4Sa9Vdg;A1M3A3S39G1S1a6G2S174Vdg;Va;Vk;Vb;A4G3A3S39G1S5dVk;Z1A2S14cVdg;Sd0Vdg;Va;A2Vb;A3S32X2fx2X2fx2X2fx2X2fx2X2fx2X2fx2Lhb;Llb;X30x1Lha;Lla;X30x1").

Definition shr_arg (dg : fdig) (e : sv) : option (sv * Z) := ltac2:(tb__ "0|10|
S0S31S30S0S2cA2M0A1M1Le;Ve;S2cS3aG0A1M2Lz;S2dG2Li;M3S43S0S0S43G1Lop;M4R3G2G2G2G2G2G2S0G1Lb;M5R1S2cS2fG1L_;M6S2fS2fL_;M7S5dZ0R1A2S60R1Z40A2S32X2fx2S35G0S33S0S2cR3R1A4A2M8G2X2fx2Ls;G3S43S0S0G2Lb0;La;M9Lop0;MaGaS44G9Lop0;MbGbS2fS2eS0G2La;Lw;Lsgn;McS2dS0S2cG2Lk;Li;Ll;MdX0x8G2G2G2X43xaLb;Lx;Lop;S43S0S0G4R3G2G2G2G2G2G2G5R1S2cG6G7S5dZ1R1A2G7S60R1Z20MeA2Sa0Vdg;R3GeA3S32X2fx2S32X2fx2G8G2X2fx2Ls;G3GaGaGbGbGcGdX0x8G2G2G2X43xaLb;Lx;Lop;S44S0S0G2Lb;La;Lop;MfGfGcGdX0x8").
Definition shr_mono (dg : fdig) (a : sv) (k : Z) (b : sv) : bool := ltac2:(tb__ "0|3|
S31S30S0S2cA2M0A1S2fLx;M1SffVdg;Va;A2G0G0S2fLp;R1S0S2cG1SffVdg;Vb;A2G0G0S2fLp0;R1S0S2cS2fS2fL_;M2S62R4R1A2G2S5dZ0Vk;A2Sa6Vdg;Sd0Vdg;R5A2S66Vk;S61Z2R4A2A2R2A4S32X2fx2S32X2fx2Ls';Ly;X30x1Lp0;S32X31x2Ls;Lx;X30x1Lp;S32X31x2").

Fixpoint sv_replace (t u : sv) (e : sv) : sv :=
  if sv_eqb e t then u else
  match e with
  | SAlu op a b => SAlu op (sv_replace t u a) (sv_replace t u b)
  | SAluW op a b => SAluW op (sv_replace t u a) (sv_replace t u b)
  | SMd op a b => SMd op (sv_replace t u a) (sv_replace t u b)
  | SMdW op a b => SMdW op (sv_replace t u a) (sv_replace t u b)
  | SExt sg w a => SExt sg w (sv_replace t u a)
  | _ => e
  end.

Definition is_selmask (e : sv) : option sv := ltac2:(tb__ "0|d|
S0S31S0A1M0Le;Ve;S2cS3aS0A1M1Lz;M2S2dG1Li;M3S43S0S0S43G0Lop;R3S0G0La;R2G2G3S43S0S0S43G0Lop0;R3G1G1G1G1S0G0Lb0;R1S2cS0G0Lb;R5S2cS2fG0L_;S2fS2fL_;S62S80R2A1Z1A2S62S80R1A1S91A2S32X2fx2S35S0R4A2G1X2fx2Lm;G3S43S0S0G1Lb1;La0;M4Lop1;M5G5S44G4Lop1;M6G6S2fS2eS0G1La0;Lw;Lsgn;M7S2dS0S2cG1Lk;Li;Ll;M8X0x8Lc1;G3G5G5G6G6G7G8X0x8G1G1G1G1G1X43xaLb0;Lz;Lop0;S43S0S0G1Lb0;La0;M9Lop0;S44G9Lop0;MaGaG7G8X0x8G1G1G1G1G1G1G1G1G1X43xaLb;La;Lop;S43S0S0G1Lb;La;MbLop;S44GbLop;McGcS2fS2eS0G1La;Lw;Lsgn;G8X0x8").
Definition sel_here (e : sv) : option (sv * sv * sv) := ltac2:(tb__ "0|8|
S0S31S30S30S0S0A2M0S0A2M1A1M2Le;Ve;S2cS3aG1A1M3Lz;S2dG3Li;S43S0S0S43G2Lop;R3G3G3G3G3G3G3G3G3G3S31S0A1G2Lx;M4Se7R2A1S0S35G1S33G0S0S33S0S0Ve;R1A4M5R2A4A2Lz;G4Se7R1A1S0S35G1S33G0S0G5R3A4A2Lz;G3X31x2X31x2X43xaLb;La;Lop;S43S0S0G3Lb;La;M6Lop;S44G6Lop;M7G7S2fS2eS0G3La;Lw;Lsgn;S2dS0S2cG3Lk;Li;Ll;X0x8").

Fixpoint find_sel (e : sv) : option (sv * sv * sv) :=
  match sel_here e with
  | Some r => Some r
  | None =>
      match e with
      | SAlu _ a b | SAluW _ a b | SMd _ a b | SMdW _ a b =>
          match find_sel a with Some r => Some r | None => find_sel b end
      | SExt _ _ a => find_sel a
      | _ => None
      end
  end.

Definition sel_case (dg : fdig) (a : sv) (k : Z) (b : sv) : bool := ltac2:(tb__ "0|3|
S31S30S30S0S0A2M0S0A2M1A1S2fLx;S11bVa;A1G1G1S2fLp;R1G0S0G0S2fLp0;R2S0S0S2fS2fL_;Sa6Vdg;S106R2S2Z0A1M2Va;A3Vk;Vb;A4Sa6S96S3bS1S14S5bR1G2A3S92Vdg;A1A3A1S106R2R3Va;A3Vk;Vb;A4S32X2fx2Lz;Lsel;X30x1Ly;Lp0;X30x1Lp;S32X31x2").

Definition aligned_tighten (dg : fdig) (a : sv) (k : Z) (b : sv) : bool := ltac2:(tb__ "0|3|
S64Sb9S92Vdg;A1M0Va;A2Sb9G0Vb;A2A2S2cS2fS2fL_;M1S5dZ1M2R1A2G1S5dVk;S61Z2R1A2A2Sa6Vdg;Va;G2Vb;A4S32X2fx2S32X2fx2Tj;").

Definition uleq_d (dg : fdig) (a : sv) (k : Z) (b : sv) : bool := ltac2:(tb__ "0|1|
Sd0Vdg;Va;A2S0S2fS2fL_;M0Sa6Vdg;R1Vk;Vb;A4S39G0S154Vdg;R1Vk;Vb;A4S39G0S153Vdg;R1Vk;Vb;A4S39S10eVdg;R1Vk;Vb;A4X2fx2X2fx2X2fx2Ta;").

Definition uleq (facts : list sprop) (a : sv) (k : Z) (b : sv) : bool := ltac2:(tb__ "0|0|
S2fS2fL_;S8eS89Vfacts;A1Va;Vk;Vb;A4S39S8eS96Vfacts;A1Va;Vk;Vb;A4X2fx2").

Definition sitv_of (p : Z * Z) : option (Z * Z) := ltac2:(tb__ "0|4|
S30S2cS2cA2M0S31G0A1M1Lp;Vp;S2cS2cS2fG1L_;M2S3dS5dR2R1A2A1S3aG0A1M3G2S60R1S88A2S35G0S33S2cS2cR2R1A4A2G2S5dS88R2A2S35G0S33S2cS2cS5fR2S78A2S5fR1S78A2A4A2G3X2fx2X2fx2X2fx2Lh;Ll;X30x1").

Definition sitv_d (dg : fdig) (e : sv) : option (Z * Z) := ltac2:(tb__ "0|3|
S31S30S2cS2cA2M0A1M1G1Lx;S155S121Vdg;Ve;A2A1G0S35G0R1A2M2Lp;S90Vdg;Ve;A2G0S2fG1L_;S5dS37S2cS2cR1A3S38S2cS2cR1A3A2G2S3aG0A1X2fx2Tp;X31x2").
Definition sitv (facts : list sprop) (e : sv) : option (Z * Z) := sitv_of (itv facts e).

Definition wnorm (facts : list sprop) (e : sv) : sv := wnorm_t (mk_ctx facts) e.

Definition sleq_same (dg : fdig) (a : sv) (k : Z) (b : sv) : bool := ltac2:(tb__ "0|0|
S31S2cA1S2fLx;S8dVa;Vb;A2S2cS86R1A1S2cS30S2cS2cA2S2fLx;S90Vdg;Vb;A2S2cS2cS34S34S34S5dR2R1A2S5dS81S5eR2R3A2A2A2S5dS5eR1R3A2S83A2A2S5dS5eR3Vk;A2Z0A2A2Lhb;Llb;X30x1Td;Ld0;S32X31x2").

Definition sleq_by_rel (dg : fdig) (a : sv) (k : Z) (b : sv) (r : sv * Z * sv) : bool := ltac2:(tb__ "0|4|
S30S30S0S2cA2M0S0A2S2fLr;Vr;G0S0G0S2fLp;R2S0S2cSa7Vdg;R2A2S0Sa7Vdg;R4A2S0S31S2cA1S2fLx;M1S8dVa;R2A2S2cG1S8dVb;R2A2S2cS86R2A1M2S2cG2S2cS30S2cS2cA2S2fLx;M3S90Vdg;R6A2S2cS2cG3S90Vdg;R7A2S2cS2cS34S34S34S34S34S34S5dR4R3A2S5dR2R1A2A2S5dS81S5eR4R6A2A2A2S5dS5eR3R6A2S83A2A2S5dS81S5eR2R5A2A2A2S5dS5eR1R5A2S83A2A2S5dS5eR6Vk;A2S5eR5RbA2A2A2Lhy;Lly;X30x1Lhx;Llx;X30x1Tdb;Tda;Ldb0;S32X31x2Lda0;S32X31x2Ty;Tx;Ld;Lx;X30x1Ly;Lp;X30x1").

Definition sleq_d (dg : fdig) (a0 : sv) (k : Z) (b0 : sv) : bool := ltac2:(tb__ "0|2|
Sa7Vdg;Va0;A2S0Sa7Vdg;Vb0;A2S0S30S2cS2cA2S2fLx;M0S90Vdg;R2A2S2cS2cG0S90Vdg;R3A2S2cS2cS2fS2fL_;M1S34S34S5dR4R3A2S5dR2R1A2A2S5dS5eR3Vk;A2R2A2A2S39G1S158Vdg;R6Vk;R5A4S39G1S157Vdg;Va0;Vk;Vb0;A4S39S1a6S30S30S0S2cA2S0A2S156Vdg;R6Vk;R5A4Sa2Vdg;A1A3X2fx2X2fx2X2fx2Lhb;Llb;X30x1Lha;Lla;X30x1Tb;Ta;").

Definition sleq (facts : list sprop) (a : sv) (k : Z) (b : sv) : bool := ltac2:(tb__ "0|0|
S2fS2fL_;S9fS89Vfacts;A1Va;Vk;Vb;A4S39S9fS96Vfacts;A1Va;Vk;Vb;A4X2fx2").

Definition prover_decide (dg : fdig) (c : branch_cond) (a b : sv) : decision := ltac2:(tb__ "0|a|
S45S7aLc;Vc;S2fS7aL_;M0S2fS2fL_;M1S8eVdg;Va;Z1M2Vb;A4M3S39S8eVdg;Vb;G2Va;A4X2fx2M4S7eG0G1S8eVdg;Va;Z0M5Vb;A4S8eVdg;Vb;G5Va;A4M6S32X2fx2M7S7fS85X2fx2X2fx2G0G4S7fG0G7S7eS85X2fx2X2fx2G0S9fVdg;Va;G2Vb;A4M8S7fG0S9fVdg;Vb;G5Va;A4M9S7eS85X2fx2X2fx2G0G8S7eG0G9S7fS85X2fx2X2fx2G0G3S7fG0G6S7eS85X2fx2X2fx2G0G3S7eG0G6S7fS85X2fx2X2fx2X45x6").

Definition decide_t (dg : fdig) (c : branch_cond) (a b : sv) : decision := ltac2:(tb__ "0|0|
S7aS7aLx;Sc3Vdg;Vc;Va;Vb;A4S7fS7eS149Vdg;Vc;Va;Vb;A4X7ax3").

Definition mk_slt_f_t (dg : fdig) (op : aluop) (a b : sv) : sv := ltac2:(tb__ "0|16|
S92Vdg;A1S36S1A1Sc6Vdg;S43S0Lop;Vop;S95R1Vop;Va;Vb;A4M0G0G0S2fS0L_;M1S4Va;Vb;A2M2S2Z0M3A1M4S7aS0Lx;M5SbcVdg;S50Va;Vb;A4S2Z1A1M6G4G0X7ax3X2fx2G1G2G4S31S0A1S0Lx;S15aVa;Vb;A2S0R1Lr;G5SbcVdg;S51Va;Vb;A4G6G4G0X7ax3X31x2X2fx2G0S0S0La;Va;S2cS95R2Vop;Va;Vb;A4M7Lz;S2dG7Li;S43S0S0S43S0Lop0;R3S95R4Vop;Va;Vb;A4M8G8S0S0Lb0;R1S2cS0S0Lb;Vb;S2cG1S2fS2fL_;M9S5dG3R1A2G9S5dR1R2A2G9S60R2Z40MaA2Sa0Vdg;R4S5fGaR2A2A3S32X2fx2S32X2fx2S32X2fx2S8cS4fR4S2S5fR2R1A2A1A3S95R6Vop;Va;Vb;A4MbX2fx2Ls;S2dGbLi;S43S0S0S95R8Vop;Va;Vb;A4McLb1;La0;MdLop1;MeGeS44GdLop1;MfGfS2fS2eS0GcLa0;Lw;Lsgn;S2dS0S2cGcLk0;Li;Ll;X0x8Lk;S2dS95R5Vop;Va;Vb;A4Li;S43S0S0S95R7Vop;Va;Vb;A4M10Lb1;La0;M11Lop1;M12G12S44G11Lop1;M13G13S2fS2eS0G10La0;Lw;Lsgn;S2dS0S2cG10Lk;Li;Ll;X0x8G8G8G8G8G8G8G8X43xaLb0;Lx;Lop0;S43S0S0G8Lb0;La0;M14Lop0;S44G14Lop0;M15G15S2fS2eS0G8La0;Lw;Lsgn;S2dS0S2cG8Lk;Li;Ll;X0x8G0G0G0X43xaA2Tfacts;").

Definition slt_retry (r : sv) : bool := ltac2:(tb__ "0|b|
S0S2fLr;Vr;S2cS32Lz;M0S2dS32Li;M1S43S0S0S43S2fLop;R3S32S32S32S39S39S32S0S2fLa;R2G0G1S43S0S0S43S2fLop0;R3S32S32S0S2fLb0;R1S2cS0S2fLb;R5S2cS39Lz;G1S43S0S0S32Lb1;La1;M2Lop1;M3G3S44G2Lop1;M4G4S2fS2eS0S32La1;Lw;Lsgn;M5S2dS0S2cS32Lk0;Li;Ll;X0x8Lk;G1G3G3G4G4G5S2dS0S2cS32Lk;Li;Ll;M6X0x8S32S32S32S32S32S32S32X43xaLb0;La0;Lop0;S43S0S0S32Lb0;La0;M7Lop0;S44G7Lop0;M8G8S2fS2eS0S32La0;Lw;Lsgn;G6X0x8S32S32S32X43xaLb;La;Lop;S43S0S0S32Lb;La;M9Lop;S44G9Lop;MaGaS2fS2eS0S32La;Lw;Lsgn;G6X0x8").

Definition mk_slt_f (facts : list sprop) (op : aluop) (a b : sv) : sv := ltac2:(tb__ "0|0|
Sf8S89Vfacts;A1Vop;Va;Vb;A4S0S2fS0L_;S159R1A1Sf8S96Vfacts;A1Vop;Va;Vb;A4R1X2fx2Tr;").

Definition sub_fold (a b : sv) : option sv := ltac2:(tb__ "0|8|
S0S31S0A1M0Lb;Vb;S2cS3aS0A1M1Lz;S2dG0G0Lx;S14aVb;Va;A2S0S35S0R1A2Loff;S30S76S2cA2G0Lx;M2S94Va;A1S76S2cG2S94Vb;A1S76S2cS9cR4R2A2S76S2fG0L_;S1b4S40S30S2cS0A2M3R1A2S1b1S40G3R5A2S40G3R3A2A2A2S35S0S105R1S5fR4R2A2A2A2G1X2fx2Td;Lcb;Llb;X30x1Lca;Lla;X30x1X31x2M4Li;S43S0S0G4Lb0;La0;M5Lop;M6G6S44G5Lop;M7G7S2fS2eS0G4La0;Lw;Lsgn;S2dS0S2cG4Lk;Li;Ll;X0x8").

Definition mk_op_f (facts : list sprop) (op : aluop) (a b : sv) : sv := ltac2:(tb__ "0|1|
S43S0Lop;Vop;ScaVfacts;Vop;Va;Vb;A4M0S31S0A1S0Lx;S104Va;Vb;A2S0Sc6S89Vfacts;A1R1A2Loff;G0X31x2G0G0G0G0G0G0G0G0X43xa").

Definition mk_opw_f (facts : list sprop) (op : aluop) (a b : sv) : sv := ltac2:(tb__ "0|1|
S43S0Lop;Vop;Sc8Vfacts;Vop;Va;Vb;A4M0S31S0A1S0Lx;S104Va;Vb;A2S0Sc8Vfacts;S49R1S2Z0A1A4Loff;G0X31x2G0G0G0G0G0G0G0G0X43xa").

Definition C3magic : Z := 0xAAAAAAAAAAAAAAAB.

Definition lit_is (a : sv) (k : Z) : bool := ltac2:(tb__ "0|3|
S0S2fLa;Va;S2cS62S80R1A1S80Vk;A1A2Lm;S2dS32Li;S43S0S0S32Lb;La0;M0Lop;M1G1S44G0Lop;M2G2S2fS2eS0S32La0;Lw;Lsgn;S2dS0S2cS32Lk0;Li;Ll;X0x8").
Definition mk_md_1 (op : mulop) (a b : sv) : option sv := ltac2:(tb__ "0|6|
S44S31S0A1M0Lop;Vop;S2fG0L_;M1Sb0Va;Z1M2A2S35S0Vb;A2G1Sb0Vb;G2A2S35S0Va;A2G1Sb0Va;N1M3A2S35S0S8cS49S2Z0A1M4Vb;A3A2G1Sb0Vb;G3A2S35S0S8cS49G4Va;A3A2S3aS0A1M5X2fx2X2fx2X2fx2X2fx2G5G5G5G5G5G5G5X44x8").

Definition mk_mdw_f (facts : list sprop) (op : mulop) (a b : sv) : sv := ltac2:(tb__ "0|1|
S44S0Lop;Vop;Sf6S52Va;Vb;A3S0S2fS0L_;S101Vfacts;R1Z1fA3R1S139Vop;Va;Vb;A3M0X2fx2Tr;G0G0G0G0G0G0G0X44x8").
Definition mk_md_f0 (facts : list sprop) (op : mulop) (a b : sv) : sv := ltac2:(tb__ "0|8|
S44S0Lop;Vop;Sf6Vop;Va;Vb;A3M0G0G0S0S0Lb;Vb;S2cS2fS0L_;M1S62S80R1A1S108A2S30S76S2cA2S0Lx;S94Va;A1S76S2cS36S30S2cS0A2M2A1M3S0Ll;R2G0G2G3G2S0Lp;R2S2cS0S2cS0Lz0;R2G0S2dS2dS0Lp0;R1S2dS2dS0Lp1;R1S2dG0Lp2;M4G4G3S0Ll0;R5S2cS0Lz;R7G1S101Vfacts;R3Z3eA3S8cS4fR3S2Z1A1A3G0X2fx2G4G4X2cx3G2G3G0Ll1;Lp2;X36x2X2dx3Lp1;S2dG0Lp1;G0X2dx3Lp0;S2dG0Lp0;X2cx3Lv;Lz0;X30x1Ll0;Lp;X36x2Lz;Ll;X30x1G0X2fx2Lc;S2dG0Li;S43S0S0G0Lb0;La0;M5Lop0;M6G6S44G5Lop0;M7G7S2fS2eS0G0La0;Lw;Lsgn;S2dS0S2cG0Lk;Li;Ll;X0x8G0G0G0G0X44x8").
Definition mk_md_f (facts : list sprop) (op : mulop) (a b : sv) : sv := ltac2:(tb__ "0|0|
S31S0A1S0Lx;S136Vop;Va;Vb;A3S0R1Lr;S138Vfacts;Vop;Va;Vb;A4X31x2").

Definition in_bounds_d (dg : fdig) (lo hi off : sv) (k : Z) : bool := ltac2:(tb__ "0|5|
S31S30S2cS2cA2M0A1S2fLx;M1S9eVdg;Vlo;A2G0G0S2fLp;R1S2cS2cG1S9eVdg;Vhi;A2G0G0S2fLp0;R1S2cS2cG1S9eVdg;Voff;A2G0G0S2fLp1;R1S2cS2cS2fS2fL_;M2G2S5dR7R2A2S39G2G2S34S5dZ0M3R8A2S5dG3R2A2M4A2S8eVdg;Vlo;G3Voff;A4S32X2fx2S39S9fVdg;Vlo;G3Voff;A4X2fx2X2fx2G2S5dS5eR1Vk;A2R5A2S39G2G2S34G4S5dG3R5A2A2S8eVdg;Voff;Vk;Vhi;A4S32X2fx2S39S9fVdg;Voff;Vk;Vhi;A4X2fx2X2fx2S32X2fx2Lh3;Ll3;X30x1Lp1;S32X31x2Lh2;Ll2;X30x1Lp0;S32X31x2Lh1;Ll1;X30x1Lp;S32X31x2").

Definition in_bounds (facts : list sprop) (lo hi off : sv) (k : Z) : bool := ltac2:(tb__ "0|0|
S2fS2fL_;Se5S89Vfacts;A1Vlo;Vhi;Voff;Vk;A5S39Se5S96Vfacts;A1Vlo;Vhi;Voff;Vk;A5X2fx2").

Definition atom_index (t : sv) (esz : Z) : option sv := ltac2:(tb__ "0|21|
S0S31S0A1M0Lt;Vt;S2cS3aS0A1M1Lz;S2dG1Li;M2S43S0S0S43G0Lop;R3G1G1S0G0Lb;R1S2cS2fG0L_;M3S34S34S5dZ0R1A2S60R1Z40M4A2A2S62S61Z2M5R1A2Vesz;A2A2S35S0R3A2G1X2fx2Lsh;G2S43S0S0G1Lb0;M6La;M7Lop0;M8G8S44G7Lop0;M9G9S2fS2eS0G1La;Lw;Lsgn;MaS2dS0S2cG1Lk;MbLi;Ll;McX0x8G1G1G1G1G1G1G1X43xaLb;Lx;Lop;S43S0S0G1Lb;MdLa;MeLop;MfS44S0S0S44G0Lop;R3S0G0Lx;M10R2S2cG3S62S63R1S61G5G4A2A2Vesz;A2M11S35S0R2A2G10R2S2cG3G11S35S0S2R2A1A2G1X2fx2Le';G2GfGfS44GeLop;M12G12GaGcX0x8X2fx2Le;S2dG10R2S2cG3G11S35S0R4A2G1X2fx2Le;S2dG1Li0;M13S43GeLop0;M14G14S44GeLop0;M15G15GaS2dS0GbLi0;Ll;X0x8Li;S43S0S0G10R4S2cG3G11S35S0R6A2G1X2fx2Le;M16G2S43S0G6La0;M17Lop1;M18G18S44G17Lop1;M19G19S2fS2eS0G1La0;M1aLw;Lsgn;GcX0x8Lb;La;M1bLop0;M1cG1cS44G1bLop0;M1dG1dS2fS2eS0G10R4G16G2S43S0GdLa0;M1eLop0;M1fG1fS44G1eLop0;M20G20S2fS2eG1aLw0;Lsgn0;GcX0x8La;Lw;Lsgn;S2dS0S2cG10R4G16G13G14G14G15G15GaS2dS0S2cG1Lk0;Li0;Ll0;X0x8Lk;Li;Ll;X0x8G1G1G1G1G1G1G1X44x8Lx;Lx;Lop;G12GaGcX0x8").

Definition lin_decomp_syn (d : sv) (esz : Z) : option (sv * Z) := ltac2:(tb__ "0|5|
S30S36S0A1M0S2cA2S31S30S0S2cA2M1A1M2Lx;S97Vd;S3eS0A1Z0A3G0S2cG0G2Latoms;R2S63R1S61Z2Z40A2A2S2cS35G1S33S0S2cS2S68R1Vesz;A2A1S63R1Vesz;A2A4A2Tc';S0G0G0G2Ll;R1S31S0A1M3G2Lx;S2fG3L_;S62Vesz;Z1A2S35S0R2A2S114R2Vesz;A2X2fx2S0S35G1S33S0S2cS8bR1S68R4Vesz;A2A2S63R4Vesz;A2A4A2Lx;S3aG1A1M4X31x2S0G0G4Ll0;Ls;X36x2Ll;Lt;X36x2Lc;Latoms;X30x1").

Fixpoint lin_decomp_facts (facts : list sprop) (d : sv) (esz : Z) : option (sv * Z) :=
  match facts with
  | [] => None
  | SPEq a b :: rest =>
      let try1 := match same_atoms d a with
                  | Some delta => lin_decomp_syn (mk_addk b delta) esz
                  | None => None
                  end in
      match try1 with
      | Some r => Some r
      | None =>
          let try2 := match same_atoms d b with
                      | Some delta => lin_decomp_syn (mk_addk a delta) esz
                      | None => None
                      end in
          match try2 with
          | Some r => Some r
          | None => lin_decomp_facts rest d esz
          end
      end
  | _ :: rest => lin_decomp_facts rest d esz
  end.

Definition lin_decomp (facts : list sprop) (d : sv) (esz : Z) : option (sv * Z) := ltac2:(tb__ "0|2|
S2fS31S30S0S2cA2M0A1M1L_;S34S60Z0Vesz;A2S60Vesz;S61Z2Z3eA2A2A2G1G1Lx;S126Vd;Vesz;A2G0S35G0R1A2Lr;S125Vfacts;Vd;Vesz;A3X31x2S3aG0A1X2fx2").

Fixpoint find_obj_d (objs : list sobj) (dg : fdig) (ae : sv) (k : Z) (n : nat)
  : option (nat * sobj * sv) :=
  match objs with
  | [] => None
  | o :: rest =>
      let here :=
        match rel_offset (ob_base o) ae with
        | Some off => if in_bounds_d dg (ob_lo o) (ob_hi o) off k then Some (n, o, off) else None
        | None => None
        end in
      match here with
      | Some r => Some r
      | None => find_obj_d rest dg ae k (S n)
      end
  end.

Definition find_obj (objs : list sobj) (facts : list sprop) (ae : sv) (k : Z) (n : nat)
  : option (nat * sobj * sv) := ltac2:(tb__ "0|2|
S31S30S30S3cS5A2S0A2M0A1M1G1Lx;SdfVobjs;S89Vfacts;A1Vae;Vk;Vn;A5G0S35G0R1A2Lr;SdfVobjs;S96Vfacts;A1Vae;Vk;Vn;A5X31x2").

Inductive crel :=
| CLit (d : Z)
| CDisj
| CUnk.

Definition cell_rel (facts : list sprop) (off : sv) (k : Z) (c : cell) : crel := ltac2:(tb__ "0|6|
S31S2cA1SbbLx;S8dS28Vc;A1M0Voff;A2S2cS109S86R1A1A1Ld;S96Vfacts;A1Sa3S31S30S2cS2cA2M1A1S2fLx;M2S9eR1Voff;A2G1G1S2fLp;M3R1S2cS2cG2S9eR4G0A2G1G1S2fLp0;R1S2cS2cS3fS5dS5eR4Vk;A2R2A2S5dS5eR1S29Vc;A1M4A2R5A2A2Lh2;Ll2;X30x1Lp0;S32X31x2Lh1;Ll1;X30x1Lp;S32X31x2S2fS0G2S9eR3R1A2G1G3R1S2cS2cS5dZ0R2A2Lz;Ll;X30x1Lp;S32X31x2Le;S0S2fFe;S2fSbbLby_itv;R2Sd2S2fSbbL_;S2fS2fL_;M5S34R1Voff;A1R1G0A1A2G5S8eR3Voff;Vk;G0A4S39S8eR3G0G4Voff;A4X2fx2S32X2fx2Sd2S10aX2fx2X2fx2Tnonneg;Tby_itv;Tdg;X31x2").

Definition lit_overlaps (d w k : Z) : bool := ltac2:(tb__ "0|0|
S34S60Vd;Vk;A2S60Z0S5eVd;Vw;A2A2A2").

Inductive cell_read :=
| CRExact (v : sv)
| CRInside (v : sv) (sh : Z)
| CRNone
| CRTile
| CRUnknown.

Fixpoint read_cells (facts : list sprop) (cells : list cell) (off : sv) (k : Z) (acc : cell_read) : cell_read :=
  match cells with
  | [] => acc
  | c :: rest =>
      match cell_rel facts off k c with
      | CLit d =>
          if lit_overlaps d (c_width c) k then
            if (d =? 0) && (c_width c =? k) then CRExact (c_val c)
            else if (d <=? 0) && (k <=? d + c_width c) then CRInside (c_val c) (- d)
            else read_cells facts rest off k (match acc with CRUnknown => CRUnknown | _ => CRTile end)
          else read_cells facts rest off k acc
      | CDisj => read_cells facts rest off k acc
      | CUnk => read_cells facts rest off k CRUnknown
      end
  end.

Fixpoint lit_cells (facts : list sprop) (cells : list cell) (off : sv) (k : Z) : list (Z * Z * sv) :=
  match cells with
  | [] => []
  | c :: rest =>
      match cell_rel facts off k c with
      | CLit d => (d, c_width c, c_val c) :: lit_cells facts rest off k
      | _ => lit_cells facts rest off k
      end
  end.

Fixpoint find_lcell_at (cells : list (Z * Z * sv)) (p : Z) : option (Z * sv) :=
  match cells with
  | [] => None
  | (d, w, v) :: rest => if d =? p then Some (w, v) else find_lcell_at rest p
  end.

Fixpoint tile_cells (fuel : nat) (cells : list (Z * Z * sv)) (p stop : Z) : option sv :=
  match fuel with
  | O => None
  | S fuel' =>
      if p =? stop then Some (SLit 0)
      else match find_lcell_at cells p with
           | Some (w, v) =>
               if (0 <? w) && (p + w <=? stop) then
                 match tile_cells fuel' cells (p + w) stop with
                 | Some rest =>
                     Some (mk_alu ALU_OR
                             (mk_alu ALU_SLL (mk_ext false (8 * Z.to_N w)%N v) (SLit (8 * p)))
                             rest)
                 | None => None
                 end
               else None
           | None => None
           end
  end.

Fixpoint store_cells (facts : list sprop) (cells : list cell) (off : sv) (k : Z) : list cell * bool :=
  match cells with
  | [] => ([], false)
  | c :: rest =>
      let '(rest', taint) := store_cells facts rest off k in
      match cell_rel facts off k c with
      | CLit d =>
          if lit_overlaps d (c_width c) k then
            let lo_keep := if d <? 0 then [mkCell (c_off c) (- d) (c_val c)] else [] in
            let hi_keep := if k <? d + c_width c
                           then [mkCell (mk_addk off k) (d + c_width c - k)
                                        (mk_alu ALU_SRL (c_val c) (SLit (8 * (k - d))))]
                           else [] in
            (lo_keep ++ hi_keep ++ rest', taint)
          else (c :: rest', taint)
      | CDisj => (c :: rest', taint)
      | CUnk => (rest', true)
      end
  end.

Fixpoint list_upd {A} (l : list A) (n : nat) (f : A -> A) : list A :=
  match l, n with
  | [], _ => []
  | h :: t, O => f h :: t
  | h :: t, S n' => h :: list_upd t n' f
  end.

Definition obj_store (facts : list sprop) (o : sobj) (off : sv) (k : Z) (v : sv) : sobj := ltac2:(tb__ "0|1|
S30S36S1eA1M0S2fA2S5Lx;S160Vfacts;S16Vo;A1Voff;Vk;A4G0S2fS1fS1bVo;A1S17Vo;A1S20Vo;A1S3bS1eS26Voff;Vk;Vv;A3R2A3S2fS6Ltaint;R1S19SdVo;A1X2fx2A5Ltaint;Lcells';X30x1").

Definition obj_add_cell (o : sobj) (off : sv) (k : Z) (v : sv) : sobj := ltac2:(tb__ "0|0|
S1fS1bVo;A1S17Vo;A1S20Vo;A1S3bS1eS26Voff;Vk;Vv;A3S16Vo;A1A3SdVo;A1A5").

Fixpoint fld_index (flds : list (Z * Z)) (c k : Z) : option nat :=
  match flds with
  | [] => None
  | f :: rest => if (fst f =? c) && (snd f =? k) then Some O
                 else option_map S (fld_index rest c k)
  end.

Fixpoint fld_vars (x0 : positive) (m : nat) : list sv :=
  match m with
  | O => []
  | S m' => SVar x0 :: fld_vars (Pos.succ x0) m'
  end.

Fixpoint arr_cells (off0 : sv) (flds : list (Z * Z)) (x0 : positive) : list cell :=
  match flds with
  | [] => []
  | f :: rest => mkCell (mk_addk off0 (fst f)) (snd f) (SVar x0) :: arr_cells off0 rest (Pos.succ x0)
  end.

Fixpoint strip_ext (w : N) (x : sv) : sv :=
  match x with
  | SExt _ w' a => if (w <=? w')%N && (w' <=? 64)%N then strip_ext w a else x
  | _ => x
  end.

Definition extsv (sx : option (bool * N)) (x : sv) : sv := ltac2:(tb__ "0|1|
S31S30S2fS2eA2M0A1S0Lsx;Vsx;G0G0S0Lp;R1S2fS2eS84R2R1S162R1Vx;A2A3Lw;Lsgn;X30x1Lp;Vx;X31x2").

Definition narrow (facts : list sprop) (k : Z) (v : sv) : sv := ltac2:(tb__ "0|0|
S30S2cS2cA2S0Lx;Se8Vfacts;Vv;A2S2cS2cS2fS0L_;S34S5dR2R1A2S60R1S61Z2S66Z8Vk;A2A2A2A2Vv;S84S32S1b5Q8S6eVk;A1A2Vv;A3X2fx2Lh;Ll;X30x1").

Definition sp_rel (strict : bool) (a b : sv) : sprop := ltac2:(tb__ "0|0|
S2fS1Lstrict;Vstrict;S27Va;Vb;A2S1aVa;Vb;A2X2fx2").

Definition tf_inst (xs : list sv) (t : tfact) : list sprop := ltac2:(tb__ "0|7|
SbS36S1A1Lt;Vt;S2fS3cS31S30S2fS2eA2A1M0S0S3bS1ScfR4S11aR2S1a4S0R3Vxs;S2Z0A1M1A4M2A2M3R1A3S3eS1A1M4A3Le;Lsx;Li;Ls;S2fS3cG0S0S3bS1ScfR4R1G3A3G4A3Le;Lsx;Li;Ls;S2fS3cS3cS0S3bS1ScfR4S9S4bG2S1a4S0R2Vxs;G1A4M5A3M6R1A3S3bS1S1aG2G6A2S3bS1S1aG2R1A2S3bS1S1aG5R1A2G4A3A3A3A3Le;Lj;Li;Ls;Xbx3").

Fixpoint tmpl_inst (xs : list sv) (tmpl : list tfact) : list sprop :=
  match tmpl with
  | [] => []
  | t :: rest => tf_inst xs t ++ tmpl_inst xs rest
  end.

Definition tf_mentions (i : nat) (t : tfact) : bool := ltac2:(tb__ "0|2|
SbS2fLt;Vt;S2fS3cS31S30S2fS2eA2A1S0S1b3Vi;R3A2M0Le;Lsx;Lj;Lstrict;M1G1S2fS3cS3cS0S3fG0S1b3Vi;R2A2A2Le;Ll;Lj;Lstrict;Xbx3").

Definition prove_sprop (facts : list sprop) (p : sprop) : bool := ltac2:(tb__ "0|1|
S3fS1a6S1S2bVp;A1Vfacts;A3S1S2fLp;Vp;S45S0S0S32Lb;La;M0Lc;S1S32Lp0;S0S0Sb6Vfacts;R2Z1R1A4Lb;La;S0S0Sb6Vfacts;R2Z0R1A4Lb;La;G0S32S2dS2cS32La;Li;X1x7A2").

Definition fld_cached (facts : list sprop) (cells : list cell) (off0 : sv) (f : Z * Z) : option sv := ltac2:(tb__ "0|2|
Sa8S31S0A1Lx;SfaVfacts;Vcells;S8bVoff0;S37S2cS2cVf;A3A2S38S2cS2cVf;A3M0Sd3A5S0S35S0S84S32S1b5Q8S6eG0A1A2R1A3A2Lv;S0S2cS3aS0A1M1Lsh;Lv;G1G1G1Xa8x5").

Fixpoint store_xs (facts : list sprop) (cells : list cell) (off0 : sv) (flds : list (Z * Z))
         (i : nat) (v : sv) (k : Z) (need : nat -> bool) (j : nat) : option (list sv) :=
  match flds with
  | [] => Some []
  | f :: rest =>
      let here :=
        if Nat.eqb j i then Some (narrow facts k v)
        else if need j then fld_cached facts cells off0 f
        else Some (SLit 0) in
      match here, store_xs facts cells off0 rest i v k need (S j) with
      | Some x, Some xs => Some (x :: xs)
      | _, _ => None
      end
  end.

Definition flds_apart (flds : list (Z * Z)) (i : nat) (c k : Z) : bool := ltac2:(tb__ "0|4|
S1a7S30S3cS30S2cS2cA2M0A2M1G1S3fS1b3S37S3cG0R1A3Vi;A2S3fS5dS5eS38S2cS2cS38S3cG0R1A3M2A3S37S2cS2cG2A3M3A2Vc;A2S5dS5eVc;Vk;A2G3A2A2A2Ljf;S1a9S3cG0S1a5U0S40G0Vflds;A2A2Vflds;A4A3").

Definition arr_after_store (facts : list sprop) (o : sobj) (off : sv) (k : Z) (v : sv)
           (esz : Z) (cnt : sv) (flds : list (Z * Z)) (tmpl : list tfact) : odefault := ltac2:(tb__ "0|3|
S31S30S0S2cA2M0A1S6Lx;SebVfacts;S8cS49Voff;S17Vo;A1A3Vesz;A3G0G0S6Lp;R1S0S2cS31S2cA1S2fLx;S8dR2Vcnt;A2S2cS34S5dZ0R1A2S60S5eS66Vesz;R1A2R2A2S61Z2Z3eA2A2A2Ldlt;S32X31x2S2fS2fS6Lbeyond;R1SdVo;A1M1S31S3cA1S6Lx;Se0Vflds;R2Vk;A3S3cS8bVoff;S67R3A1A2S0S3cS1a6SbSbS34Sd1R4R1A2Sd1R2R1A2A2Lt;Vtmpl;A3Lj;S3cS2fFj;S31S36S0A1M2A1S6Lx;S161Vfacts;S16Vo;A1R2Vflds;R3Vv;Vk;R1U0A9G2S2fS6L_;S34S34Sb6Vfacts;R7Z1Vcnt;A4S11dVflds;R4R6Vk;A4A2S1a7SbSbS3fS3dSd1R5R1A2A1S1a7S1S148Vfacts;A1S16eR2R1A2A3A2Lt;Vtmpl;A3A2G1S19X2fx2Lxs;S19X31x2Tneed;Toff0;Li;S19X31x2X2fx2Tbeyond;Lc;Lidx;X30x1Lp;S19X31x2").

Definition obj_store_d (facts : list sprop) (o : sobj) (off : sv) (k : Z) (v : sv) : sobj := ltac2:(tb__ "0|1|
S145Vfacts;Vo;Voff;Vk;Vv;A5S5S6S5Lx;SdVo;A1R1R1R1S2dR2Ll;M0G0S2cS0S36S30S2cS2cA2A1S36SbA1S1fS1bR5A1S17R5A1S20R5A1S16R5A1S112Vfacts;Vo;Voff;Vk;Vv;R4R3R2R1A9A5Ltmpl;Lflds;Lcnt;Lesz;X6x6To1;").

Section WithImage.
  Variable segs : list Segment.

  Fixpoint image_bytes (a : Z) (k : nat) : option (list byte) :=
    match k with
    | O => Some []
    | S k' => match image_byte segs (Z_to_bv 64 a), image_bytes (a + 1) k' with
              | Some b, Some bs => Some (b :: bs)
              | _, _ => None
              end
    end.

  Fixpoint all_ro (a : Z) (k : nat) : bool :=
    match k with
    | O => true
    | S k' => ro_addr segs (Z_to_bv 64 a) && all_ro (a + 1) k'
    end.

  Definition ro_load (a : Z) (k : nat) : option Z := ltac2:(tb__ "0|3|
S2fS31S2cA1M0L_;S34S34S5dZ0Va;A2S5dS5eVa;S73Vk;A1A2S61Z2Z40A2A2A2S184Va;Vk;A2A2S31S36S19eQ8A1A1M1A1G0Lx;S17fVa;Vk;A2G1S35S2cS1b7R1A1A2Lbs;S3aS2cA1M2X31x2G2X2fx2").

  Definition ro_span_max : Z := 4096.
  Definition ro_span (facts : list sprop) (ae : sv) (k : Z) : bool := ltac2:(tb__ "0|3|
S30S2cS2cA2S2fLx;Se8Vfacts;Vae;A2S2cS2cS5fS5eR1Vk;A2R2A2S2cS2fS2fL_;M0S5dR3R2A2G0S5dR1S19dA2G0S5dS5eR2Vk;A2S78A2G0S184R3S6cR1A1M1A2S31S36S19eQ8A1A1M2A1S2fLx;S17fR3G1A2G2S39Ll;S32X31x2S32X2fx2S32X2fx2S32X2fx2S32X2fx2Tn;Lhi;Llo;X30x1").

  Definition image_load (a : Z) (k : nat) : option Z := ltac2:(tb__ "0|1|
S31S36S19eQ8A1A1M0A1S31S2cA1Lx;S17fVa;Vk;A2G0S35S2cS1b7R1A1A2Lbs;S3aS2cA1X31x2").

  Inductive load_res :=
  | LROk (v : sv) (S' : sstate)
  | LRFail.

  Definition load_fresh (S : sstate) (n : nat) (o : sobj) (off : sv) (k : Z) (sgn : bool) (w : N) : load_res := ltac2:(tb__ "0|0|
S30S0S3A2S177Lx;S99VS;A1S0S3S2fS177L_;S25SdVo;A1A1S144Vo;Voff;Vk;R2A4S5S179S84Vsgn;Vw;R3A3SfdR2SafS5ScR2A1Vn;R1A4A2A2To';S179S84Vsgn;Vw;R2A3R1A2X2fx2LS1;Lx;X30x1").

  Definition load_arr (S : sstate) (n : nat) (o : sobj) (off : sv) (k : Z) (sgn : bool) (w : N)
             (esz : Z) (cnt : sv) (flds : list (Z * Z)) (tmpl : list tfact) : load_res := ltac2:(tb__ "0|4|
S7VS;A1S36S1A1S31S30S0S2cA2M0A1S177Lx;SebR1S8cS49Voff;S17Vo;A1M1A3Vesz;A3G0G0S177Lp;R1S0S2cS31S3cA1S177Lx;Se0Vflds;R1Vk;A3S3cS2fS177L_;Sb6R5R3Z1Vcnt;A4S11VS;A1S2dS40S30S2cS2cA2Vflds;A2S3cS11cR2R1A2S36S0A1S8bVoff;S67R5A1A2S0S1fS1bVo;A1G1S20Vo;A1S41S1eS113R1Vflds;R4A3S16Vo;A1A3SdVo;A1A5S5S179S84Vsgn;Vw;S15S1b8S1b1S1baR5A1M2R6A2A1A1A3SfS8VS;A1S12VS;A1S10VS;A1SaVS;A1S13VS;A1SafS5ScVS;A1Vn;R1A4S41S1S170R3Vtmpl;A2RaA3S1b8S1b1G2R4A2A1SeVS;A1A9A2To';Toff0;Txs;Tm;Tx0;S17bVS;Vn;Vo;Voff;Vk;Vsgn;Vw;A7M3X2fx2Li;G3X31x2Lc;Lidx;X30x1Lp;G3X31x2Tfacts;").

  Definition load_dflt (S : sstate) (n : nat) (o : sobj) (off : sv) (k : Z) (sgn : bool) (w : N) : load_res := ltac2:(tb__ "0|2|
S6S177Lx;SdVo;A1S17bVS;Vn;Vo;Voff;Vk;Vsgn;Vw;A7M0G0G0S2dG0Ll;M1G1S2cS0S36S30S2cS2cA2A1S36SbA1S18aVS;Vn;Vo;Voff;Vk;Vsgn;Vw;R4R3R2R1AbLtmpl;Lflds;Lcnt;Lesz;X6x6").

  Definition sym_load (S : sstate) (ae : sv) (k : Z) (sgn : bool) : load_res := ltac2:(tb__ "0|18|
S1b5Q8S6eVk;A1A2S2eS7VS;A1S36S1A1S0S31S2cA1M0Lae;Vae;S2cS19bS63R1S61Z2Z40A2A2M1S6cVk;A1M2A2La;S2dS3aS2cA1M3Li;S43S0S0G3Lb;La;M4Lop;M5G5S44G4Lop;M6G6S2fS2eS0G3La;Lw0;Lsgn0;S2dS0S2cG3Lk0;Li;Ll;X0x8G0G0S177Lro;R1S2cS179S84Vsgn;R4S2R1A1M7A3VS;A2Lz;S31S30S30S3cS5A2M8S0A2M9A1S177Lx;SdeScVS;A1R2Vae;Vk;U0A5G9G9S177Lp;R1G8S0G8S177Lp0;R2S3cS5Sa8S177Lx;SfaR7S16R1A1MaR3Vk;Sd3A5S0S179Sc9R8Vsgn;R9R1A4VS;A2Lv;S0S2cS179Sc9R9Vsgn;RaS8cS59R2S2S66Z8R1A2A1A3A4VS;A2Lsh;Lv;S6S177Lx;SdR1A1S17bVS;R2R1R3Vk;Vsgn;R8A7S179S2Z0MbA1VS;A2S0S177Lx;S1bR1A1S2cS2cS177Lz;R1S0S177Loff;R4S2cG0S177Lx;S197G1G2A2S2cS179S84Vsgn;RbG7A3VS;A2Lz;S181X31x2Lzo;S2dS17bVS;R4R3R5Vk;Vsgn;RaA7McLi;S43S0S0S17bVS;R6R5R7Vk;Vsgn;RcA7MdLb;La;MeLop;MfGfS44GeLop;M10G10S2fS2eS0GdLa;Lw0;Lsgn0;S2dS0S2cGdLk0;Li;Ll;X0x8S2dGcLp;M11G11X2cx3Lz;S2dS17bVS;R3R2R4Vk;Vsgn;R9A7Li;S43S0S0S17bVS;R5R4R6Vk;Vsgn;RbA7M12Lb;La;M13Lop;M14G14S44G13Lop;M15G15S2fS2eS0G12La;Lw0;Lsgn0;S2dS0S2cG12Lk0;Li;Ll;X0x8S2dS179Sc9R8Vsgn;R9S21R1S95R8S49R4S17R2A1A4Vk;A3A4VS;A2Ll;M16G16S2cS0S36S30S2cS2cA2A1S36SbA1S18aVS;R6R5R7Vk;Vsgn;RcR4R3R2R1AbLtmpl;Lflds;Lcnt;Lesz;X6x6S31S0A1S177Lx;S16fU9S12fR7GaR3Vk;A4GbVk;A4S0S179S84Vsgn;R9R1A3VS;A2Lv;S199VS;R2R1R3Vk;Vsgn;R8A7M17X31x2G17Xa8x5Lo;Ln;X30x1Loff;Lp0;X30x1Lp;S2fS177L_;S2fS2fL_;SeVS;A1S39S19cR2Vae;Vk;A3X2fx2S30S0S3A2S177Lx;S99VS;A1S0S3S179S84Vsgn;R5R2A3R1A2LS1;Lx;X30x1S181X2fx2X31x2X31x2Tro;Tfacts;Tw;").

  Definition sym_store (S : sstate) (ae : sv) (k : Z) (v : sv) : option sstate := ltac2:(tb__ "0|6|
S31S30S30S3cS5A2M0S0A2M1A1S31S3A1M2Lx;SdeScVS;A1M3S7VS;A1M4Vae;Vk;U0A5G1G1G2Lp;R1G0S0G0G2Lp0;R2S3cS5S2fG2L_;S25SdR1A1A1S35S3SfdVS;S12dS5G3R2S5S146G4R1R4Vk;Vv;A5Lo;A4A2A2S3aS3A1M5X2fx2Lo;Ln;X30x1Loff;Lp0;X30x1Lp;G5X31x2").

  Definition canon_branch (c : branch_cond) (a b : sv) : sprop := ltac2:(tb__ "0|3|
S45S1Lc;Vc;S14S5aVa;Vb;A3M0S1dG0A1S14S50Va;Vb;A3M1S1dG1A1S14S51Va;Vb;A3M2S1dG2A1X45x6").

  Fixpoint canon_prop (p : sprop) : sprop :=
    match p with
    | SPBranch c a b => canon_branch c a b
    | SPNot q => match canon_prop q with
                 | SPNot r => r
                 | r => SPNot r
                 end
    | _ => p
    end.

  Fixpoint fact_lookup (facts : list sprop) (p : sprop) : decision :=
    match facts with
    | [] => DUnknown_
    | f :: rest =>
        let cf := canon_prop f in
        let cp := canon_prop p in
        if sprop_eqb cf cp then DTrue
        else if sprop_eqb cf (canon_prop (SPNot p)) then DFalse
        else fact_lookup rest p
    end.

  Definition decide_branch (S : sstate) (c : branch_cond) (a b : sv) : decision := ltac2:(tb__ "0|10|
S0S7aLa;Va;S2cS0S7aLb;Vb;S2cS2fS7aL_;M0S1afVc;S19fQ40M1R2A2S19fG1R1A2A3S7fS7eX2fx2Ly;S2dG0S4Va;Vb;A2S45S7aLc;M2Vc;S7fS7eS7eS7fS7eS7fX45x6G2Vc;S31S2fA1S7aLx;M3S14fVa;Vb;A2M4S2fS2fS7aLe;M5R1S7fS7eX2fx2Le;S7aS7aLx;M6S194S7VS;A1M7S14Vc;Va;Vb;A3A2S7fS7eG6Sc3S89G7A1Vc;Va;Vb;A4S7fS7eSbcS96G7A1Vc;Va;Vb;A4X7ax3X7ax3M8X31x2G3G4S2fG5R1S7eS7fX2fx2Le;G8X31x2G8G8G8G8X45x6X2fx2M9Li;MaS43S0S0G9Lb0;La0;MbLop;McGcS44GbLop;MdGdS2fS2eS0G9La0;Lw;Lsgn;MeS2dS0S2cG9Lk;Li;Ll;MfX0x8Lx;GaGcGcGdGdGeGfX0x8").

  Inductive stop_reason :=
  | RsEcall | RsCut | RsNoCode | RsUnsupported | RsSymJump | RsMem | RsFuel.

  Inductive step_out :=
  | StNext (S' : sstate)
  | StFork (S1 S2 : sstate)
  | StStop (r : stop_reason).

  Definition immI (imm : bv 12) : Z := bv_signed imm.
  Definition msz (sz : msize) : Z := msize_bytes sz.

  Definition rm_ok (S : sstate) (rm : bv 3) : bool := ltac2:(tb__ "0|0|
S18S2fLx;SaVS;A1S1a0Q3Vrm;A2S2cS3fS5dR1Z4A2S62R1Z7A2A2Tr;S0S32Lv;X18x2").

  Definition addr_aligned (facts : list sprop) (ae : sv) (a : Z) : bool := ltac2:(tb__ "0|b|
S34S34S5dZ0M0Va;A2S5dVa;Z40M1A2A2S0S2fLae;Vae;S2cS62S63S63R1S61Z2M2G1A2A2S61G2Va;A2A2G0A2M3Lz;S2dS5dVa;Sa1Vfacts;R1A2A2Lj;S43S0S0S43S2fLop;R3S0S2fLa0;R2S2cS32Lz;S2dS0S2fLb;R2S2cS34S5dVa;Sa1Vfacts;R2A2A2G3A2Lc;S2dS32Li;S43S0S0S32Lb0;La1;M4Lop0;M5G5S44G4Lop0;M6G6S2fS2eS0S32La1;Lw;Lsgn;M7S2dS0S2cS32Lk;Li;Ll;M8X0x8Lj;G5G5G6G6G7G8X0x8S32S32S32S32S32S32S32S32S32X43xaLb;La0;Lop;S43S0S0S32Lb;La0;M9Lop;S44G9Lop;MaGaS2fS2eS0S32La0;Lw;Lsgn;G8X0x8A2").

  Definition amo_k (wd : awidth) : Z := match wd with AW => 4 | AD => 8 end.
  Definition amo_log (wd : awidth) : Z := match wd with AW => 2 | AD => 3 end.

  Definition mk_nanbox (e : sv) : sv := mk_alu ALU_OR e (SLit 18446744069414584320).

  Definition sym_csr (S : sstate) (op : csrop) (rd : reg) (writes : bool) (csr : bv 12) : step_out := ltac2:(tb__ "0|3|
S18S178Lx;SaVS;A1S1a0QcVcsr;A2S2cS2fS178L_;M0S34S62R1Z2A2S3dVwrites;A1A2S17aS87S7dVS;Vrd;S2Z0A1A3S5eS8VS;A1Z4A2M1A2A1G0S62R1Z1A2S30S0S3A2S178Lx;S99VS;A1S0S3S17aS87S7dR1Vrd;R2A3G1A2A1LS1;Lx;X30x1S17cS182A1M2X2fx2X2fx2Tc;S0G2Lv;X18x2").

  Definition havoc_freg (S : sstate) (rd : reg) : step_out := ltac2:(tb__ "0|0|
S30S0S3A2S178Lx;S99VS;A1S0S3S17aS87Sa4R1Vrd;R2A3S5eS8VS;A1Z4A2A2A1LS1;Lx;X30x1").
  Definition havoc_reg (S : sstate) (rd : reg) : step_out := ltac2:(tb__ "0|0|
S30S0S3A2S178Lx;S99VS;A1S0S3S17aS87S7dR1Vrd;R2A3S5eS8VS;A1Z4A2A2A1LS1;Lx;X30x1").

  Definition havoc_reg_b (S : sstate) (rd : reg) : step_out := ltac2:(tb__ "0|0|
S30S0S3A2S178Lx;S99VS;A1S0S3S17aS87S7dSb7R1S1aR2S2Z1A1A2A2Vrd;R2A3S5eS8VS;A1Z4A2A2A1LS1;Lx;X30x1").

  Definition frm0b (S : sstate) : bool := ltac2:(tb__ "0|0|
S18S2fLx;SaVS;A1S39S0S32Lv;X18x2").

  Definition fcvt_fty (t : fcvt_ty) : bool := ltac2:(tb__ "0|0|
S48S2fLt;Vt;S32S32S32S32S39S39X48x6").
  Definition fcvt_ity (t : fcvt_ty) : bool := ltac2:(tb__ "0|0|
S48S2fLt;Vt;S39S39S39S39S32S32X48x6").

  Definition sym_step (S : sstate) : step_out := ltac2:(tb__ "0|33|
S8VS;A1S2cS31S47A1S178Lx;S11eVsegs;R1A2S47S3S17aS87R1S5eR3Z4M0A2A2A1LS';S3S178FS';S47S178Li;R2S19eQ5M1A1M2S19eQ14M3A1M4R3S7dVS;R2S9dS1b2Q20M5Q40S1a2G5G3QcM6R1S19fG6Z0M7A2A5M8A3A1A3A1Limm;Lrd;G2G4R3S7dVS;R2S2S63S5eR5S1a1G5G8A2A2S61Z2Z40A2M9A2A1A3A1Limm;Lrd;G2S19eQ15MaA1S17aS87S7dVS;R2S2S63S5eR5G0A2G9A2A1A3S63S5eR5S1a1GaR1A2A2G9A2A2A1Limm;Lrd;G2G2S19eG6A1MbS0S178Lx;S8bSc1VS;R2A2McS198R1A1MdA2MeS2cS63S6bR1S72Z1MfA1A2G9A2S2cS17aS87S7dVS;R5S2S63S5eR8G0A2G9A2A1A3R1A2A1Ttgt;Lt;S2dS17cS191A1M10Li0;S43S0S0G10Lb;La;M11Lop;M12G12S44G11Lop;M13G13S2fS2eS0G10La;Lw;Lsgn;S2dS0S2cG10Lk;Li0;Ll;X0x8Limm;Lrs1;Lrd;S45G2G2S19eQdM14A1Sc1VS;R3A2M15S0G15S0S63S5eR9S1a1G14R3A2A2G9A2S2cS7aS178Lx;S193VS;R7R3R2A4S17aS87VS;R1A2A1S17aS87VS;S5eRaG0A2M16A2A1S192S87Sb7VS;S14R7R3R2A3M17A2R1A2S87Sb7VS;S1dG17A1A2G16A2A2X7ax3Ttpc;Tb;Ta;Limm;Lrs2;Lrs1;Lc;S4eS2fG2G2GbGeS0S177S178Lx;M18S17dVS;R1S18cR6A1R5A4S0S3R9S7dR1R6R2A3A1LS';Lv;S17cS18fA1M19X177x2Tae;Limm;Lrs1;Lrd;Lsgn;Lsz;S4eG2G2GbS8bG15GdA2M1aS0S31S0A1S178Lx;M1bS13VS;A1M1cS0S17cS182A1M1dLs;M1eS31S3A1S178Lx;M1fS180VS;R1S18cR5A1G15A4S3R7R1A1LS';M20G19X31x2X31x2Tae;Limm;Lrs2;Lrs1;Lsz;S43G2G2GbR5S7dVS;R3ScaS7VS;A1M21R4GcS2S63GdG9A2A1M22A4A3A1Limm;Lrs1;Lrd;Lop;S43G2G2S19eQ6M23A1R5S7dVS;R3ScaG21R4GcS2S1a0G23R1A2A1A4A3A1Lsh;Lrs1;Lrd;Lop;S43G2G2G2R5S7dVS;R3S13bG21R4GcSc1VS;R1A2M24A4A3A1Lrs2;Lrs1;Lrd;Lop;G2G2GbR4S7dVS;R3Sc8G21S4bGcG22A4A3A1Limm;Lrs1;Lrd;S43G2G2G2R5S7dVS;R3Sc7R4GcS2S1a0G1R1A2A1A3A3A1Lsh;Lrs1;Lrd;Lop;S43G2G2G2R5S7dVS;R3S13cG21R4GcG24A4A3A1Lrs2;Lrs1;Lrd;Lop;S19eQ4A1M25G25G25G2G2R6VS;A1Lrs1;Lrd;Lsucc;Lpred;Lfm;G2G2GbR4VS;A1Limm;Lrs1;Lrd;S17cS18eA1G1dS44G2G2G2R5S7dVS;R3S137G21R4GcG24A4A3A1Lrs2;Lrs1;Lrd;Lop;S44G2G2G2R5S7dVS;R3S13aG21R4GcG24A4A3A1Lrs2;Lrs1;Lrd;Lop;S4cS2fS2fG2G2G24S0S2fS178L_;M26S3dS183G21R1S186R6A1A3A1G1dG18S17dVS;R1S185R6A1S39A4S0S3R9SfeS7dR1R5R2A3S35S0R3A2A2A1LS';Lv;G19X177x2X2fx2Tae;Lrs1;Lrd;Lrl;Laq;Lwd;S4cS2fS2fG2G2G2GcS0G26S3dS183G21R1S186R7A1A3A1G1dG1bG1cS0G26S4R1R2A2G1fS180SfeVS;S3aS0A1A2R2S185R8A1G15A4S3RaS7dR1R6S2G7A1A3A1LS';G19X31x2G1dX2fx2Le;R8S7dVS;R4S2GfA1A3A1X31x2X2fx2Tae;Lrs2;Lrs1;Lrd;Lrl;Laq;Lwd;S53S4cS2fS2fG2G2G2G1dLrs2;Lrs1;Lrd;Lrl;Laq;Lw;Lop;S4aG2G2GbS18dVS;R4R3S4aS2fLop;M27R4S39S3dS1b0R2A1A1M28G28X4ax3R1A5Lcsr;Lrs1;Lrd;Lop;S4aG2G2GbS18dVS;R4R3G27R4S39S3dS62S1a0G1R2A2G7A2A1M29G29X4ax3R1A5Lcsr;Luimm;Lrd;Lop;S46G2G2GbGeS0S46S178Lfmt;M2aR5G18S17dVS;R1G0S32A4S0S3R8Sa4R1R6S18bR2A1A3A1LS';Lv;G19X177x2G18S17dVS;R1Z8M2bS39A4S0S3R8Sa4R1R6R2A3A1LS';Lv;G19X177x2X46x2Tae;Limm;Lrs1;Lrd;Lfmt;S46G2G2GbG1aS0G1bG1cG1eG1fS180VS;R1S46S2cLfmt;R5G0G2bX46x2Se1VS;R3A2A4G20G19X31x2X31x2Tae;Limm;Lrs2;Lrs1;Lfmt;S56S46G2G2G2G2S19eQ3A1M2cG26S19aVS;R1A2M2dS17eVS;R5A2G1dX2fx2Lrm;Lrs3;Lrs2;Lrs1;Lrd;Lfmt;Lop;S54S46G2G2G2G2cG26G2dS17eVS;R4A2G1dX2fx2Lrm;Lrs2;Lrs1;Lrd;Lfmt;Lop;S46G2G2G2cG26G2dS17eVS;R3A2M2eG1dX2fx2Lrm;Lrs1;Lrd;Lfmt;S58S46G2G2G2G26S195VS;A1M2fG2eG1dX2fx2Lrs2;Lrs1;Lrd;Lfmt;M30Lop;S57G30Lop;S55S46G2G2G2G26G2fS196VS;R3A2G1dX2fx2Lrs2;Lrs1;Lrd;Lfmt;Lop;S48S48G2G2G2cG26S3dG2dA1G1dG26S34S187R5A1S3fS187R4A1M31S188R4A1A2A2
G2eG26S34S188R5A1G31A2S189VS;R3A2G1dX2fx2X2fx2X2fx2Lrm;Lrs1;Lrd;Lsrc;Ldst;S4dS46G2G2S4dS178Ldir;R4G2aR3R5S7dVS;R2S84S39G5Se1VS;R1A2M32A3A3A1R5S7dVS;R2G32A3A1X46x2G2aR3R5Sa4VS;R2S18bS84S32G5G24A3A1A3A1R5Sa4VS;R2G24A3A1X46x2X4dx2Lrs1;Lrd;Lfmt;Ldir;S46G2G2G26G2fS189VS;R2A2G1dX2fx2Lrs1;Lrd;Lfmt;X47x23Tnx;Li;S17cS190A1X31x2Tpc;").

  Record leaf := mkLeaf { lf_state : sstate; lf_reason : stop_reason }.

  Fixpoint memZ (z : Z) (l : list Z) : bool :=
    match l with [] => false | x :: t => (x =? z) || memZ z t end.

  Fixpoint sym_run (fuel : nat) (cuts : list Z) (S : sstate) (first : bool)
    : option (list leaf) :=
    match fuel with
    | O => if first then None else Some [mkLeaf S RsFuel]
    | S fuel' =>
        if negb first && memZ (ss_pc S) cuts then Some [mkLeaf S RsCut]
        else
          match sym_step S with
          | StNext S' => sym_run fuel' cuts S' false
          | StFork S1 S2 =>
              match sym_run fuel' cuts S1 false, sym_run fuel' cuts S2 false with
              | Some l1, Some l2 => Some (l1 ++ l2)
              | _, _ => None
              end
          | StStop r => if first then None else Some [mkLeaf S r]
          end
    end.

End WithImage.
