(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "sobj"; "sstate"; "ss_facts"; "odefault"; "SLit"; "cell"; "tfact"; "ob_dflt"; "ob_cells"; "ob_lo"; "DUnknown"; "ob_base"; "SLBytes"; "SVar"; "mkObj"; "ob_hi"; "ss_objs"; "SAlu"; "SMd"; "SMdW"; "SPBranch"; "ss_lenient"; "ss_pc"; "ss_resv"; "sv_eqb"; "SAluW"; "SExt"; "SPNot"; "c_off"; "c_width"; "dflt_writable"; "mkCell"; "mkSS"; "sprop_eqb"; "ss_fcsr"; "ss_fregs"; "ss_next"; "ss_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast"; "pcache"; "pc_ok"; "cres"; "pc_0"; "pc_sf"; "get_d"; "pc_ud"; "pc_u0"; "force_d"; "pc_d"; "get_x"; "mkPC"; "pc_init"; "pc_x"; "force_x"; "mk_aluw_f_c"; "mk_ext_f_c"; "mk_slt_f_c"; "uleq_r"; "find_obj_c"; "read_cells_c"; "set_ud"; "arr_after_store_c"; "force_ud"; "get_ud"; "lit_cells_c"; "mk_mdw_f_c"; "mk_op_f_c"; "mk_opw_f_c"; "obj_store_c"; "obj_store_d_c"; "prove_sprop_r"; "set_u0"; "small_u_c"; "store_cells_c"; "store_xs_r"; "uleq_c"; "cell_rel_c"; "fld_cached_r"; "narrow_r"; "@Corelib.Init.Datatypes"; "bool"; "prod"; "pair"; "option"; "list"; "nat"; "false"; "Some"; "true"; "None"; "andb"; "negb"; "fst"; "orb"; "app"; "snd"; "cons"; "length"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "step_out"; "load_res"; "fdig"; "decision"; "set_reg"; "leaf"; "cell_read"; "mk_ext"; "DFalse"; "DTrue"; "LROk"; "set_pc"; "crel"; "mk_dig"; "StNext"; "StStop"; "ctx0"; "load_fresh"; "mk_addk"; "set_freg"; "sym_run"; "get_reg"; "havoc_freg"; "mk_alu"; "tf_mentions"; "CDisj"; "CRNone"; "LRFail"; "add_fact"; "addr_aligned"; "amo_k"; "amo_log"; "dg_facts"; "fcvt_fty"; "fcvt_ity"; "find_obj"; "fld_index"; "get_freg"; "havoc_reg"; "itv_lin"; "lin_decomp"; "list_set"; "mk_aluw_f_t"; "mk_ctx"; "mk_ext_f_t"; "mk_nanbox"; "mk_slt_f_t"; "msz"; "same_atoms"; "set_resv"; "small_u_t"; "stop_reason"; "sub_fold"; "sym_csr"; "sym_step"; "uleq"; "CLit"; "CUnk"; "M64"; "RsEcall"; "RsMem"; "RsNoCode"; "RsSymJump"; "RsUnsupported"; "StFork"; "all_ro"; "arr_after_store"; "arr_cells"; "cell_rel"; "decide_branch"; "dg_with_pool"; "fact_lookup"; "find_obj_d"; "fld_cached"; "fld_vars"; "flds_apart"; "fresh"; "frm0b"; "havoc_reg_b"; "image_bytes"; "image_load"; "immI"; "instr_at"; "itv_decide_t"; "lf_state"; "lit_cells"; "lit_fold_t"; "lit_of"; "load_arr"; "load_dflt"; "mk_alu_f"; "mk_aluw"; "mk_aluw_f"; "mk_aluw_s"; "mk_ext_f"; "mk_ext_s"; "mk_md"; "mk_md_f"; "mk_mdw"; "mk_mdw_f"; "mk_op_f"; "mk_opw_f"; "mk_slt_f"; "narrow"; "obj_store"; "obj_store_d"; "prove_sprop"; "read_cells"; "rm_ok"; "ro_load"; "ro_span"; "ro_span_max"; "same_base_eq"; "set_objs"; "slt_retry"; "small_u"; "store_cells"; "store_xs"; "sym_load"; "sym_store"; "tf_inst"; "tile_cells"; "tmpl_inst"; "@Corelib.Init.Logic"; "eq"; "and"; "True"; "ex"; "or"; "@LinuxProcessSemantics.Riscv.Instr"; "aluop"; "mulop"; "ffmt"; "branch_cond"; "csrop"; "ALU_SUB"; "instr"; "awidth"; "fmvdir"; "fcvt_ty"; "msize"; "ALU_ADD"; "ALU_SRL"; "M_MUL"; "amoop"; "fariop"; "fcmpop";
"fmaop"; "fminmaxop"; "fsgnop"; "@Stdlib.ZArith.BinInt.Z"; "add"; "modulo"; "leb"; "pow"; "mul"; "to_N"; "to_nat"; "ltb"; "opp"; "eqb"; "land"; "lnot"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymQFast"; "u2memo"; "u2_ok"; "uleq_d_o"; "mk_u2"; "sitv_d_q"; "find_obj_d_m"; "decide_t_q"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_signed"; "bv_unsigned"; "bv_concat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.WithImage"; "cleaf"; "sym_load_c"; "lcres"; "sym_store_c"; "load_arr_c"; "load_dflt_c"; "lr_keeps"; "cleaf_ok"; "decide_branch_c"; "load_image"; "omap_fst"; "reinit"; "ro_span_r"; "step_ok"; "sym_run_c"; "sym_run_cl"; "sym_run_lc"; "sym_step_c"; "lres_ok"; "oall_ok"; "sres_ok"; "sym_run_fast"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymDigFast"; "sf_ok"; "mk_ctx_x"; "mk_dig_x"; "mk_pool_x"; "sfilter"; "snorm_h"; "@Corelib.Init.Nat"; "add"; "@Stdlib.NArith.BinNat.N"; "mul"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@Stdlib.Lists.List"; "existsb"; "forallb"; "nth_error"; "@Stdlib.PArith.BinPos.Pos"; "of_nat"; "to_nat"; "@LinuxProcessSemantics.Riscv.Prelude"; "sext"; "@LinuxProcessSemantics.Riscv.Sem"; "branch_taken"; "is_x0"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool.
From Stdlib Require Import PArith PeanoNat.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymDigFast SymQFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Record pcache := mkPC {
  pc_0  : fdig;
  pc_sf : list sprop;
  pc_x  : option fdig;
  pc_d  : option fdig;
  pc_u0 : option u2memo;
  pc_ud : option u2memo }.

Definition pc_init (facts : list sprop) : pcache := ltac2:(tb__ "0|2|
S33S75Vfacts;A1S12cVfacts;A1S59S67A1M0G0S59S106A1M1G1A6").

Definition get_x (pc : pcache) (facts : list sprop) : fdig := ltac2:(tb__ "0|0|
S53S67A1S67Lx;S35Vpc;A1S67R1Ld;S129Vfacts;A1X53x2").
Definition get_d (pc : pcache) (facts : list sprop) : fdig := ltac2:(tb__ "0|0|
S53S67A1S67Lx;S31Vpc;A1S67R1Ld;S12aVfacts;A1X53x2").

Definition force_x (pc : pcache) (facts : list sprop) : pcache := ltac2:(tb__ "0|0|
S53S67A1S28Lx;S35Vpc;A1S67Vpc;Lf;S33S2bVpc;A1S2cVpc;A1S57S67S129Vfacts;A1A2S31Vpc;A1S2fVpc;A1S2eVpc;A1A6X53x2").
Definition force_d (pc : pcache) (facts : list sprop) : pcache := ltac2:(tb__ "0|0|
S53S67A1S28Lx;S31Vpc;A1S67Vpc;Lf;S32Vpc;Vfacts;A2S67S33S2bVpc;A1S2cVpc;A1S57S67R1A2S57S67SabR1S12bR1A1A2A2S2fVpc;A1S2eVpc;A1A6Tx;X53x2").

Definition set_u0 (pc : pcache) (ou : option u2memo) : pcache := ltac2:(tb__ "0|0|
S33S2bVpc;A1S2cVpc;A1S35Vpc;A1S31Vpc;A1Vou;S2eVpc;A1A6").
Definition set_ud (pc : pcache) (ou : option u2memo) : pcache := ltac2:(tb__ "0|0|
S33S2bVpc;A1S2cVpc;A1S35Vpc;A1S31Vpc;A1S2fVpc;A1Vou;A6").

Definition pc_ok (pc : pcache) (facts : list sprop) : Prop := ltac2:(tb__ "0|6|
Se1Se0S67S2bVpc;A1S75Vfacts;A1M0A3Se1Se4Se0S53S67A1M1S35Vpc;A1M2S59S67A1M3A3Se0G1G2S57S67S90Vfacts;A1A2A3A2Se1Se4Se0G1S31Vpc;A1M4G3A3Se0G1G4S57S67S72Vfacts;A1M5A2A3A2Se1S128S2cVpc;A1Vfacts;A2Se1S107S2fVpc;A1G0A2S107S2eVpc;A1G5A2A2A2A2A2A2").

Lemma pc_init_ok : ltac2:(tb__ "0|0|
S54S1A1S29S34R1A1R1A2Ffacts;").
Proof.
  intros facts. split; [reflexivity|]. split; [left; reflexivity|]. split; [left; reflexivity|].
  split; [apply sfilter_ok|]. split; left; reflexivity.
Qed.

Lemma pc_0_ok : ltac2:(tb__ "0|0|
S28S54S1A1S29R2R1A2Se0S67S2bR3A1S75R2A1A3F_;Ffacts;Fpc;").
Proof. intros pc facts H. exact (proj1 H). Qed.

Lemma pc_sf_ok : ltac2:(tb__ "0|0|
S28S54S1A1S29R2R1A2S128S2cR3A1R2A2F_;Ffacts;Fpc;").
Proof. intros pc facts (_ & _ & _ & H & _). exact H. Qed.
Lemma pc_u0_ok : ltac2:(tb__ "0|0|
S28S54S1A1S29R2R1A2S107S2fR3A1S75R2A1A2F_;Ffacts;Fpc;").
Proof. intros pc facts (_ & _ & _ & _ & H & _). exact H. Qed.
Lemma pc_ud_ok : ltac2:(tb__ "0|0|
S28S54S1A1S29R2R1A2S107S2eR3A1S72R2A1A2F_;Ffacts;Fpc;").
Proof. intros pc facts (_ & _ & _ & _ & _ & H). exact H. Qed.

Lemma get_x_ok : ltac2:(tb__ "0|0|
S28S54S1A1S29R2R1A2Se0S67S32R3R2A2S90R2A1A3F_;Ffacts;Fpc;").
Proof.
  intros pc facts (_ & [Hx|Hx] & _); unfold get_x; rewrite Hx; [apply mk_ctx_x_eq | reflexivity].
Qed.

Lemma get_d_ok : ltac2:(tb__ "0|0|
S28S54S1A1S29R2R1A2Se0S67S2dR3R2A2S72R2A1A3F_;Ffacts;Fpc;").
Proof.
  intros pc facts (_ & _ & [Hd|Hd] & _); unfold get_d; rewrite Hd; [apply mk_dig_x_eq | reflexivity].
Qed.

Lemma force_x_ok : ltac2:(tb__ "0|0|
S28S54S1A1S29R2R1A2S29S36R3R2A2R2A2F_;Ffacts;Fpc;").
Proof.
  intros pc facts H. unfold force_x. destruct (pc_x pc) as [d|] eqn:E; [exact H|].
  destruct H as (H0 & _ & Hd & Hs & Hu0 & Hud). split; [exact H0|].
  split; [right; cbn [pc_x]; rewrite mk_ctx_x_eq; reflexivity|].
  split; [exact Hd|]. split; [exact Hs|]. split; [exact Hu0 | exact Hud].
Qed.

Lemma force_d_ok : ltac2:(tb__ "0|0|
S28S54S1A1S29R2R1A2S29S30R3R2A2R2A2F_;Ffacts;Fpc;").
Proof.
  intros pc facts H. unfold force_d. destruct (pc_d pc) as [d|] eqn:E; [exact H|].
  cbv zeta. rewrite mk_pool_x_eq. rewrite (get_x_ok _ _ H). destruct H as (H0 & _ & _ & Hs & Hu0 & Hud).
  split; [exact H0|]. split; [right; reflexivity|]. split; [right; reflexivity|].
  split; [exact Hs|]. split; [exact Hu0 | exact Hud].
Qed.

Lemma set_u0_ok : ltac2:(tb__ "0|0|
S28S54S1A1S53S106A1S29R3R2A2S107R2S75R3A1A2S29S48R5R3A2R4A2F_;F_;Fou;Ffacts;Fpc;").
Proof.
  intros pc facts ou (H0 & Hx & Hd & Hs & _ & Hud) Hou.
  split; [exact H0|]. split; [exact Hx|]. split; [exact Hd|]. split; [exact Hs|]. split; [exact Hou | exact Hud].
Qed.

Lemma set_ud_ok : ltac2:(tb__ "0|0|
S28S54S1A1S53S106A1S29R3R2A2S107R2S72R3A1A2S29S3dR5R3A2R4A2F_;F_;Fou;Ffacts;Fpc;").
Proof.
  intros pc facts ou (H0 & Hx & Hd & Hs & Hu0 & _) Hou.
  split; [exact H0|]. split; [exact Hx|]. split; [exact Hd|]. split; [exact Hs|]. split; [exact Hu0 | exact Hou].
Qed.

Definition force_ud (pc : pcache) (facts : list sprop) : pcache := ltac2:(tb__ "0|0|
S30Vpc;Vfacts;A2S28S53S106A1S28Lx;S2eR1A1S106R2Lu;S3dR1S57S106S109S2dR1Vfacts;A2A1A2A2X53x2Tpc1;").
Definition get_ud (pc : pcache) (facts : list sprop) : u2memo := ltac2:(tb__ "0|0|
S53S106A1S106Lx;S2eVpc;A1S106R1Lu;S109S2dVpc;Vfacts;A2A1X53x2").

Lemma force_ud_ok : ltac2:(tb__ "0|0|
S28S54S1A1S29R2R1A2S29S3fR3R2A2R2A2F_;Ffacts;Fpc;").
Proof.
  intros pc facts H. unfold force_ud. cbv zeta. pose proof (force_d_ok _ _ H) as H1.
  destruct (pc_ud (force_d pc facts)); [exact H1|].
  apply set_ud_ok; [exact H1|]. right. rewrite (get_d_ok _ _ H1). reflexivity.
Qed.

Lemma get_ud_ok : ltac2:(tb__ "0|0|
S28S54S1A1S29R2R1A2Se0S106S40R3R2A2S109S72R2A1A1A3F_;Ffacts;Fpc;").
Proof.
  intros pc facts H. unfold get_ud. destruct (pc_ud_ok _ _ H) as [E|E]; rewrite E; [|reflexivity].
  rewrite (get_d_ok _ _ H). reflexivity.
Qed.

Lemma pc_sf_ok_0 : ltac2:(tb__ "0|0|
S28S54S1A1S29R2R1A2S128S2cR3A1S85S2bR3A1A1A2F_;Ffacts;Fpc;").
Proof. intros pc facts H. rewrite (pc_0_ok _ _ H). exact (pc_sf_ok _ _ H). Qed.
Lemma pc_sf_ok_d : ltac2:(tb__ "0|0|
S28S54S1A1S29R2R1A2S128S2cR3A1S85S72R2A1A1A2F_;Ffacts;Fpc;").
Proof. intros pc facts H. rewrite dg_facts_mk_dig. exact (pc_sf_ok _ _ H). Qed.

Definition cres {A} (facts : list sprop) (r : A * pcache) (orig : A) : Prop :=
  exists pc', r = (orig, pc') /\ pc_ok pc' facts.

Lemma cres_ret : forall {A} facts (a : A) pc, pc_ok pc facts -> cres facts (a, pc) a.
Proof. intros A facts a pc H. exists pc. split; [reflexivity | exact H]. Qed.

Definition small_u_c (pc : pcache) (facts : list sprop) (e : sv) (w : Z) : bool * pcache := ltac2:(tb__ "0|0|
S50S51S50S28A2L_;S97S2bVpc;A1Ve;Vw;A3S52S50S28S58Vpc;A4S36Vpc;Vfacts;A2S28S52S50S28S97S32R1Vfacts;A2Ve;Vw;A3R1A4Tpc1;X50x2").

Lemma small_u_c_ok : ltac2:(tb__ "0|0|
S28S54S1A1S0S62S29R4R3A2S2aS50R4S49R5R4R3R2A4Sd8R4R3R2A3A4F_;Fw;Fe;Ffacts;Fpc;").
Proof.
  intros pc facts e w H. unfold small_u_c, small_u. rewrite (pc_0_ok _ _ H).
  destruct (small_u_t (ctx0 facts) e w); [apply cres_ret; exact H|].
  cbv zeta. rewrite (get_x_ok _ _ (force_x_ok _ _ H)). apply cres_ret. apply force_x_ok; exact H.
Qed.

Definition mk_ext_f_c (pc : pcache) (facts : list sprop) (sgn : bool) (w : N) (a : sv) : sv * pcache := ltac2:(tb__ "0|7|
S0S51S0S28A2Lx;S91S2bVpc;A1Vsgn;Vw;Va;A4S62S52S0S28S6R1A1M0Vpc;A4Lz;S63S52S0S28SfR1A1M1Vpc;A4Li;Se5S0S0S52S0S28S13R3R2R1A3M2Vpc;A4Lb;La0;Lop;Se5S0S0S52S0S28S1bR3R2R1A3M3Vpc;A4Lb;La0;Lop;Se6S0S0S52S0S28S14R3R2R1A3M4Vpc;A4Lb;La0;Lop;Se6S0S0S52S0S28S15R3R2R1A3M5Vpc;A4Lb;La0;Lop;S50S64S0S36Vpc;Vfacts;A2S28S32R1Vfacts;A2S67S52S0S28S0S0Lx;S91R1Vsgn;Vw;Va;A4S62G0Lz;S63G1Li;Se5S0S0G2Lb;La0;Lop;Se5S0S0G3Lb;La0;Lop;Se6S0S0G4Lb;La0;Lop;Se6S0S0G5Lb;La0;Lop;S50S64S0Sc4R4Vsgn;Vw;Va;A4La0;Lw0;Lsgn0;S63S0S62SeR3R2R1A3M6Lk;Li;Ll;X0x8R2A4Tx;Tpc1;La0;Lw0;Lsgn0;S63S0S62S52S0S28G6Vpc;A4Lk;Li;Ll;X0x8").

Lemma mk_ext_f_c_ok : ltac2:(tb__ "0|0|
S28S54S1A1S50S64S0S29R5R4A2S2aS0R5S38R6R5R4R3R2A5Sc3R5R4R3R2A4A4F_;Fa;Fw;Fsgn;Ffacts;Fpc;").
Proof.
  intros pc facts sgn w a H. unfold mk_ext_f_c, mk_ext_f. rewrite (pc_0_ok _ _ H).
  destruct (mk_ext_f_t (ctx0 facts) sgn w a); try (apply cres_ret; exact H).
  cbv zeta. rewrite (get_x_ok _ _ (force_x_ok _ _ H)). apply cres_ret. apply force_x_ok; exact H.
Qed.

Definition mk_aluw_f_c (pc : pcache) (facts : list sprop) (op : aluop) (a b : sv) : sv * pcache := ltac2:(tb__ "0|7|
S0S51S0S28A2Lx;S8fS2bVpc;A1Vop;Va;Vb;A4S62S52S0S28S6R1A1M0Vpc;A4Lz;S63S52S0S28SfR1A1M1Vpc;A4Li;Se5S0S0S52S0S28S13R3R2R1A3M2Vpc;A4Lb0;La0;Lop0;Se5S0S0S36Vpc;Vfacts;A2S28S32R1Vfacts;A2S67S52S0S28S0S0Lx;S8fR1Vop;Va;Vb;A4S62G0Lz;S63G1Li;Se5S0S0G2Lb0;La0;Lop0;Se5S0S0Sc2R4Vop;Va;Vb;A4Lb0;La0;Lop0;Se6S0S0S14R3R2R1A3M3Lb0;La0;Lop0;Se6S0S0S15R3R2R1A3M4Lb0;La0;Lop0;S50S64S0S1cR3R2R1A3M5La0;Lw;Lsgn;S63S0S62SeR3R2R1A3M6Lk;Li;Ll;X0x8R2A4Tx;Tpc1;Lb0;La0;Lop0;Se6S0S0S52S0S28G3Vpc;A4Lb0;La0;Lop0;Se6S0S0S52S0S28G4Vpc;A4Lb0;La0;Lop0;S50S64S0S52S0S28G5Vpc;A4La0;Lw;Lsgn;S63S0S62S52S0S28G6Vpc;A4Lk;Li;Ll;X0x8").

Lemma mk_aluw_f_c_ok : ltac2:(tb__ "0|0|
S28S54S1A1Se5S0S0S29R5R4A2S2aS0R5S37R6R5R4R3R2A5Sc1R5R4R3R2A4A4F_;Fb;Fa;Fop;Ffacts;Fpc;").
Proof.
  intros pc facts op a b H. unfold mk_aluw_f_c, mk_aluw_f. rewrite (pc_0_ok _ _ H).
  destruct (mk_aluw_f_t (ctx0 facts) op a b); try (apply cres_ret; exact H).
  cbv zeta. rewrite (get_x_ok _ _ (force_x_ok _ _ H)). apply cres_ret. apply force_x_ok; exact H.
Qed.

Definition mk_slt_f_c (pc : pcache) (facts : list sprop) (op : aluop) (a b : sv) : sv * pcache := ltac2:(tb__ "0|0|
S93S2bVpc;A1Vop;Va;Vb;A4S0S50S51S0S28A2L_;Sd7R1A1S30Vpc;Vfacts;A2S28S52S0S28S93S2dR1Vfacts;A2Vop;Va;Vb;A4R1A4Tpc1;S52S0S28R1Vpc;A4X50x2Tr;").

Lemma mk_slt_f_c_ok : ltac2:(tb__ "0|0|
S28S54S1A1Se5S0S0S29R5R4A2S2aS0R5S39R6R5R4R3R2A5ScbR5R4R3R2A4A4F_;Fb;Fa;Fop;Ffacts;Fpc;").
Proof.
  intros pc facts op a b H. unfold mk_slt_f_c, mk_slt_f. rewrite (pc_0_ok _ _ H). cbv zeta.
  destruct (slt_retry (mk_slt_f_t (ctx0 facts) op a b)); [|apply cres_ret; exact H].
  rewrite (get_d_ok _ _ (force_d_ok _ _ H)). apply cres_ret. apply force_d_ok; exact H.
Qed.

Definition mk_op_f_c (pc : pcache) (facts : list sprop) (op : aluop) (a b : sv) : sv * pcache := ltac2:(tb__ "0|2|
Se5S51S0S28A2M0Lop;Vop;S39Vpc;Vfacts;Vop;Va;Vb;A5M1S53S0A1G0Lx;S99Va;Vb;A2S0S52S0S28SbbS2bVpc;A1R1A2Vpc;A4Loff;G1X53x2G1G1G1G1G1G1G1G1Xe5xa").

Lemma mk_op_f_c_ok : ltac2:(tb__ "0|0|
S28S54S1A1Se5S0S0S29R5R4A2S2aS0R5S43R6R5R4R3R2A5Sc9R5R4R3R2A4A4F_;Fb;Fa;Fop;Ffacts;Fpc;").
Proof.
  intros pc facts op a b H. unfold mk_op_f_c, mk_op_f.
  destruct op; try (apply mk_slt_f_c_ok; exact H).
  destruct (sub_fold a b); [|apply mk_slt_f_c_ok; exact H].
  rewrite (pc_0_ok _ _ H). apply cres_ret; exact H.
Qed.

Definition mk_opw_f_c (pc : pcache) (facts : list sprop) (op : aluop) (a b : sv) : sv * pcache := ltac2:(tb__ "0|2|
Se5S51S0S28A2M0Lop;Vop;S37Vpc;Vfacts;Vop;Va;Vb;A5M1S53S0A1G0Lx;S99Va;Vb;A2S0S37Vpc;Vfacts;SeaR1S6Z0A1A5Loff;G1X53x2G1G1G1G1G1G1G1G1Xe5xa").

Lemma mk_opw_f_c_ok : ltac2:(tb__ "0|0|
S28S54S1A1Se5S0S0S29R5R4A2S2aS0R5S44R6R5R4R3R2A5ScaR5R4R3R2A4A4F_;Fb;Fa;Fop;Ffacts;Fpc;").
Proof.
  intros pc facts op a b H. unfold mk_opw_f_c, mk_opw_f.
  destruct op; try (apply mk_aluw_f_c_ok; exact H).
  destruct (sub_fold a b); apply mk_aluw_f_c_ok; exact H.
Qed.

Definition mk_mdw_f_c (pc : pcache) (facts : list sprop) (op : mulop) (a b : sv) : sv * pcache := ltac2:(tb__ "0|3|
Se6S51S0S28A2M0Lop;Vop;Sc5Sf2Va;Vb;A3S0S51S50S28A2G0Lx;S49Vpc;Vfacts;R1Z1fA4S50S28S52S0S28S50S0Ls;R2R3Sc7Vop;Va;Vb;A3M1X50x2R1A4Lpc1;Ls;X51x1Tr;S52S0S28G1Vpc;A4M2G2G2G2G2G2G2Xe6x8").

Lemma mk_mdw_f_c_ok : ltac2:(tb__ "0|0|
S28S54S1A1Se6S0S0S29R5R4A2S2aS0R5S42R6R5R4R3R2A5Sc8R5R4R3R2A4A4F_;Fb;Fa;Fop;Ffacts;Fpc;").
Proof.
  intros pc facts op a b H. unfold mk_mdw_f_c, mk_mdw_f.
  destruct op; try (apply cres_ret; exact H).
  cbv zeta. destruct (small_u_c_ok pc facts (mk_md M_MUL a b) 31 H) as (pc1 & -> & H1).
  apply cres_ret; exact H1.
Qed.

Definition uleq_c (pc : pcache) (facts : list sprop) (a : sv) (k : Z) (b : sv) : bool * pcache := ltac2:(tb__ "0|0|
S50S51S50S28A2L_;S108S2fVpc;A1S2bVpc;A1Va;Vk;Vb;A5S52S50S28S58Vpc;A4S30Vpc;Vfacts;A2S28S52S50S28S108S2eR1A1S2dR1Vfacts;A2Va;Vk;Vb;A5R1A4Tpc1;X50x2").

Lemma uleq_c_ok : ltac2:(tb__ "0|0|
S28S54S1A1S0S62S0S29R5R4A2S2aS50R5S4cR6R5R4R3R2A5S9cR5R4R3R2A4A4F_;Fb;Fk;Fa;Ffacts;Fpc;").
Proof.
  intros pc facts a k b H. unfold uleq_c, uleq.
  rewrite (pc_0_ok _ _ H), (uleq_d_o_eq _ _ a k b (pc_u0_ok _ _ H)).
  destruct (uleq_d (ctx0 facts) a k b); [apply cres_ret; exact H|].
  cbv zeta. pose proof (force_d_ok _ _ H) as H1.
  rewrite (get_d_ok _ _ H1), (uleq_d_o_eq _ _ a k b (pc_ud_ok _ _ H1)). apply cres_ret. exact H1.
Qed.

Definition uleq_r (pc : pcache) (facts : list sprop) (a : sv) (k : Z) (b : sv) : bool := ltac2:(tb__ "0|0|
S50S50L_;S108S2fVpc;A1S2bVpc;A1Va;Vk;Vb;A5S58S108S2eVpc;A1S2dVpc;Vfacts;A2Va;Vk;Vb;A5X50x2").

Lemma uleq_r_ok : ltac2:(tb__ "0|0|
S28S54S1A1S0S62S0S29R5R4A2Se0S50S3aR6R5R4R3R2A5S9cR5R4R3R2A4A3F_;Fb;Fk;Fa;Ffacts;Fpc;").
Proof.
  intros pc facts a k b H. unfold uleq_r, uleq.
  rewrite (pc_0_ok _ _ H), (get_d_ok _ _ H), (uleq_d_o_eq _ _ a k b (pc_u0_ok _ _ H)), (uleq_d_o_eq _ _ a k b (pc_ud_ok _ _ H)).
  reflexivity.
Qed.

Definition find_obj_c (pc : pcache) (objs : list sobj) (facts : list sprop) (ae : sv) (k : Z) (n : nat)
  : option (nat * sobj * sv) * pcache := ltac2:(tb__ "0|5|
S51S53S51S51S55S2A2S0A2M0A1M1S53S106A1M2A2S51G1S28A2M3Lx;M4S10bS2cVpc;A1S2fVpc;A1Vobjs;S2bVpc;A1Vae;Vk;Vn;A7G1G2S48Vpc;R1A2S28G1G3Lr0;R3G0S52G1S28S57G0R1A2R2A4Lr;S30R1Vfacts;A2S28G4S10bS2cR1A1S2eR1A1Vobjs;S2dR1Vfacts;A2Vae;Vk;Vn;A7G1G2S52G1S28R2S3dR3R1A2A4Lud;Lr1;X51x1Tpc1;X53x2Tpc0;Lu0;Lr0;X51x1").

Lemma find_obj_c_ok : ltac2:(tb__ "0|0|
S28S54S2A1S54S1A1S0S62S55S29R6R4A2S2aS53S51S51S55S2A2S0A2A1R5S3bR7R6R5R4R3R2A6S88R6R5R4R3R2A5A4F_;Fn;Fk;Fae;Ffacts;Fobjs;Fpc;").
Proof.
  intros pc objs facts ae k n H. unfold find_obj_c, find_obj.
  destruct (find_obj_d_m_ok (pc_sf pc) (pc_0 pc) ae k (pc_sf_ok_0 _ _ H) objs (pc_u0 pc) n)
    as (u0 & -> & Hu0); [rewrite (pc_0_ok _ _ H); exact (pc_u0_ok _ _ H)|].
  rewrite (pc_0_ok _ _ H) in Hu0 |- *.
  pose proof (set_u0_ok pc facts u0 H Hu0) as H0.
  destruct (find_obj_d objs (ctx0 facts) ae k n); [apply cres_ret; exact H0|].
  cbv zeta. pose proof (force_d_ok _ _ H0) as H1. rewrite (get_d_ok _ _ H1).
  destruct (find_obj_d_m_ok (pc_sf (force_d (set_u0 pc u0) facts)) (mk_dig facts) ae k (pc_sf_ok_d _ _ H1) objs
              (pc_ud (force_d (set_u0 pc u0) facts)) n (pc_ud_ok _ _ H1)) as (ud & -> & Hud).
  apply cres_ret. apply set_ud_ok; assumption.
Qed.

Definition cell_rel_c (pc : pcache) (facts : list sprop) (off : sv) (k : Z) (c : cell) : crel * pcache := ltac2:(tb__ "0|7|
S53S62A1S51S71S28A2Lx;S95S1eVc;A1M0Voff;A2S62S52S71S28S9dS12dR1A1A1Vpc;A4Ld;S30Vpc;Vfacts;A2S28S2dR1Vfacts;A2S67S2cR2A1S54S1A1S53S51S62S62A2M1A1S50Lx;M2S10aR1R2Voff;A3G1G1S50Lp;M3R1S62S62G2S10aR4R5G0A3G1G1S50Lp0;R1S62S62S5dSfbSf9R4Vk;A2R2A2SfbSf9R1S1fVc;A1M4A2R5A2A2Lh2;Ll2;X51x1Lp0;S56X53x2Lh1;Ll1;X51x1Lp;S56X53x2S50S0G2S10aR3R4R1A3G1G3R1S62S62SfbZ0R2A2Lz;Ll;X51x1Lp;S56X53x2Le;S0S50Fe;S52S71S28S50S71Lby_itv;R2S7eS50S71L_;S50S50L_;M5S5aR1Voff;A1R1G0A1A2G5S108S2eR5A1M6R4Voff;Vk;G0A5S58S108G6R4G0G4Voff;A5X50x2S56X50x2S7eS9eX50x2X50x2R5A4Tnonneg;Tby_itv;Tsf;Tdg;Tpc1;X53x2").

Lemma cell_rel_c_ok : ltac2:(tb__ "0|0|
S28S54S1A1S0S62S7S29R5R4A2S2aS71R5S4dR6R5R4R3R2A5Sa9R5R4R3R2A4A4F_;Fc;Fk;Foff;Ffacts;Fpc;").
Proof.
  intros pc facts off k c H. unfold cell_rel_c, cell_rel.
  destruct (same_atoms (c_off c) off); [rewrite snorm_h_eq; apply cres_ret; exact H|].
  cbv zeta. pose proof (force_d_ok _ _ H) as H1. rewrite (get_d_ok _ _ H1).
  rewrite !(sitv_d_q_eq _ _ _ (pc_sf_ok_d _ _ H1)), !(uleq_d_o_eq _ _ _ _ _ (pc_ud_ok _ _ H1)).
  apply cres_ret. exact H1.
Qed.

Fixpoint read_cells_c (pc : pcache) (facts : list sprop) (cells : list cell) (off : sv) (k : Z) (acc : cell_read)
  : cell_read * pcache :=
  match cells with
  | [] => (acc, pc)
  | c :: rest =>
      let '(r, pc1) := cell_rel_c pc facts off k c in
      match r with
      | CLit d =>
          if lit_overlaps d (c_width c) k then
            if (d =? 0) && (c_width c =? k) then (CRExact (c_val c), pc1)
            else if (d <=? 0) && (k <=? d + c_width c) then (CRInside (c_val c) (- d), pc1)
            else read_cells_c pc1 facts rest off k (match acc with CRUnknown => CRUnknown | _ => CRTile end)
          else read_cells_c pc1 facts rest off k acc
      | CDisj => read_cells_c pc1 facts rest off k acc
      | CUnk => read_cells_c pc1 facts rest off k CRUnknown
      end
  end.

Lemma read_cells_c_ok : ltac2:(tb__ "0|0|
S54S1A1S0S62S54S7A1S28S6bS29R2R6A2S2aS6bR7S3cR3R7R4R6R5R2A6Sd0R7R4R6R5R2A5A4F_;Facc;Fpc;Fcells;Fk;Foff;Ffacts;").
Proof.
  intros facts off k. induction cells as [|c rest IH]; intros pc acc H; cbn [read_cells_c read_cells].
  - apply cres_ret; exact H.
  - destruct (cell_rel_c_ok pc facts off k c H) as (pc1 & -> & H1).
    destruct (cell_rel facts off k c) as [d| |].
    + destruct (lit_overlaps d (c_width c) k); [|apply IH; exact H1].
      destruct ((d =? 0) && (c_width c =? k)); [apply cres_ret; exact H1|].
      destruct ((d <=? 0) && (k <=? d + c_width c)); [apply cres_ret; exact H1|].
      apply IH; exact H1.
    + apply IH; exact H1.
    + apply IH; exact H1.
Qed.

Fixpoint lit_cells_c (pc : pcache) (facts : list sprop) (cells : list cell) (off : sv) (k : Z)
  : list (Z * Z * sv) * pcache :=
  match cells with
  | [] => ([], pc)
  | c :: rest =>
      let '(r, pc1) := cell_rel_c pc facts off k c in
      match r with
      | CLit d => let '(l, pc2) := lit_cells_c pc1 facts rest off k in ((d, c_width c, c_val c) :: l, pc2)
      | _ => lit_cells_c pc1 facts rest off k
      end
  end.

Lemma lit_cells_c_ok : ltac2:(tb__ "0|0|
S54S1A1S0S62S54S7A1S28S29R1R5A2S2aS54S51S51S62S62A2S0A2A1R6S41R2R6R3R5R4A5SbaR6R3R5R4A4A4F_;Fpc;Fcells;Fk;Foff;Ffacts;").
Proof.
  intros facts off k. induction cells as [|c rest IH]; intros pc H; cbn [lit_cells_c lit_cells].
  - apply cres_ret; exact H.
  - destruct (cell_rel_c_ok pc facts off k c H) as (pc1 & -> & H1).
    destruct (cell_rel facts off k c) as [d| |]; try (apply IH; exact H1).
    destruct (IH pc1 H1) as (pc2 & -> & H2). apply cres_ret; exact H2.
Qed.

Fixpoint store_cells_c (pc : pcache) (facts : list sprop) (cells : list cell) (off : sv) (k : Z)
  : (list cell * bool) * pcache :=
  match cells with
  | [] => (([], false), pc)
  | c :: rest =>
      let '((rest', taint), pc1) := store_cells_c pc facts rest off k in
      let '(r, pc2) := cell_rel_c pc1 facts off k c in
      (match r with
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
       end, pc2)
  end.

Lemma store_cells_c_ok : ltac2:(tb__ "0|1|
S54S1A1S0S62S54S7A1M0S28S29R1R5A2S2aS51G0S50A2R6S4aR2R6R3R5R4A5Sd9R6R3R5R4A4A4F_;Fpc;Fcells;Fk;Foff;Ffacts;").
Proof.
  intros facts off k. induction cells as [|c rest IH]; intros pc H; cbn [store_cells_c store_cells].
  - apply cres_ret; exact H.
  - destruct (IH pc H) as (pc1 & -> & H1).
    destruct (store_cells facts rest off k) as [rest' taint].
    destruct (cell_rel_c_ok pc1 facts off k c H1) as (pc2 & -> & H2).
    apply cres_ret; exact H2.
Qed.

Definition obj_store_c (pc : pcache) (facts : list sprop) (o : sobj) (off : sv) (k : Z) (v : sv) : sobj * pcache := ltac2:(tb__ "0|3|
S51S51S54S7A1M0S50A2M1S28A2S51S2S28A2M2Lx;S4aVpc;Vfacts;SaVo;A1Voff;Vk;A5G1S28G1G2Lp;R2G0S50S52S2S28S10SdVo;A1SbVo;A1S11Vo;A1S60S7S21Voff;Vk;Vv;A3R2A3S50S5Ltaint;R1ScS9Vo;A1X50x2A5R3A4Ltaint;Lcells';X51x1Lpc1;Lp;X51x1").

Lemma obj_store_c_ok : ltac2:(tb__ "0|0|
S28S54S1A1S2S0S62S0S29R6R5A2S2aS2R6S45R7R6R5R4R3R2A6ScdR6R5R4R3R2A5A4F_;Fv;Fk;Foff;Fo;Ffacts;Fpc;").
Proof.
  intros pc facts o off k v H. unfold obj_store_c, obj_store.
  destruct (store_cells_c_ok facts off k (ob_cells o) pc H) as (pc1 & -> & H1).
  destruct (store_cells facts (ob_cells o) off k) as [cells' taint].
  apply cres_ret; exact H1.
Qed.

Definition narrow_r (pc : pcache) (facts : list sprop) (k : Z) (v : sv) : sv := ltac2:(tb__ "0|0|
S51S62S62A2S0Lx;S8cS2dVpc;Vfacts;A2Vv;A2S62S62S50S0L_;S5aSfbR2R1A2S100R1SfcZ2SfdZ8Vk;A2A2A2A2Vv;S6cS56S12fQ8SfeVk;A1A2Vv;A3X50x2Lh;Ll;X51x1").

Lemma narrow_r_ok : ltac2:(tb__ "0|0|
S28S54S1A1S62S0S29R4R3A2Se0S0S4fR5R4R3R2A4SccR4R3R2A3A3F_;Fv;Fk;Ffacts;Fpc;").
Proof. intros pc facts k v H. unfold narrow_r, narrow, itv. rewrite (get_d_ok _ _ H). reflexivity. Qed.

Definition prove_sprop_r (pc : pcache) (facts : list sprop) (p : sprop) : bool := ltac2:(tb__ "0|1|
S5dS132S1S23Vp;A1Vfacts;A3S1S50Lp;Vp;Se8S0S0S56Lb;La;M0Lc;S1S56Lp0;S0S0S3aVpc;Vfacts;R2Z1R1A5Lb;La;S0S0S3aVpc;Vfacts;R2Z0R1A5Lb;La;G0S56S63S62S56La;Li;X1x7A2").

Lemma prove_sprop_r_ok : ltac2:(tb__ "0|0|
S28S54S1A1S1S29R3R2A2Se0S50S47R4R3R2A3ScfR3R2A2A3F_;Fp;Ffacts;Fpc;").
Proof.
  intros pc facts p H. unfold prove_sprop_r, prove_sprop.
  destruct p; try reflexivity; rewrite (uleq_r_ok _ _ _ _ _ H); reflexivity.
Qed.

Definition fld_cached_r (pc : pcache) (facts : list sprop) (cells : list cell) (off0 : sv) (f : Z * Z) : option sv := ltac2:(tb__ "0|2|
S6bS53S0A1Lx;S5cS6bS28S3cVpc;Vfacts;Vcells;S77Voff0;S5cS62S62Vf;A3A2S5fS62S62Vf;A3M0S7fA6A3S0S57S0S6cS56S12fQ8SfeG0A1A2R1A3A2Lv;S0S62S59S0A1M1Lsh;Lv;G1G1G1X6bx5").

Lemma fld_cached_r_ok : ltac2:(tb__ "0|0|
S28S54S1A1S54S7A1S0S51S62S62A2S29R5R4A2Se0S53S0A1S4eR6R5R4R3R2A5SaeR5R4R3R2A4A3F_;Ff;Foff0;Fcells;Ffacts;Fpc;").
Proof.
  intros pc facts cells off0 f H. unfold fld_cached_r, fld_cached.
  destruct (read_cells_c_ok facts (mk_addk off0 (fst f)) (snd f) cells pc CRNone H) as (pc1 & -> & _).
  reflexivity.
Qed.

Fixpoint store_xs_r (pc : pcache) (facts : list sprop) (cells : list cell) (off0 : sv) (flds : list (Z * Z))
         (i : nat) (v : sv) (k : Z) (need : nat -> bool) (j : nat) : option (list sv) :=
  match flds with
  | [] => Some []
  | f :: rest =>
      let here :=
        if Nat.eqb j i then Some (narrow_r pc facts k v)
        else if need j then fld_cached_r pc facts cells off0 f
        else Some (SLit 0) in
      match here, store_xs_r pc facts cells off0 rest i v k need (S j) with
      | Some x, Some xs => Some (x :: xs)
      | _, _ => None
      end
  end.

Lemma store_xs_r_ok : ltac2:(tb__ "0|0|
S28S54S1A1S54S7A1S0S55S0S62S55S50F_;S54S51S62S62A2A1S55S29RaR9A2Se0S53S54S0A1A1S4bRbRaR9R8R3R7R6R5R4R2AaSdaRaR9R8R3R7R6R5R4R2A9A3F_;Fj;Fflds;Fneed;Fk;Fv;Fi;Foff0;Fcells;Ffacts;Fpc;").
Proof.
  intros pc facts cells off0 i v k need flds. induction flds as [|f rest IH]; intros j H; cbn [store_xs_r store_xs].
  - reflexivity.
  - rewrite (IH (S j) H), (narrow_r_ok _ _ _ _ H), (fld_cached_r_ok _ _ _ _ _ H). reflexivity.
Qed.

Lemma forallb_ext_eq : forall {A} (f g : A -> bool) (l : list A),
  (forall x, f x = g x) -> forallb f l = forallb g l.
Proof.
  intros A f g l H. induction l as [|x t IH]; cbn [forallb]; [reflexivity|]. rewrite (H x), IH. reflexivity.
Qed.

Definition arr_after_store_c (pc : pcache) (facts : list sprop) (o : sobj) (off : sv) (k : Z) (v : sv)
           (esz : Z) (cnt : sv) (flds : list (Z * Z)) (tmpl : list tfact) : odefault * pcache := ltac2:(tb__ "0|5|
S53S51S0S62A2M0A1S51S5S28A2M1Lx;S8dVfacts;S7cSeaVoff;SbVo;A1A3Vesz;A3G0G0G1Lp;R1S0S62S53S62A1S50Lx;S95R2Vcnt;A2S62S5aSfbZ0R1A2S100Sf9SfdVesz;R1A2R2A2SfcZ2Z3eA2A2A2Ldlt;S56X53x2S50S50G1Lbeyond;R1S52S5S28S9Vo;A1M2Vpc;A4S53S55A1G1Lx;S89Vflds;R2Vk;A3S55S30Vpc;Vfacts;A2S28S77Voff;S101R4A1A2S0S55S132S8S8S5aS7dR5R1A2S7dR2R1A2A2Lt;Vtmpl;A3Lj;S55S50Fj;S52S5S28S53S54S0A1M3A1S5Lx;S4bR3Vfacts;SaVo;A1R2Vflds;R4Vv;Vk;R1U0AaG3S50S5L_;S5aS5aS3aR4Vfacts;R8Z1Vcnt;A5Sb0Vflds;R5R7Vk;A4A2S133S8S8S5dS5bS7dR6R1A2A1S133S1S47R5Vfacts;A2SddR2R1A2A3A2Lt;Vtmpl;A3A2G2ScX50x2Lxs;ScX53x2R3A4Tneed;Toff0;Tpc1;Li;S52S5S28ScVpc;A4M4X53x2X50x2Tbeyond;Lc;Lidx;X51x1Lp;G4X53x2").

Lemma arr_after_store_c_ok : ltac2:(tb__ "0|0|
S28S54S1A1S2S0S62S0S62S0S54S51S62S62A2A1S54S8A1S29RaR9A2S2aS5RaS3eRbRaR9R8R7R6R5R4R3R2AaSa7RaR9R8R7R6R5R4R3R2A9A4F_;Ftmpl;Fflds;Fcnt;Fesz;Fv;Fk;Foff;Fo;Ffacts;Fpc;").
Proof.
  intros pc facts o off k v esz cnt flds tmpl H. unfold arr_after_store_c, arr_after_store.
  destruct (lin_decomp facts (mk_alu ALU_SUB off (ob_lo o)) esz) as [[idx c]|]; [|apply cres_ret; exact H].
  cbv zeta.
  destruct (match same_atoms idx cnt with
            | Some dlt => (0 <=? dlt) && (esz * dlt + c <? 2 ^ 62)
            | None => false
            end); [apply cres_ret; exact H|].
  destruct (fld_index flds c k) as [i|]; [|apply cres_ret; exact H].
  pose proof (force_d_ok _ _ H) as H1.
  rewrite (store_xs_r_ok _ _ _ _ _ _ _ _ _ _ H1).
  destruct (store_xs facts (ob_cells o) (mk_addk off (- c)) flds i v k
              (fun j => existsb (fun t => tf_mentions i t && tf_mentions j t) tmpl) 0) as [xs|];
    [|apply cres_ret; exact H1].
  rewrite (uleq_r_ok _ _ _ _ _ H1).
  rewrite (forallb_ext_eq
             (fun t => negb (tf_mentions i t) || forallb (prove_sprop_r (force_d pc facts) facts) (tf_inst xs t))
             (fun t => negb (tf_mentions i t) || forallb (prove_sprop facts) (tf_inst xs t))).
  - apply cres_ret; exact H1.
  - intros t. f_equal. apply forallb_ext_eq. intros p. apply prove_sprop_r_ok; exact H1.
Qed.

Definition obj_store_d_c (pc : pcache) (facts : list sprop) (o : sobj) (off : sv) (k : Z) (v : sv) : sobj * pcache := ltac2:(tb__ "0|3|
S51S2S28A2M0G0Lx;S45Vpc;Vfacts;Vo;Voff;Vk;Vv;A6S2S28S5G0Lx;S9Vo;A1S52S2S28R2R1A4M1G1G1S63S52S2S28R3R2A4Ll;M2G2S62S0S54S51S62S62A2A1S54S8A1S51S5S28A2G0Lx;S3eR5Vfacts;Vo;Voff;Vk;Vv;R4R3R2R1AaS5S28S52S2S28S10SdR8A1SbR8A1S11R8A1SaR8A1R2A5R1A4Lpc2;Ld;X51x1Ltmpl;Lflds;Lcnt;Lesz;X5x6Lpc1;Lo1;X51x1").

Lemma obj_store_d_c_ok : ltac2:(tb__ "0|0|
S28S54S1A1S2S0S62S0S29R6R5A2S2aS2R6S46R7R6R5R4R3R2A6SceR6R5R4R3R2A5A4F_;Fv;Fk;Foff;Fo;Ffacts;Fpc;").
Proof.
  intros pc facts o off k v H. unfold obj_store_d_c, obj_store_d.
  destruct (obj_store_c_ok pc facts o off k v H) as (pc1 & -> & H1).
  destruct (ob_dflt o) as [ | | | l | l | esz cnt flds tmpl]; try (apply cres_ret; exact H1).
  destruct (arr_after_store_c_ok pc1 facts o off k v esz cnt flds tmpl H1) as (pc2 & -> & H2).
  apply cres_ret; exact H2.
Qed.

Lemma set_reg_facts : ltac2:(tb__ "0|0|
S3S10dQ5A1S0Se0S54S1A1S4S69R3R2R1A3A1S4R3A1A3Fv;Fr;FS;").
Proof. intros S r v. unfold set_reg. destruct (regZ r =? 0); reflexivity. Qed.

Lemma find_obj_d_nth : ltac2:(tb__ "0|2|
S54S2A1S67S0S62S55S55S2S0Se0S53S51S51S55S2A2M0S0A2M1A1SadR8R7R6R5R4A5S57G1S52G0S0S52S55S2R3R2A4R1A4A2A3Se3S55S55Se1Se0S55R5S12eR6R1A2A3Se0S53S2A1S134S2RaR1A3S57S2R4A2A3A2Li;A2F_;Foff;Fo;Fn;Fn0;Fk;Fae;Fdg;Fobjs;").
Proof.
  intros objs dg ae k. induction objs as [|o0 rest IH]; intros n0 n o off H; cbn [find_obj_d] in H; [discriminate|].
  destruct (match rel_offset (ob_base o0) ae with
            | Some off0 => if in_bounds_d dg (ob_lo o0) (ob_hi o0) off0 k then Some (n0, o0, off0) else None
            | None => None
            end) as [r|] eqn:E.
  - injection H as ->. exists 0%nat.
    destruct (rel_offset (ob_base o0) ae) as [off0|]; [|discriminate].
    destruct (in_bounds_d dg (ob_lo o0) (ob_hi o0) off0 k); [|discriminate].
    injection E as <- <- <-. split; [symmetry; apply Nat.add_0_r | reflexivity].
  - destruct (IH (S n0) n o off H) as (i & Hn & Hnth). exists (S i).
    split; [rewrite Hn; apply Nat.add_succ_comm | exact Hnth].
Qed.

Lemma find_obj_nth : ltac2:(tb__ "0|2|
S54S2A1S54S1A1S0S62S55S2S0Se0S53S51S51S55S2A2M0S0A2M1A1S88R7R6R5R4U0A5S57G1S52G0S0S52S55S2R3R2A4R1A4A2A3Se0S53S2A1S134S2R8R4A3S57S2R3A2A3F_;Foff;Fo;Fn;Fk;Fae;Ffacts;Fobjs;").
Proof.
  intros objs facts ae k n o off H. unfold find_obj in H.
  destruct (find_obj_d objs (ctx0 facts) ae k 0) as [r|] eqn:E.
  - injection H as ->. destruct (find_obj_d_nth _ _ _ _ _ _ _ _ E) as (i & -> & Hi). exact Hi.
  - destruct (find_obj_d_nth _ _ _ _ _ _ _ _ H) as (i & -> & Hi). exact Hi.
Qed.

Lemma list_upd_set : forall {A} (l : list A) n f x,
  nth_error l n = Some x -> list_upd l n f = list_set l n (f x).
Proof.
  induction l as [|h t IH]; intros n f x H; destruct n; cbn in *; try discriminate.
  - inversion H. reflexivity.
  - rewrite (IH _ _ _ H). reflexivity.
Qed.

Section WithImage.
  Variable segs : list Segment.

  Definition lres_ok (pc' : pcache) (r : load_res) : Prop := ltac2:(tb__ "0|0|
S66OLr;Vr;S0S3S29Vpc';S4R1A1A2LS';Lv;Se2X66x2").
  Definition lr_keeps (S : sstate) (r : load_res) : Prop := ltac2:(tb__ "0|0|
S66OLr;Vr;S0S3Se0S54S1A1S4R1A1S4VS;A1A3LS';Lv;Se2X66x2").

  Definition lcres (r : load_res * pcache) (orig : load_res) : Prop := ltac2:(tb__ "0|0|
Se3S28S28Se1Se0S51S66S28A2Vr;S52S66S28Vorig;R1A4A3S124R1Vorig;A2A2Lpc';A2").

  Lemma lcres_keep : ltac2:(tb__ "0|0|
S3S28S66S29R2S4R3A1A2S118R4R2A2S114S52S66S28R3R4A4R3A2F_;F_;Fr;Fpc;FS;").
  Proof.
    intros S pc r H K. exists pc. split; [reflexivity|]. destruct r as [v S'|]; [|exact I].
    cbn in *. rewrite K. exact H.
  Qed.

  Lemma load_fresh_keeps : ltac2:(tb__ "0|0|
S3S55S2S0S62S50S64S118R7S76R7R6R5R4R3R2R1A7A2Fw;Fsgn;Fk;Foff;Fo;Fn;FS;").
  Proof. intros. unfold load_fresh, fresh. destruct (dflt_writable (ob_dflt o)); reflexivity. Qed.

  Definition ro_span_r (pc : pcache) (facts : list sprop) (ae : sv) (k : Z) : bool := ltac2:(tb__ "0|3|
S51S62S62A2S50Lx;S8cS2dVpc;Vfacts;A2Vae;A2S62S62S105Sf9R1Vk;A2R2A2S62S50S50L_;M0SfbR3R2A2G0SfbR1Sd4A2G0SfbSf9R2Vk;A2S9fA2G0Sa6Vsegs;R3SffR1A1M1A3S53S54S10dQ8A1A1M2A1S50Lx;Sb4Vsegs;R3G1A3G2S58Ll;S56X53x2S56X50x2S56X50x2S56X50x2S56X50x2Tn;Lhi;Llo;X51x1").

  Lemma ro_span_r_ok : ltac2:(tb__ "0|0|
S28S54S1A1S0S62S29R4R3A2Se0S50S11eR5R4R3R2A4Sd3Vsegs;R4R3R2A4A3F_;Fk;Fae;Ffacts;Fpc;").
  Proof. intros pc facts ae k H. unfold ro_span_r, ro_span, itv. rewrite (get_d_ok _ _ H). reflexivity. Qed.

  Definition load_arr_c (pc : pcache) (S : sstate) (n : nat) (o : sobj) (off : sv) (k : Z) (sgn : bool) (w : N)
             (esz : Z) (cnt : sv) (flds : list (Z * Z)) (tmpl : list tfact) : load_res * pcache := ltac2:(tb__ "0|7|
S4VS;A1S54S1A1S53S51S0S62A2M0A1S51S66S28A2M1Lx;S8dR1S7cSeaVoff;SbVo;A1M2A3Vesz;A3G0G0G1Lp;R1S0S62S53S55A1G1Lx;S89Vflds;R1Vk;A3S55S51S50S28A2G1Lx;S4cVpc;R5R3Z1Vcnt;A5S50S28S50G1Lu;R2S26VS;A1S63S61S51S62S62A2Vflds;A2S55SafR2R1A2S54S0A1S77Voff;S101R7A1A2S0S10SdVo;A1G2S11Vo;A1S5eS7Sa8R1Vflds;R4A3SaVo;A1A3S9Vo;A1A5S2S52S66S28S6fS6cVsgn;Vw;SfS135S12eS136R5A1M3R8A2A1A1A3S22S18VS;A1S27VS;A1S25VS;A1S24VS;A1S19VS;A1S8eS2S12VS;A1Vn;R1A4S5eS1SdfR3Vtmpl;A2RcA3M4S135S12eG3R4A2A1S17VS;A1A9A2S34G4A1A4To';Toff0;Txs;Tm;Tx0;S52S66S28S76VS;Vn;Vo;Voff;Vk;Vsgn;Vw;A7M5R1A4X50x2Lpc1;Lu;X51x1Li;S52S66S28G5Vpc;A4M6X53x2Lc;Lidx;X51x1Lp;G6X53x2Tfacts;").

  Lemma load_arr_c_ok : ltac2:(tb__ "0|0|
S28S3S55S2S0S62S50S64S62S0S54S51S62S62A2A1S54S8A1S29RcS4RbA1A2S114S116RdRcRbRaR9R8R7R6R5R4R3R2AcSbdRcRbRaR9R8R7R6R5R4R3R2AbA2F_;Ftmpl;Fflds;Fcnt;Fesz;Fw;Fsgn;Fk;Foff;Fo;Fn;FS;Fpc;").
  Proof.
    intros pc S n o off k sgn w esz cnt flds tmpl H. unfold load_arr_c, load_arr. cbv zeta.
    destruct (lin_decomp (ss_facts S) (mk_alu ALU_SUB off (ob_lo o)) esz) as [[idx c]|];
      [|apply (lcres_keep S); [exact H | apply load_fresh_keeps]].
    destruct (fld_index flds c k) as [i|]; [|apply (lcres_keep S); [exact H | apply load_fresh_keeps]].
    destruct (uleq_c_ok pc (ss_facts S) idx 1 cnt H) as (pc1 & -> & H1).
    destruct (uleq (ss_facts S) idx 1 cnt); [|apply (lcres_keep S); [exact H1 | apply load_fresh_keeps]].
    eexists. split; [reflexivity|]. cbn [lres_ok ss_facts]. apply pc_init_ok.
  Qed.

  Definition load_dflt_c (pc : pcache) (S : sstate) (n : nat) (o : sobj) (off : sv) (k : Z) (sgn : bool) (w : N)
    : load_res * pcache := ltac2:(tb__ "0|2|
S5S51S66S28A2Lx;S9Vo;A1S52S66S28S76VS;Vn;Vo;Voff;Vk;Vsgn;Vw;A7Vpc;A4M0G0G0S63G0Ll;M1G1S62S0S54S51S62S62A2A1S54S8A1S116Vpc;VS;Vn;Vo;Voff;Vk;Vsgn;Vw;R4R3R2R1AcLtmpl;Lflds;Lcnt;Lesz;X5x6").

  Lemma load_dflt_c_ok : ltac2:(tb__ "0|0|
S28S3S55S2S0S62S50S64S29R8S4R7A1A2S114S117R9R8R7R6R5R4R3R2A8SbeR8R7R6R5R4R3R2A7A2F_;Fw;Fsgn;Fk;Foff;Fo;Fn;FS;Fpc;").
  Proof.
    intros pc S n o off k sgn w H. unfold load_dflt_c, load_dflt.
    destruct (ob_dflt o); try (apply (lcres_keep S); [exact H | apply load_fresh_keeps]).
    apply load_arr_c_ok; exact H.
  Qed.

  Definition load_image (S : sstate) (n : nat) (o : sobj) (off : sv) (k : Z) (sgn : bool) (w : N) : load_res := ltac2:(tb__ "0|8|
S0S66Lx;SdVo;A1S62S62S66Lz;R1S0S66Loff;Voff;S62S53S62A1S66Lx;Sb5Vsegs;SfaR1SfcZ2Z40A2A2SffVk;A1A3S62S6fS6cVsgn;Vw;S6R1A1A3VS;A2Lz;S80X53x2Lzo;S63S76VS;Vn;Vo;Voff;Vk;Vsgn;Vw;A7M0Li;M1Se5S0S0G0Lb;La;M2Lop;M3G3Se6G2Lop;M4G4S50S64S0G0La;Lw0;Lsgn0;M5S63S0S62G0Lk0;Li;Ll;M6X0x8S63G0Lp;M7G7X62x3Lz;G1G3G3G4G4G5G6X0x8").

  Lemma load_image_keeps : ltac2:(tb__ "0|0|
S3S55S2S0S62S50S64S118R7S11bR7R6R5R4R3R2R1A7A2Fw;Fsgn;Fk;Foff;Fo;Fn;FS;").
  Proof.
    intros. unfold load_image.
    destruct (ob_base o) as [z| | | | | | |]; try apply load_fresh_keeps.
    destruct z; try apply load_fresh_keeps.
    destruct off; try apply load_fresh_keeps.
    destruct (image_load segs _ _); [reflexivity | exact I].
  Qed.

  Definition sym_load_c (pc : pcache) (S : sstate) (ae : sv) (k : Z) (sgn : bool) : load_res * pcache := ltac2:(tb__ "0|f|
S12fQ8SfeVk;A1A2S64S4VS;A1S54S1A1S0S53S62A1M0Lae;Vae;S62Sd2Vsegs;SfaR1SfcZ2Z40A2A2SffVk;A1A3La;S63S59S62A1M1Li;Se5S0S0G1Lb;La;M2Lop;M3G3Se6G2Lop;M4G4S50S64S0G1La;Lw0;Lsgn0;S63S0S62G1Lk0;Li;Ll;X0x8G0G0S51S66S28A2M5Lro;R1S62S52S66S28S6fS6cVsgn;R4S6R1A1A3VS;A2Vpc;A4Lz;S51S53S51S51S55S2A2M6S0A2M7A1M8S28A2G5Lx;S3bVpc;S12VS;A1R2Vae;Vk;U0A6G8S28G8G5Lfo;R2G7G7G5Lp;R1G6S0G6G5Lp0;R2S55S2S51S6bS28A2G5Lx;S3cR6R9SaR1A1R3Vk;S7fA6S6bS28S6bG5Lcr;R2S0S51S0S28A2G5Lx;M9S38R2RcVsgn;RdR1A5S0S28S52S66S28S6fR2VS;A2R1A4Lpc3;Le;MaX51x1Lv;S0S62G9S38R3RdVsgn;ReS7cSf1R2S6SfdZ8R1A2A1A3A5GaX51x1Lsh;Lv;S5G5Lx;S9R3A1S52S66S28S76VS;R4R3R5Vk;Vsgn;RcA7R1A4S52S66S28S6fS6Z0MbA1VS;A2R1A4S52S66S28S11bVS;R4R3R5Vk;Vsgn;RcA7R1A4S63G9S38R2RcVsgn;RdSeR1SbfRcSeaR6SbR4A1A4Vk;A3A5GaX51x1Ll;McGcS62S0S54S51S62S62A2MdA1S54S8A1S116R5VS;R8R7R9Vk;Vsgn;R10R4R3R2R1AcLtmpl;Lflds;Lcnt;Lesz;X5x6S51S54S51GdS0A2A1MeS28A2G5Lx;S41R1RbSaR3A1R5Vk;A5GeS28S53S0A1G5Lx;SdeU9R2GbVk;A4S0S52S66S28S6fS6cVsgn;RfR1A3VS;A2R2A4Lv;S117R1VS;R6R5R7Vk;Vsgn;ReA8X53x2Lpc3;Llc;X51x1S117R1VS;R4R3R5Vk;Vsgn;RcA8X6bx5Lpc2;Lcr;X51x1Lo;Ln;X51x1Loff;Lp0;X51x1Lp;S52S66S28S50S66L_;S50S50L_;S17VS;A1S58S11eR1R4Vae;Vk;A4X50x2S51S0S3A2S66Lx;Sb1VS;A1S0S3S6fS6cVsgn;R7R2A3R1A2LS1;Lx;X51x1S80X50x2R1A4X53x2Lpc1;Lfo;X51x1X53x2Tro;Tfacts;Tw;").

  Lemma sym_load_c_ok : ltac2:(tb__ "0|0|
S28S3S0S62S50S29R5S4R4A1A2S114S113R6R5R4R3R2A5SdbVsegs;R5R4R3R2A5A2F_;Fsgn;Fk;Fae;FS;Fpc;").
  Proof.
    intros pc S ae k sgn H. unfold sym_load_c, sym_load. cbv zeta.
    destruct (match ae with
              | SLit a => ro_load segs (a mod 2 ^ 64) (Z.to_nat k)
              | _ => None
              end) as [z|].
    { apply (lcres_keep S); [exact H | reflexivity]. }
    destruct (find_obj_c_ok pc (ss_objs S) (ss_facts S) ae k 0 H) as (pc1 & -> & H1).
    destruct (find_obj (ss_objs S) (ss_facts S) ae k 0) as [[[n o] off]|].
    - destruct (read_cells_c_ok (ss_facts S) off k (ob_cells o) pc1 CRNone H1) as (pc2 & -> & H2).
      destruct (read_cells (ss_facts S) (ob_cells o) off k CRNone) as [v|v sh| | |].
      + destruct (mk_ext_f_c_ok pc2 (ss_facts S) sgn (8 * Z.to_N k)%N v H2) as (pc3 & -> & H3).
        apply (lcres_keep S); [exact H3 | reflexivity].
      + destruct (mk_ext_f_c_ok pc2 (ss_facts S) sgn (8 * Z.to_N k)%N (mk_alu ALU_SRL v (SLit (8 * sh))) H2)
          as (pc3 & -> & H3).
        apply (lcres_keep S); [exact H3 | reflexivity].
      + destruct (ob_dflt o) as [ | | | l | l | esz cnt flds tmpl].
        * apply (lcres_keep S); [exact H2 | apply load_fresh_keeps].
        * apply (lcres_keep S); [exact H2 | reflexivity].
        * apply (lcres_keep S); [exact H2 | apply load_image_keeps].
        * destruct (mk_ext_f_c_ok pc2 (ss_facts S) sgn (8 * Z.to_N k)%N
                      (SLBytes l (mk_alu_f (ss_facts S) ALU_SUB off (ob_lo o)) k) H2) as (pc3 & -> & H3).
          apply (lcres_keep S); [exact H3 | reflexivity].
        * destruct (mk_ext_f_c_ok pc2 (ss_facts S) sgn (8 * Z.to_N k)%N
                      (SLBytes l (mk_alu_f (ss_facts S) ALU_SUB off (ob_lo o)) k) H2) as (pc3 & -> & H3).
          apply (lcres_keep S); [exact H3 | reflexivity].
        * apply load_arr_c_ok; exact H2.
      + destruct (lit_cells_c_ok (ss_facts S) off k (ob_cells o) pc2 H2) as (pc3 & -> & H3).
        destruct (tile_cells 9 (lit_cells (ss_facts S) (ob_cells o) off k) 0 k).
        * apply (lcres_keep S); [exact H3 | reflexivity].
        * apply load_dflt_c_ok; exact H3.
      + apply load_dflt_c_ok; exact H2.
    - rewrite (ro_span_r_ok _ _ _ _ H1). apply (lcres_keep S); [exact H1|].
      destruct (ss_lenient S ||| ro_span segs (ss_facts S) ae k); [reflexivity | exact I].
  Qed.

  Definition sym_store_c (pc : pcache) (S : sstate) (ae : sv) (k : Z) (v : sv) : option sstate * pcache := ltac2:(tb__ "0|8|
S51S53S51S51S55S2A2M0S0A2M1A1M2S28A2S51S53S3A1M3S28A2M4Lx;S3bVpc;S12VS;A1M5S4VS;A1M6Vae;Vk;U0A6G2S28G2G4Lfo;R2G1G1G4Lp;R1G0S0G0G4Lp0;R2S55S2S50G4L_;S20S9R1A1A1S51S2S28A2G4Lx;S46R6G6R1R3Vk;Vv;A6S2S28S52G3S28S57S3Sd6VS;S8eS2G5R4R2A4A2A2R1A4Lpc2;Lo';X51x1S52G3S28S59S3A1M7R6A4X50x2Lo;Ln;X51x1Loff;Lp0;X51x1Lp;S52G3S28G7R1A4X53x2Lpc1;Lfo;X51x1").

  Definition sres_ok (pc' : pcache) (r : option sstate) : Prop := ltac2:(tb__ "0|0|
S53S3A1OLr;Vr;S3S29Vpc';S4R1A1A2LS';Se2X53x2").

  Lemma sym_store_c_ok : ltac2:(tb__ "0|2|
S28S3S0S62S0S29R5S4R4A1A2Se3S28S28Se1Se0S51S53S3A1M0S28A2S115R7R6R5R4R3A5S52G0S28SdcR6R5R4R3A4M1R1A4A3S126R1G1A2A2Lpc';A2F_;Fv;Fk;Fae;FS;Fpc;").
  Proof.
    intros pc S ae k v H. unfold sym_store_c, sym_store.
    destruct (find_obj_c_ok pc (ss_objs S) (ss_facts S) ae k 0 H) as (pc1 & -> & H1).
    destruct (find_obj (ss_objs S) (ss_facts S) ae k 0) as [[[n o] off]|] eqn:E;
      [|exists pc1; split; [reflexivity | exact I]].
    destruct (dflt_writable (ob_dflt o)); [|exists pc1; split; [reflexivity | exact I]].
    destruct (obj_store_d_c_ok pc1 (ss_facts S) o off k v H1) as (pc2 & -> & H2).
    rewrite (list_upd_set _ _ (fun o0 => obj_store_d (ss_facts S) o0 off k v) _ (find_obj_nth _ _ _ _ _ _ _ E)).
    exists pc2. split; [reflexivity | exact H2].
  Qed.

  Definition decide_branch_c (pc : pcache) (S : sstate) (c : branch_cond) (a b : sv) : decision * pcache := ltac2:(tb__ "0|11|
S0S51S68S28A2M0La;Va;S62S0G0Lb;Vb;S62S52S68S28S50S68L_;S138Vc;S10eQ40M1R2A2S10eG1R1A2A3S6eS6dX50x2Vpc;A4Ly;S63S50G0L_;S1aVa;Vb;A2S52S68S28Se8S68Lc;Vc;S6eS6dS6dS6eS6dS6eXe8x6Vpc;A4Se8G0Lc;Vc;S53S50A1G0Lx;M2Sd5Va;Vb;A2M3S50S52S68S28S50S68Le;M4R1S6eS6dX50x2Vpc;A4Le;S68G0Lx;M5SacS4VS;A1M6S16Vc;Va;Vb;A3A2S52S68S28S6eVpc;A4M7S52S68S28S6dVpc;A4M8G5Sb8S2bVpc;A1Vc;Va;Vb;A4G7G8S3fVpc;G6A2S28S52S68S28S10cS2cR1A1S40R1G6A2S2dR1G6A2Vc;Va;Vb;A6R1A4Tpc1;X68x3X68x3M9X53x2G2G3S50S52S68S28G4R1S6dS6eX50x2Vpc;A4Le;G9X53x2G9G9G9G9Xe8x6X50x2MaLi;MbSe5S0S0GaLb0;La0;McLop;MdGdSe6GcLop;MeGeS50S64S0GaLa0;Lw;Lsgn;MfS63S0S62GaLk;Li;Ll;M10X0x8Lx;GbGdGdGeGeGfG10X0x8").

  Lemma decide_branch_c_ok : ltac2:(tb__ "0|0|
S28S3Se8S0S0S29R5S4R4A1A2S2aS68S4R5A1S11aR6R5R4R3R2A5SaaR5R4R3R2A4A4F_;Fb;Fa;Fc;FS;Fpc;").
  Proof.
    intros pc S c a b H.
    assert (Hgen : cres (ss_facts S)
              (match fact_lookup (ss_facts S) (SPBranch c a b) with
               | DUnknown_ =>
                   match itv_decide_t (pc_0 pc) c a b with
                   | DUnknown_ => let pc1 := force_ud pc (ss_facts S) in
                                  (decide_t_q (pc_sf pc1) (get_ud pc1 (ss_facts S)) (get_d pc1 (ss_facts S)) c a b, pc1)
                   | d => (d, pc)
                   end
               | d => (d, pc)
               end)
              (match fact_lookup (ss_facts S) (SPBranch c a b) with
               | DUnknown_ =>
                   match itv_decide_t (ctx0 (ss_facts S)) c a b with
                   | DUnknown_ => decide_t (mk_dig (ss_facts S)) c a b
                   | d => d
                   end
               | d => d
               end)).
    { destruct (fact_lookup (ss_facts S) (SPBranch c a b)); try (apply cres_ret; exact H).
      rewrite (pc_0_ok _ _ H).
      destruct (itv_decide_t (ctx0 (ss_facts S)) c a b); try (apply cres_ret; exact H).
      cbv zeta. pose proof (force_ud_ok _ _ H) as H1.
      rewrite (get_d_ok _ _ H1), (get_ud_ok _ _ H1), (decide_t_q_eq _ _ c a b (pc_sf_ok_d _ _ H1)).
      apply cres_ret. exact H1. }
    unfold decide_branch_c, decide_branch.
    destruct a; destruct b; try (apply cres_ret; exact H);
      (destruct (sv_eqb _ _); [apply cres_ret; exact H|]);
      destruct c; try exact Hgen;
      (destruct (same_base_eq _ _); [apply cres_ret; exact H | exact Hgen]).
  Qed.

  Definition step_ok (ch' : pcache) (o : step_out) : Prop := ltac2:(tb__ "0|0|
S65OLo;Vo;S3S29Vch';S4R1A1A2LS';S3S3Se2LS2;LS1;S98Se2Lr;X65x3").

  Definition reinit (ch : pcache) (o : step_out) : pcache := ltac2:(tb__ "0|0|
S65S28Lo;Vo;S3S34S4R1A1A1LS';S3S3Vch;LS2;LS1;S98Vch;Lr;X65x3").

  Definition sym_step_c (ch : pcache) (S : sstate) : step_out * pcache := ltac2:(tb__ "0|3c|
S18VS;A1S62S53SebA1S51S65S28A2M0Lx;Sb7Vsegs;R1A2SebS3S73S70R1Sf9R3Z4M1A2A2A1LS';S3S65FS';SebG0Li;R2S10dQ5M2A1M3S10dQ14M4A1M5S52S65S28R3S69VS;R2SbcS137Q20M6Q40S111G6G4QcM7R1S10eG7Z0M8A2A5M9A3A1A3A1Vch;A4Limm;Lrd;G3G5S52S65S28R3S69VS;R2S6SfaSf9R5S10fG6G9A2A2SfcZ2Z40A2MaA2A1A3A1Vch;A4Limm;Lrd;G3S10dQ15MbA1S52S65S28S73S70S69VS;R2S6SfaSf9R5G1A2GaA2A1A3SfaSf9R5S10fGbR1A2A2GaA2A2A1Vch;A4Limm;Lrd;G3G3S10dG7A1McS52S65S28S0S65Lx;S77S7aVS;R2A2MdSb6R1A1MeA2MfS62SfaS103R1S104Z1M10A1A2GaA2S62S73S70S69VS;R5S6SfaSf9R8G1A2GaA2A1A3R1A2A1Ttgt;Lt;S63S74Sa3A1M11Li0;Se5S0S0G11Lb;La;M12Lop;M13G13Se6G12Lop;M14G14S50S64S0G11La;Lw;Lsgn;S63S0S62G11Lk;Li0;Ll;X0x8Vch;A4Limm;Lrs1;Lrd;Se8G3G3S10dQdM15A1S7aVS;R3A2M16S0G16S0SfaSf9R9S10fG15R3A2A2GaA2S62S51S68S28A2G0Lx;S11aVch;VS;R7R3R2A5S68S28S52S65S28S68S65Ld;R2S73S70VS;R3A2A1S73S70VS;Sf9RcG1A2M17A2A1Sa5S70S81VS;S16R9R5R4A3M18A2R3A2S70S81VS;S1dG18A1A2G17A2A2X68x3R1A4Lch1;Ld;X51x1Ttpc;Tb;Ta;Limm;Lrs2;Lrs1;Lc;SefS50G3G3GcGfS0S51S66S28A2G0Lx;M19S113Vch;VS;R1S94R6A1R5A5S66S28S52S65S28S66S65Lr;M1aR2S0S3RbS69R1R8R2A3A1LS';Lv;S74Sa1A1M1bX66x2R1A4Lch1;Lr;X51x1Tae;Limm;Lrs1;Lrd;Lsgn;Lsz;SefG3G3GcS77G16GeA2M1cS0S53S0A1G0Lx;M1dS19VS;A1M1eS0S52S65S28S74Sa4A1M1fVch;A4M20Ls;M21S51S53S3A1M22S28A2G0Lx;M23S115Vch;VS;R1S94R5A1G16A5G22S28S52S65S28G22S65Lr;M24R2S3R9R1A1LS';G1bX53x2R1A4Lch1;Lr;M25X51x1X53x2Tae;Limm;Lrs2;Lrs1;Lsz;Se5G3G3GcS51S0S28A2G0Lx;M26S39Vch;S4VS;A1M27R4GdS6SfaGeGaA2A1M28A5S0S28S52S65S28R7S69VS;R5R2A3M29A1R1A4Lch1;Lv;M2aX51x1Limm;Lrs1;Lrd;Lop;Se5G3G3S10dQ6M2bA1G26S39Vch;G27R4GdS6S110G2bR1A2A1A5G2aX51x1Lsh;Lrs1;Lrd;Lop;Se5G3G3G3G26S43Vch;G27R4GdS7aVS;R1A2M2cA5G2aX51x1Lrs2;Lrs1;Lrd;Lop;G3G3GcG26S37Vch;G27Sf0GdG28A5S0S28S52S65S28R6G29A1R1A4Lch1;Lv;X51x1Limm;Lrs1;Lrd;Se5G3G3G3S52S65S28R5S69VS;R3Sc0R4GdS6S110G2R1A2A1A3A3A1Vch;A4Lsh;Lrs1;Lrd;Lop;Se5G3G3G3G26S44Vch;G27R4GdG2cA5G2aX51x1Lrs2;Lrs1;Lrd;Lop;S10dQ4A1M2dG2dG2dG3G3S52S65S28R6VS;A1Vch;A4Lrs1;Lrd;Lsucc;Lpred;Lfm;G3G3GcS52S65S28R4VS;A1Vch;A4Limm;Lrs1;Lrd;S52S65S28S74Sa0A1Vch;A4G20Se6G3G3G3S52S65S28R5S69VS;R3Sc6G27R4GdG2cA4A3A1Vch;A4Lrs2;Lrs1;Lrd;Lop;Se6G3G3G3G26S42Vch;G27R4GdG2cA5G2aX51x1Lrs2;Lrs1;Lrd;Lop;SecS50S50G3G3G2cS0S50G0L_;M2eS5bS82G27R1S84R6A1A3A1G20G19S113Vch;VS;R1S83R6A1S58A5S66S28S52S65S28G1aR2S0S3RbS96S69R1R7R2A3S57S0R5A2A2A1LS';Lv;G1bX66x2R1A4Lch1;Lr;X51x1X50x2Tae;Lrs1;Lrd;Lrl;Laq;Lwd;SecS50S50G3G3G3GdS0G2eS5bS82G27R1S84R7A1A3A1G20G1dG1eS0G2eS1aR1R2A2G23S115Vch;S96VS;S59S0A1A2R2S83R8A1G16A5G22S28S52S65S28G24R2S3RcS69R1R8S6G8A1A3A1LS';G1bX53x2R1A4Lch1;Lr;X51x1G20X50x2Le;S52S65S28R8S69VS;R4S6G10A1A3A1Vch;A4X53x2X50x2Tae;Lrs2;Lrs1;Lrd;Lrl;Laq;Lwd;Sf3SecS50S50G3G3G3G20Lrs2;Lrs1;Lrd;Lrl;Laq;Lw;Lop;Se9G3G3GcS52S65S28S9aVS;R4R3Se9S50Lop;M2fR4S58S5bS139R2A1A1M30G30Xe9x3R1A5Vch;A4Lcsr;Lrs1;Lrd;Lop;Se9G3G3GcS52S65S28S9aVS;R4R3G2fR4S58S5bS102S110G2R2A2G8A2A1M31G31Xe9x3R1A5Vch;A4Lcsr;Luimm;Lrd;Lop;Se7G3G3GcGfS0Se7G0Lfmt;R5G19S113Vch;VS;R1G1S56A5S66S28S52S65S28G1aR2S0S3RaS78R1R8S92R2A1A3A1LS';Lv;G1bX66x2R1A4Lch1;Lr;X51x1G19S113Vch;VS;R1Z8M32S58A5S66S28S52S65S28G1aR2S0S3RaS78R1R8
R2A3A1LS';Lv;G1bX66x2R1A4Lch1;Lr;X51x1Xe7x2Tae;Limm;Lrs1;Lrd;Lfmt;Se7G3G3GcG1cS0G1dG1eG21G23S115Vch;VS;R1Se7S62Lfmt;R5G1G32Xe7x2S8aVS;R3A2A5G25X51x1X53x2Tae;Limm;Lrs2;Lrs1;Lfmt;Sf6Se7G3G3G3G3S10dQ3A1M33S52S65S28S50S65L_;M34Sd1VS;R1A2M35S7bVS;R5A2G1fX50x2Vch;A4Lrm;Lrs3;Lrs2;Lrs1;Lrd;Lfmt;Lop;Sf4Se7G3G3G3G33S52S65S28G34G35S7bVS;R4A2G1fX50x2Vch;A4Lrm;Lrs2;Lrs1;Lrd;Lfmt;Lop;Se7G3G3G33S52S65S28G34G35S7bVS;R3A2M36G1fX50x2Vch;A4Lrm;Lrs1;Lrd;Lfmt;Sf8Se7G3G3G3S52S65S28G34Sb2VS;A1M37G36G1fX50x2Vch;A4Lrs2;Lrs1;Lrd;Lfmt;M38Lop;Sf7G38Lop;Sf5Se7G3G3G3G34G37Sb3VS;R3A2G1fX50x2S65S52S65S28R1S11dVch;R1A2A4To;Lrs2;Lrs1;Lrd;Lfmt;Lop;SeeSeeG3G3G33S52S65S28G34S5bG35A1G1fG34S5aS86R5A1S5dS86R4A1M39S87R4A1A2A2G36G34S5aS87R5A1G39A2S8bVS;R3A2G1fX50x2X50x2X50x2Vch;A4Lrm;Lrs1;Lrd;Lsrc;Ldst;SedSe7G3G3S52S65S28SedS65Ldir;R4Se7S65Lfmt;M3aR3R5S69VS;R2S6cS58G6S8aVS;R1A2M3bA3A3A1R5S69VS;R2G3bA3A1Xe7x2G3aR3R5S78VS;R2S92S6cS56G6G2cA3A1A3A1R5S78VS;R2G2cA3A1Xe7x2Xedx2Vch;A4Lrs1;Lrd;Lfmt;Ldir;Se7G3G3S52S65S28G34G37S8bVS;R2A2G1fX50x2Vch;A4Lrs1;Lrd;Lfmt;Xebx23Tnx;Li;S52S65S28S74Sa2A1Vch;A4X53x2Tpc;").

  Ltac fin_ok H :=
    cbn [step_ok lres_ok sres_ok set_pc set_freg set_resv set_objs add_fact ss_facts] in *;
    rewrite ?set_reg_facts;
    cbn [step_ok set_pc set_freg set_resv set_objs add_fact ss_facts];
    rewrite ?set_reg_facts;
    first [exact H | exact I].

  Ltac keep_ok H :=
    eexists; split; [reflexivity|];
    unfold havoc_freg, havoc_reg, sym_csr, fresh;
    repeat match goal with
           | |- step_ok _ (match ?x with _ => _ end) => destruct x
           end;
    fin_ok H.

  Lemma reinit_ok : ltac2:(tb__ "0|0|
S28S65S11fS11dR2R1A2R1A2Fo;Fch;").
  Proof. intros ch o. destruct o; cbn [reinit step_ok]; [apply pc_init_ok | exact I | exact I]. Qed.

  Ltac go_ok H :=
    repeat lazymatch goal with
    | |- exists _, (match sym_load_c ?a ?b ?c ?d ?e with _ => _ end) = _ /\ _ =>
        let ch1 := fresh "ch" in let H1 := fresh "H" in
        destruct (sym_load_c_ok a b c d e H) as (ch1 & -> & H1); exists ch1; split; [reflexivity|];
        destruct (sym_load segs b c d e); fin_ok H1
    | |- exists _, (match sym_store_c ?a ?b ?c ?d ?e with _ => _ end) = _ /\ _ =>
        let ch1 := fresh "ch" in let H1 := fresh "H" in
        destruct (sym_store_c_ok a b c d e H) as (ch1 & -> & H1); exists ch1; split; [reflexivity|];
        destruct (sym_store b c d e); fin_ok H1
    | |- exists _, (match decide_branch_c ?a ?b ?c ?d ?e with _ => _ end) = _ /\ _ =>
        let ch1 := fresh "ch" in let H1 := fresh "H" in
        destruct (decide_branch_c_ok a b c d e H) as (ch1 & -> & H1); exists ch1; split; [reflexivity|];
        destruct (decide_branch b c d e); fin_ok H1
    | |- exists _, (match ?x with _ => _ end) = _ /\ _ => destruct x
    | |- exists _, (_, reinit _ _) = _ /\ _ => eexists; split; [reflexivity | apply reinit_ok]
    | |- exists _, (_, _) = _ /\ _ => keep_ok H
    end.

  Lemma sym_step_c_ok : ltac2:(tb__ "0|1|
S28S3S29R2S4R1A1A2Se3S28S28Se1Se0S51S65S28A2S123R4R3A2S52S65S28S9bVsegs;R3A2M0R1A4A3S11fR1G0A2A2Lch';A2F_;FS;Fch;").
  Proof.
    intros ch S H. unfold sym_step_c, sym_step. cbv zeta.
    destruct (instr_at segs (ss_pc S)) as [i|]; [|exists ch; split; [reflexivity | exact I]].
    destruct i;
      try (match goal with
           | |- context [mk_slt_f_c ?a ?b ?c ?d ?e] =>
               destruct (mk_slt_f_c_ok a b c d e H) as (ch1 & -> & H1); exists ch1; split; [reflexivity | fin_ok H1]
           | |- context [mk_op_f_c ?a ?b ?c ?d ?e] =>
               destruct (mk_op_f_c_ok a b c d e H) as (ch1 & -> & H1); exists ch1; split; [reflexivity | fin_ok H1]
           | |- context [mk_aluw_f_c ?a ?b ?c ?d ?e] =>
               destruct (mk_aluw_f_c_ok a b c d e H) as (ch1 & -> & H1); exists ch1; split; [reflexivity | fin_ok H1]
           | |- context [mk_opw_f_c ?a ?b ?c ?d ?e] =>
               destruct (mk_opw_f_c_ok a b c d e H) as (ch1 & -> & H1); exists ch1; split; [reflexivity | fin_ok H1]
           | |- context [mk_mdw_f_c ?a ?b ?c ?d ?e] =>
               destruct (mk_mdw_f_c_ok a b c d e H) as (ch1 & -> & H1); exists ch1; split; [reflexivity | fin_ok H1]
           end).
    all: try (keep_ok H).
    all: go_ok H.
  Qed.

  Fixpoint sym_run_c (fuel : nat) (cuts : list Z) (ch : pcache) (S : sstate) (first : bool)
    : option (list leaf) :=
    match fuel with
    | O => if first then None else Some [mkLeaf S RsFuel]
    | Datatypes.S fuel' =>
        if negb first && memZ (ss_pc S) cuts then Some [mkLeaf S RsCut]
        else
          let '(o, ch') := sym_step_c ch S in
          match o with
          | StNext S' => sym_run_c fuel' cuts ch' S' false
          | StFork S1 S2 =>
              match sym_run_c fuel' cuts (pc_init (ss_facts S1)) S1 false,
                    sym_run_c fuel' cuts (pc_init (ss_facts S2)) S2 false with
              | Some l1, Some l2 => Some (l1 ++ l2)
              | _, _ => None
              end
          | StStop r => if first then None else Some [mkLeaf S r]
          end
    end.

  Lemma sym_run_c_eq : ltac2:(tb__ "0|0|
S55S54S62A1S28S3S50S29R3S4R2A1A2Se0S53S54S6aA1A1S120R6R5R4R3R2A5S79Vsegs;R6R5R3R2A5A3F_;Ffirst;FS;Fch;Fcuts;Ffuel;").
  Proof.
    induction fuel as [|fuel IH]; intros cuts ch S first H; cbn [sym_run_c sym_run]; [reflexivity|].
    destruct (negb first && memZ (ss_pc S) cuts); [reflexivity|].
    destruct (sym_step_c_ok ch S H) as (ch' & -> & H').
    destruct (sym_step segs S) as [S'|S1 S2|r]; cbn [step_ok] in H'.
    - apply IH; exact H'.
    - rewrite (IH cuts (pc_init (ss_facts S1)) S1 false (pc_init_ok _)).
      rewrite (IH cuts (pc_init (ss_facts S2)) S2 false (pc_init_ok _)). reflexivity.
    - reflexivity.
  Qed.

  Definition sym_run_fast (fuel : nat) (cuts : list Z) (S : sstate) (first : bool) : option (list leaf) := ltac2:(tb__ "0|0|
S120Vfuel;Vcuts;S34S4VS;A1A1VS;Vfirst;A5").

  Theorem sym_run_fast_eq : ltac2:(tb__ "0|0|
S55S54S62A1S3S50Se0S53S54S6aA1A1S127R4R3R2R1A4S79Vsegs;R4R3R2R1A5A3Ffirst;FS;Fcuts;Ffuel;").
  Proof. intros. apply sym_run_c_eq. apply pc_init_ok. Qed.

  Theorem sym_step_c_eq : ltac2:(tb__ "0|0|
S28S3S29R2S4R1A1A2Se0S65S5cS65S28S123R3R2A2A3S9bVsegs;R2A2A3F_;FS;Fch;").
  Proof. intros ch S H. destruct (sym_step_c_ok ch S H) as (ch' & -> & _). reflexivity. Qed.

  Definition cleaf : Type := (leaf * pcache)%type.
  Definition cleaf_ok (lc : cleaf) : Prop := ltac2:(tb__ "0|0|
S29S5fS6aS28Vlc;A3S4Sb9S5cS6aS28Vlc;A3A1A1A2").

  Fixpoint sym_run_cl (fuel : nat) (cuts : list Z) (ch : pcache) (S : sstate) (first : bool)
    : option (list cleaf) :=
    match fuel with
    | O => if first then None else Some [(mkLeaf S RsFuel, ch)]
    | Datatypes.S fuel' =>
        if negb first && memZ (ss_pc S) cuts then Some [(mkLeaf S RsCut, ch)]
        else
          let '(o, ch') := sym_step_c ch S in
          match o with
          | StNext S' => sym_run_cl fuel' cuts ch' S' false
          | StFork S1 S2 =>
              match sym_run_cl fuel' cuts (pc_init (ss_facts S1)) S1 false,
                    sym_run_cl fuel' cuts (pc_init (ss_facts S2)) S2 false with
              | Some l1, Some l2 => Some (l1 ++ l2)
              | _, _ => None
              end
          | StStop r => if first then None else Some [(mkLeaf S r, ch)]
          end
    end.

  Definition omap_fst (r : option (list cleaf)) : option (list leaf) := ltac2:(tb__ "0|2|
S53S54S112A1M0A1S53S54S6aA1M1A1Lr;Vr;G0S57G1S131S51S6aS28A2S6aS5cS6aS28A2R1A4A2Ll;S59G1A1X53x2").
  Definition oall_ok (r : option (list cleaf)) : Prop := ltac2:(tb__ "0|1|
S53S54S112A1M0A1OLr;Vr;G0S130S112S119R1A3Ll;Se2X53x2").

  Lemma sym_run_cl_ok : ltac2:(tb__ "0|1|
S55S54S62A1S28S3S50S29R3S4R2A1A2Se1Se0S53S54S6aA1A1S11cS121R6R5R4R3R2A5M0A1S79Vsegs;R6R5R3R2A5A3S125G0A1A2F_;Ffirst;FS;Fch;Fcuts;Ffuel;").
  Proof.
    induction fuel as [|fuel IH]; intros cuts ch S first H; cbn [sym_run_cl sym_run].
    - destruct first; cbn; [split; [reflexivity | exact I]|].
      split; [reflexivity|]. constructor; [exact H | constructor].
    - destruct (negb first && memZ (ss_pc S) cuts).
      { cbn. split; [reflexivity|]. constructor; [exact H | constructor]. }
      destruct (sym_step_c_ok ch S H) as (ch' & -> & H').
      destruct (sym_step segs S) as [S'|S1 S2|r]; cbn [step_ok] in H'.
      + apply IH; exact H'.
      + destruct (IH cuts (pc_init (ss_facts S1)) S1 false (pc_init_ok _)) as [E1 O1].
        destruct (IH cuts (pc_init (ss_facts S2)) S2 false (pc_init_ok _)) as [E2 O2].
        rewrite <- E1, <- E2.
        destruct (sym_run_cl fuel cuts (pc_init (ss_facts S1)) S1 false) as [l1|]; [|split; [reflexivity | exact I]].
        destruct (sym_run_cl fuel cuts (pc_init (ss_facts S2)) S2 false) as [l2|]; [|split; [reflexivity | exact I]].
        cbn [omap_fst oall_ok] in *. split; [rewrite map_app; reflexivity | apply Forall_app; split; assumption].
      + destruct first; cbn; [split; [reflexivity | exact I]|].
        split; [reflexivity|]. constructor; [exact H | constructor].
  Qed.

  Definition sym_run_lc (fuel : nat) (cuts : list Z) (S : sstate) (first : bool) : option (list cleaf) := ltac2:(tb__ "0|0|
S121Vfuel;Vcuts;S34S4VS;A1A1VS;Vfirst;A5").

  Theorem sym_run_lc_eq : ltac2:(tb__ "0|0|
S55S54S62A1S3S50Se0S53S54S6aA1A1S11cS122R4R3R2R1A4A1S79Vsegs;R4R3R2R1A5A3Ffirst;FS;Fcuts;Ffuel;").
  Proof. intros. apply sym_run_cl_ok. apply pc_init_ok. Qed.

  Theorem sym_run_lc_ok : ltac2:(tb__ "0|1|
S55S54S62A1S3S50S54S112A1M0Se0S53G0A1S122R5R4R3R2A4S57G0R1A2A3S130S112S119R2A3F_;Fl;Ffirst;FS;Fcuts;Ffuel;").
  Proof.
    intros fuel cuts S first l E.
    pose proof (proj2 (sym_run_cl_ok fuel cuts (pc_init (ss_facts S)) S first (pc_init_ok _))) as O.
    unfold sym_run_lc in E. rewrite E in O. exact O.
  Qed.

End WithImage.

Ltac run_cast_fast segs f c S b r :=
  exact_no_check (@eq_trans (option (list leaf)) (sym_run segs f c S b) (sym_run_fast segs f c S b) r
                    (@eq_sym (option (list leaf)) (sym_run_fast segs f c S b) (sym_run segs f c S b)
                             (sym_run_fast_eq segs f c S b))
                    (@eq_refl (option (list leaf)) r <: sym_run_fast segs f c S b = r)).

Ltac run_cast :=
  lazymatch goal with
  | |- sym_run ?segs ?f ?c ?S ?b = ?r => run_cast_fast segs f c S b r
  | |- ?m = ?r =>
      first [ let m' := (eval cbv delta [m] in m) in
              lazymatch m' with
              | sym_run ?segs ?f ?c ?S ?b =>
                  exact_no_check (@eq_trans (option (list leaf)) m (sym_run_fast segs f c S b) r
                    (@eq_sym (option (list leaf)) (sym_run_fast segs f c S b) m (sym_run_fast_eq segs f c S b))
                    (@eq_refl (option (list leaf)) r <: sym_run_fast segs f c S b = r))
              end
            | vm_cast_no_check (@eq_refl _ r) ]
  end.

Ltac direct_cast Mf :=
  lazymatch goal with
  | |- sym_run ?segs ?f ?c ?S ?b = ?r =>
      exact_no_check (@eq_trans (option (list leaf)) (sym_run segs f c S b) Mf r
                        (@eq_sym (option (list leaf)) Mf (sym_run segs f c S b) (sym_run_fast_eq segs f c S b))
                        (@eq_refl (option (list leaf)) Mf <: Mf = r))
  end.

Ltac memo_cast M Mf :=
  lazymatch goal with
  | |- _ = ?r =>
      let body := (eval cbv delta [M] in M) in
      lazymatch body with
      | sym_run ?segs ?f ?c ?S ?b =>
          exact_no_check (@eq_trans (option (list leaf)) M Mf r
                            (@eq_sym (option (list leaf)) Mf M (sym_run_fast_eq segs f c S b))
                            (@eq_refl (option (list leaf)) Mf <: Mf = r))
      end
  end.
