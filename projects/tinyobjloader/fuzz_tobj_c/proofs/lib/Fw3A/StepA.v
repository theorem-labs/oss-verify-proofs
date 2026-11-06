(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sstate"; "sprop"; "sobj"; "ss_facts"; "SLit"; "ss_pc"; "cell"; "valuation"; "ss_next"; "SAlu"; "sv_below"; "eval"; "SVar"; "ob_dflt"; "odefault"; "SPUle"; "ss_objs"; "smatch"; "sv_eqb"; "holds"; "dflt_writable"; "is_arr"; "ob_cells"; "ss_lenient"; "c_val"; "sprop_below"; "sfcsr"; "mkCell"; "ob_base"; "ss_resv"; "SPEq"; "enc_bytes"; "soff"; "swf"; "c_width"; "ob_hi"; "ob_lo"; "obj_wf"; "outside_all"; "tfact"; "c_off"; "mkObj"; "obj_holds"; "agree_below"; "mem_match"; "DUnknown"; "DZero"; "oaddr"; "obj_hi_of"; "obj_lo_of"; "obj_range"; "rm"; "rom_ok"; "sprop_eqb"; "ss_fcsr"; "ss_fregs"; "ss_regs"; "SAluW"; "SExt"; "SLBytes"; "SMd"; "SMdW"; "SPAlign"; "mkSS"; "ro_clear"; "tf_eqb"; "@Corelib.Init.Datatypes"; "bool"; "option"; "prod"; "Some"; "list"; "true"; "false"; "andb"; "pair"; "None"; "nat"; "snd"; "cons"; "negb"; "fst"; "nil"; "sum"; "orb"; "app"; "length"; "@Corelib.Init.Logic"; "eq"; "and"; "or"; "True"; "ex"; "not"; "False"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "step_out"; "set_pc"; "get_reg"; "StNext"; "set_reg"; "immI"; "instr_at"; "stop_reason"; "align_sv"; "mk_addk"; "fresh"; "sym_step"; "set_objs"; "rel_offset"; "list_upd"; "mk_alu"; "is_lit"; "load_res"; "msz"; "LROk"; "list_set"; "cell_rel"; "crel"; "fdig"; "amo_k"; "amo_log"; "ctx0"; "find_obj"; "sym_load"; "sym_store"; "CDisj"; "CLit"; "StStop"; "lit_overlaps"; "mk_dig"; "mk_slt_f"; "zmod64"; "RsMem"; "RsUnsupported"; "StFork"; "add_fact"; "addr_aligned"; "load_arr"; "load_dflt"; "load_fresh"; "obj_store"; "obj_store_d"; "set_freg"; "set_resv"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast"; "pcache"; "pc_ok"; "pc_u0"; "pc_init"; "force_ud"; "step_ok"; "cres"; "pc_0"; "pc_ud"; "find_obj_c"; "force_d"; "get_d"; "set_u0"; "sym_step_c"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "gdesc"; "prov"; "puleq"; "exts"; "ax_base"; "ax_X"; "g8"; "lift_out"; "step_outA"; "goff"; "mk_prov"; "obj_ext"; "pv_facts"; "granule_of"; "obj_store_z"; "axwf"; "list_eqb"; "find_granule"; "find_xr"; "amo_sv"; "ax_setS"; "is_zero_lit"; "xr_eqb"; "GVar"; "andm8_step"; "has_facts"; "lift_out_j"; "q8_of"; "r1_step"; "r3_out"; "r3_step"; "r3w_step"; "r3x_step"; "split_gk"; "store_cells_z"; "xr_rel_hit"; "F8"; "FE"; "GExact"; "amo_step"; "andm8_sh_step"; "divpow2_step"; "find_granule_eq"; "find_xr_d"; "granule_eq_ok"; "granule_expr"; "granule_ok"; "leafA"; "mkProv"; "r2_step"; "r3w_target"; "split_lit"; "sym_runA_ref"; "sym_stepA"; "word_byte"; "xb_facts"; "xr_ok"; "xr_sub_pv"; "xr_subst"; "zst_step"; "JOIN_FUEL"; "StNextA"; "StStopA"; "amo_alignedb"; "base_aligned8"; "cell_eqb"; "dflt_eqb"; "join2"; "mk_prov_f"; "or_else"; "osv_eqb"; "pv_c0"; "pv_dg"; "pv_u0"; "pv_ud"; "sfcsr_eqb"; "shadow_addr"; "shadow_ok"; "sobj_eqb"; "try_join"; "word_ok"; "xr_below"; "xr_covered"; "xrs_covered_f"; "zz_eqb"; "F3";
"FA"; "GFloor"; "GFloorK"; "GLit"; "StForkA"; "StJoinA"; "blk64_hi_ok"; "blk64_lo_ok"; "blk64_ok"; "e64_of"; "entailsA"; "entailsA_ref"; "fa_target_in"; "find_xr_lit"; "mkAX"; "pow2_log"; "r3w_lit_hit"; "run_past_branch"; "run_to_pc"; "sym_runA"; "x_related"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "pow"; "modulo"; "mul"; "eqb"; "lt"; "leb"; "sub"; "div"; "ltb"; "opp"; "to_nat"; "of_nat"; "log2"; "max"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV"; "U"; "@LinuxProcessSemantics.Riscv.Instr"; "aluop"; "instr"; "ALU_ADD"; "msize"; "mulop"; "ffmt"; "awidth"; "amoop"; "ALU_SRL"; "ALU_AND"; "csrop"; "fcvt_ty"; "Load"; "ALU_SUB"; "OpImm"; "ShiftImm"; "branch_cond"; "fariop"; "fcmpop"; "fmaop"; "fminmaxop"; "fmvdir"; "fsgnop"; "SZ1"; "Store"; "AD"; "ALU_OR"; "ALU_SLL"; "ALU_XOR"; "AW"; "Amo"; "Mul"; "SZ8"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI"; "next_rel"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "ms_mem"; "ms_rom"; "write_to_mem"; "ov_read_bytes"; "store_ok"; "@Stdlib.Lists.List"; "In"; "forallb"; "existsb"; "nth_error"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA.Exts"; "exts_kept"; "shape_kept"; "stepA_kept"; "stepA_inv"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "repeat"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymQFast"; "u2memo"; "mk_u2"; "u2_ok"; "uleq_d_o"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA.RSound"; "pv_ok"; "gdesc_sem"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "add_facts"; "existsb_lazy"; "forallb_lazy"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA.StepAFast"; "rres"; "prov_c"; "obj_store_z_c"; "granule_pre"; "is_zero_lit_h"; "rekey"; "stepA_ok"; "andm8_step_c"; "andm8_step_pv"; "facts_eqb"; "force_u0"; "r1_step_c"; "r1_step_pv"; "r2_step_c"; "r2_step_pv"; "r3_step_c"; "r3_step_pv"; "r3w_step_c"; "r3w_step_pv"; "r3x_step_c"; "r3x_step_pv"; "store_cells_z_c"; "zst_step_c"; "sym_runA_fast"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA.StepAFast.WithImage"; "or_else_c"; "dflt_c"; "ruleA"; "sres"; "run_past_branch_c"; "run_to_pc_c"; "sym_runA_c"; "x_related_l"; "sym_runA_fast"; "sym_stepA_c"; "try_join_c"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA.Build"; "or_else"; "obj_store_z"; "q8_of"; "JOIN_FUEL"; "base_aligned8"; "blk64_hi_ok"; "blk64_lo_ok"; "find_xr_d"; "r3_out"; "FA"; "amo_alignedb"; "amo_step"; "andm8_sh_step"; "andm8_step"; "blk64_ok"; "divpow2_step"; "e64_of"; "fa_target"; "fa_target_in"; "find_xr_lit"; "is_zero_lit"; "join2"; "join_regs"; "pow2_log"; "r1_step"; "r2_step"; "r3_step"; "r3w_lit_hit"; "r3w_step"; "r3w_target"; "r3w_target2"; "r3x_step"; "run_past_branch"; "run_to_pc"; "shadow_offset_like"; "store_cells_z"; "x_related"; "xb_facts"; "zst_step"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "sv_subst"; "wsub"; "@Stdlib.PArith.BinPos.Pos"; "le"; "lt"; "max"; "succ"; "add"; "eqb"; "@Corelib.Init.Peano";
"lt"; "@LinuxProcessSemantics.Riscv.Sem"; "alu64"; "amo_val"; "amo_aligned"; "low32"; "@LinuxProcessSemantics.LinuxProcessSem.BvBase"; "Z_to_le_bytes"; "bytes_le_to_Z"; "le_bytes_to_word"; "@LinuxProcessSemantics.Riscv.Prelude"; "sext"; "zext"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundF"; "ext1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL"; "dg_ok"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "@LinuxProcessSemantics.LinuxProcessSem.MemImageType"; "Segment"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "entails"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.DigFastA"; "force_d_f"; "mk_dig_f"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.EntailFast"; "entails_f"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PArith.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SpecBridge SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundW SymSoundF SymSoundR SymFrame SymEntail SymCFG SymDigFast SymQFast SymStepFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.EntailFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.DigFastA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Record axst := mkAX {
  ax_S : sstate;
  ax_X : list (sv * sv);
  ax_base : sv
}.

Definition ax_setS (A : axst) (S : sstate) : axst := ltac2:(tb__ "0|0|
S109VS;SaaVA;A1Sa9VA;A1A3").

Definition xr_below (n : positive) (r : sv * sv) : bool := ltac2:(tb__ "0|0|
S4aSbVn;S51S0S0Vr;A3A2SbVn;S4eS0S0Vr;A3A2A2").
Definition axwf (A : axst) : bool := ltac2:(tb__ "0|1|
S4aS14aS45S0S0A2Sf6S9Sa3VA;A1A1M0A1SaaVA;A1A3SbG0Sa9VA;A1A2A2").

Inductive step_outA :=
| StNextA (A' : axst)
| StForkA (A1 A2 : axst)
| StJoinA (A1 A2 : axst)
| StStopA (r : stop_reason).

Record leafA := mkLeafA { la_state : axst; la_reason : stop_reason }.

Definition lift_out (A : axst) (o : step_out) : step_outA := ltac2:(tb__ "0|1|
S61SadLo;Vo;S1Se2Sb9VA;R1A2M0A1LS';S1S1SffSb9VA;R2A2G0A2LS2;LS1;S68Se3R1A1Lr;X61x3").

Definition lift_out_j (A : axst) (o : step_out) : step_outA := ltac2:(tb__ "0|1|
S61SadLo;Vo;S1Se2Sb9VA;R1A2M0A1LS';S1S1S100Sb9VA;R2A2G0A2LS2;LS1;S68Se3R1A1Lr;X61x3").

Definition xr_subst (s : wsub) (r : sv * sv) : sv * sv := ltac2:(tb__ "0|0|
S4bS0S0S1acVs;S51S0S0Vr;A3A2S1acVs;S4eS0S0Vr;A3A2A4").
Definition xr_eqb (a b : sv * sv) : bool := ltac2:(tb__ "0|0|
S4aS13S51S0S0Va;A3S51S0S0Vb;A3A2S13S4eS0S0Va;A3S4eS0S0Vb;A3A2A2").

Definition amo_sv (op : amoop) (wd : awidth) (old src : sv) : option sv := ltac2:(tb__ "0|3|
S128S44S0A1M0Lop;Vop;S46S0Vsrc;A2S46S0SaS123Vold;Vsrc;A3A2S127G0Lwd;M1Vwd;S4cS0A1M2S46S0SaS13dVold;Vsrc;A3A2X127x2G1Vwd;G2S46S0SaS12aVold;Vsrc;A3A2X127x2G1Vwd;G2S46S0SaS13bVold;Vsrc;A3A2X127x2G2G2G2G2X128x9").

Definition g8 (g : positive) : sv := ltac2:(tb__ "0|0|
SaS13cSdVg;A1S5Z3A1A3").

Definition F8 (g : positive) (e : sv) : list sprop := ltac2:(tb__ "0|1|
S4fS2S10SabVg;A1M0Ve;A2S4fS2S10Ve;SaS123G0S5Z7A1A3A2S4fS2S10SdVg;A1S5S118S112Z2Z3dA2Z1A2A1A2S52S2A1A3A3A3").

Definition FE (g : positive) (e0 : sv) : list sprop := ltac2:(tb__ "0|1|
S4fS2S1fSabVg;A1M0Ve0;A2S4fS2S10SdVg;A1S5S118S112Z2Z3dA2Z1A2A1A2S4fS2S10G0Ve0;A2S4fS2S10Ve0;G0A2S52S2A1A3A3A3A3").

Record prov := mkProv { pv_facts : list sprop; pv_c0 : fdig; pv_dg : fdig; pv_u0 : option u2memo; pv_ud : option u2memo }.
Definition mk_prov (facts : list sprop) : prov := ltac2:(tb__ "0|0|
S7bVfacts;A1S78S83Vfacts;A1S78Sd5Vfacts;R2R1S46S159S15aR2A1A2S46S159S15aR1A1A2A5Tdg;Tc0;").
Definition puleq (pv : prov) (a : sv) (k : Z) (b : sv) : bool := ltac2:(tb__ "0|0|
S43S43L_;S15cSeeVpv;A1SecVpv;A1Va;Vk;Vb;A5S48S15cSefVpv;A1SedVpv;A1Va;Vk;Vb;A5X43x2").

Definition has_facts (fs : list sprop) (facts : list sprop) : bool := ltac2:(tb__ "0|0|
S14aS2S2S14bS2S36R1A1Vfacts;A3Lf;Vfs;A3").

Definition granule_ok (pv : prov) (g : positive) (e : sv) : bool := ltac2:(tb__ "0|3|
S43S43L_;M0SbeSc9Vg;Ve;A2Sb1Vpv;A1A2S48G0G0Sa7Vpv;SabVg;A1M1Z0M2Ve;A4Sa7Vpv;Ve;G2SaS123G1S5Z7A1A3A4S49X43x2Sa7Vpv;SdVg;A1G2S5S118S112Z2Z3dA2Z1A2A1A4S49X43x2X43x2").

Definition granule_eq_ok (pv : prov) (g : positive) (e0 : sv) : bool := ltac2:(tb__ "0|0|
S43S43L_;SbeScaVg;Ve0;A2Sb1Vpv;A1A2S48Sa7Vpv;SdVg;A1Z0S5S118S112Z2Z3dA2Z1A2A1A4X43x2").

Definition xr_sub_pv (pv : prov) (r' r : sv * sv) : bool := ltac2:(tb__ "0|7|
SaS123S51S0S0Vr';A3M0S4eS0S0Vr';A3M1A3S0SaS123S51S0S0Vr;A3M2S4eS0S0Vr;A3A3S0S43S43L_;M3S117Z3M4S69Sb1Vpv;A1M5G0A2A2G3Sa7Vpv;G2Z0M6G0A4G3Sa7Vpv;G0G6R2A4G3Sa7Vpv;R2G6R1A4G3S117G4S69G5G1A2A2S48Sa7Vpv;R1G6R2A4X43x2S49X43x2S49X43x2S49X43x2S49X43x2Te;Te';").
Definition xr_sub (facts : list sprop) (r' r : sv * sv) : bool := ltac2:(tb__ "0|0|
SdeSafVfacts;A1Vr';Vr;A3").
Definition xr_covered (facts : list sprop) (X : list (sv * sv)) (r' : sv * sv) : bool := ltac2:(tb__ "0|1|
S43S43L_;S14bS45S0S0A2M0SbbVr';A1VX;A3S48S14bG0SdeSafVfacts;A1Vr';A2VX;A3X43x2").

Definition entailsA_ref (L T : axst) (s : wsub) : bool := ltac2:(tb__ "0|2|
S4aS4aS4aS1c2Sa3VL;A1M0Sa3VT;A1Vs;A3S14aS45S0S0A2M1G1Sf7S4G0A1SaaVL;A1SdfVs;R1A2A3Lr;SaaVT;A1A3A2S13S1acVs;Sa9VT;A1A2Sa9VL;A1A2A2Sb4VT;A1A2").

Definition mk_prov_f (facts : list sprop) : prov := ltac2:(tb__ "0|0|
S7bVfacts;A1S78S1c4Vfacts;A1S78Sd5Vfacts;R2R1S46S159S15aR2A1A2S46S159S15aR1A1A2A5Tdg;Tc0;").
Lemma mk_prov_f_eq : ltac2:(tb__ "0|0|
S47S2A1S57Sa6Se9R1A1SafR1A1A3Ffacts;").
Proof. intros facts. unfold mk_prov_f, mk_prov. rewrite DigFastA.mk_dig_f_eq. reflexivity. Qed.
Definition xrs_covered_f (facts : list sprop) (XL : list (sv * sv)) (s : wsub) (XT : list (sv * sv)) : bool := ltac2:(tb__ "0|4|
S43S43L_;M0S161S45S0S0A2M1G1S160G1SbbSdfVs;R1A2M2A1VXL;A3M3Lr;VXT;A3S48Se9Vfacts;A1Sa6S161G1G1G0G3S48S160G1SdeR2G2A2VXL;A3X43x2Lr;VXT;A3Tpv;X43x2").
Lemma xrs_covered_f_eq : ltac2:(tb__ "0|2|
S47S2A1S47S45S0S0A2M0A1M1S1adG1S57S43Sf8R4R3R2R1A4S14aG0G0Sf7R5R4SdfR3R1A2A3Lr;R1A3A3FXT;Fs;FXL;Ffacts;").
Proof.
  intros facts XL s XT. unfold xrs_covered_f. cbv zeta. rewrite mk_prov_f_eq.
  assert (E : forallb_lazy (fun r => if existsb_lazy (xr_eqb (xr_subst s r)) XL then true else existsb_lazy (xr_sub_pv (mk_prov facts) (xr_subst s r)) XL) XT
              = forallb (fun r => xr_covered facts XL (xr_subst s r)) XT).
  { rewrite forallb_lazy_eq. induction XT as [|r t IH]; cbn [forallb]; [reflexivity|]. rewrite IH. unfold xr_covered. rewrite !existsb_lazy_eq. reflexivity. }
  rewrite E. destruct (forallb_lazy (fun r => existsb_lazy (xr_eqb (xr_subst s r)) XL) XT) eqn:Z; [|reflexivity].
  symmetry. rewrite forallb_lazy_eq in Z. rewrite forallb_forall in Z. apply forallb_forall. intros r Hr.
  specialize (Z r Hr). rewrite existsb_lazy_eq in Z. unfold xr_covered. rewrite Z. reflexivity.
Qed.
Definition entailsA (L T : axst) (s : wsub) : bool := ltac2:(tb__ "0|2|
S43S43L_;M0S1c5Sa3VL;A1M1Sa3VT;A1Vs;A3G0Sf8S4G1A1SaaVL;A1Vs;SaaVT;A1A4G0S13S1acVs;Sa9VT;A1A2Sa9VL;A1A2Sb4VT;A1S49X43x2S49X43x2S49X43x2").
Lemma entailsA_ref_eq : ltac2:(tb__ "0|0|
Sa4Sa4S1adS57S43S105R3R2R1A3S106R3R2R1A3A3Fs;FT;FL;").
Proof.
  intros L T s. unfold entailsA, entailsA_ref. rewrite EntailFast.entails_f_eq, xrs_covered_f_eq.
  destruct (entails (ax_S L) (ax_S T) s); [|reflexivity]. cbn [andb].
  destruct (forallb (fun r => xr_covered (ss_facts (ax_S L)) (ax_X L) (xr_subst s r)) (ax_X T)); [|reflexivity]. cbn [andb].
  destruct (sv_eqb (sv_subst s (ax_base T)) (ax_base L)); reflexivity.
Qed.

Definition split_lit (e : sv) : sv * Z := ltac2:(tb__ "0|a|
S0S45S0S5eA2M0Le;Ve;S5eS4bS0S5eVe;Z0A4M1Lz;S5fG1Li;M2S121S0S0S121G0Lop;R3S0G0Lb;R1S5eS4bS0S5eR3R1A4Lc;G2S121S0S0G1Lb0;La;M3Lop0;M4G4S125G3Lop0;M5G5S43S60S0G1La;Lw;Lsgn;M6S5fS0S5eG1Lk;Li;Ll;M7X0x8G1G1G1G1G1G1G1G1G1X121xaLb;Le0;Lop;S121S0S0G1Lb;La;M8Lop;S125G8Lop;M9G9G6G7X0x8").

Fixpoint find_granule (pv : prov) (facts : list sprop) (e : sv) : option positive :=
  match facts with
  | [] => None
  | SPUle (SAlu ALU_SLL (SVar g) (SLit 3)) e' :: rest =>
      if sv_eqb e' e &&& granule_ok pv g e then Some g else find_granule pv rest e
  | _ :: rest => find_granule pv rest e
  end.

Fixpoint find_granule_eq (pv : prov) (facts : list sprop) (e0 : sv) : option positive :=
  match facts with
  | [] => None
  | SPEq (SAlu ALU_SLL (SVar g) (SLit 3)) e' :: rest =>
      if sv_eqb e' e0 &&& granule_eq_ok pv g e0 then Some g else find_granule_eq pv rest e0
  | _ :: rest => find_granule_eq pv rest e0
  end.

Fixpoint granule_expr (pv : prov) (facts : list sprop) (g : positive) : option (sv + sv) :=
  match facts with
  | [] => None
  | SPUle (SAlu ALU_SLL (SVar g') (SLit 3)) e :: rest =>
      if Pos.eqb g' g &&& granule_ok pv g e then Some (inl e) else granule_expr pv rest g
  | SPEq (SAlu ALU_SLL (SVar g') (SLit 3)) e0 :: rest =>
      if Pos.eqb g' g &&& granule_eq_ok pv g e0 then Some (inr e0) else granule_expr pv rest g
  | _ :: rest => granule_expr pv rest g
  end.

Inductive goff := GVar (g : positive) (k : Z) | GLit (q : Z).

Definition split_gk (off : sv) : option goff := ltac2:(tb__ "0|a|
S0S44SaeA1M0Loff;Voff;S5eS46SaeSfeR1A1A2Lq;S5fS46SaeSbcR1Z0A2A2Lg;S121S0S0S121G0Lop;R3S0G0La;R2S5eS0G0Lb;M1R2S5eS4cSaeA1M2Lz;S5fS46SaeSbcR1R2A2A2Lg;S121S0S0G2Lb0;La0;M3Lop0;M4G4S125G3Lop0;M5G5S43S60S0G2La0;Lw;Lsgn;M6S5fS0S5eG2Lk0;Li;Ll;X0x8Lk;S5fG1R2S5eS46SaeSbcR2R1A2A2Lk;S5fG2Li;G4G4G5G5G6S5fS0S5eG2Lk;Li;Ll;M7X0x8Lg;G4G4G5G5G6G7X0x8G2G2G2G2G2G2G2G2G2X121xaLb;La;Lop;S121S0S0G2Lb;La;M8Lop;S125G8Lop;M9G9S43S60S0G2La;Lw;Lsgn;G7X0x8").

Inductive gdesc := GExact (q8 : sv) | GFloor (g : positive) (e : sv) | GFloorK (g : positive) (e : sv) (k : Z).

Definition granule_of (pv : prov) (off : sv) : option gdesc := ltac2:(tb__ "0|d|
S44SaeA1S44Sa5A1M0Lx;Sc6Voff;A1SaeSaeG0Lg0;R1S5fS5eS43G0L_;M1S50S4aS117Z0M2R1A2M3S11aR1S112Z2M4Z28A2A2A2A1S4cSa5A1M5S44S53S0S0A2M6A1G0Lx;Sd2Vpv;Sb1Vpv;A1R2A3G6G6G0Ls;R1S0G1S115R3G2A2S46Sa5SfcR4R1A2A2G1Sa7Vpv;R1S114Z8M7R3A2M8S5S118S112G4Z40A2Z1M9A2A1MaA4S46Sa5SfdR4R1R3A3A2G5X43x2X43x2Le;S0G1Sa7Vpv;R1S110G8Z7A2GaA4S46Sa5ScbS70S123R1S5G8A1A3A1A2G5X43x2Le0;X53x2Ls;G1Sa7Vpv;SdR2A1R1S5S118S112G4Z3dA2MbG9A2A1A4S46Sa5ScbS70S123SabR2A1S5S114G7R1A2A1McA3A1A2G5X43x2X44x2X43x2Lk;Lg;S5eG1S4aG3S11aR1GbA2A2S46Sa5ScbGcA1A2G5X43x2Lq;Xaex2Lg0;G5X44x2").

Definition xr_rel_hit (pv : prov) (b l e : sv) (d : Z) : bool := ltac2:(tb__ "0|3|
S44S0A1S43Lx;S6eVb;Ve;A2S0S43S43L_;M0S117Z0M1Vd;A2G0Sa7Vpv;R1S110Vd;Z1M2A2Vl;A4Sa7Vpv;Vl;G1SaS12eS5S118S112Z2Z40A2G2A2A1Vb;A3A4S49X43x2S49X43x2Loff;S49X44x2").

Fixpoint find_xr (pv : prov) (X : list (sv * sv)) (e : sv) (d : Z) : option (sv * sv) :=
  match X with
  | [] => None
  | (b, l) :: rest =>
      if (puleq pv b (- d) e &&& puleq pv e (d + 1) (SAlu ALU_ADD b l)) ||| xr_rel_hit pv b l e d
      then Some (b, l) else find_xr pv rest e d
  end.

Definition F3 (q8 b l : sv) (v : positive) : list sprop := ltac2:(tb__ "0|1|
S4fS2S1fSaS123Vq8;SdVv;A1M0A3SaS123Vb;Vl;A3A2S4fS2S10S5Z1A1G0A2S4fS2S10G0S5Z7A1A2S52S2A1A3A3A3").

Fixpoint list_eqb {T : Type} (eqb : T -> T -> bool) (l1 l2 : list T) : bool :=
  match l1, l2 with
  | [], [] => true
  | a :: t1, b :: t2 => eqb a b && list_eqb eqb t1 t2
  | _, _ => false
  end.

Lemma list_eqb_sound : forall {T : Type} (eqb : T -> T -> bool),
  (forall a b, eqb a b = true -> a = b) ->
  forall l1 l2, list_eqb eqb l1 l2 = true -> l1 = l2.
Proof.
  intros T eqb Hs. induction l1 as [|a t IH]; intros [|b t2] H; cbn in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H1 H2]. rewrite (Hs _ _ H1), (IH _ H2). reflexivity.
Qed.

Definition zz_eqb (a b : Z * Z) : bool := ltac2:(tb__ "0|0|
S4aS115S51S5eS5eVa;A3S51S5eS5eVb;A3A2S115S4eS5eS5eVa;A3S4eS5eS5eVb;A3A2A2").
Lemma zz_eqb_sound : ltac2:(tb__ "0|1|
S45S5eS5eA2M0G0S57S43Sf9R2R1A2S48A3S57G0R3R2A3F_;Fb;Fa;").
Proof. intros [a1 a2] [b1 b2] H. unfold zz_eqb in H. cbn in H. apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. subst. reflexivity. Qed.

Definition cell_eqb (c d : cell) : bool := ltac2:(tb__ "0|0|
S4aS4aS13S29Vc;A1S29Vd;A1A2S115S23Vc;A1S23Vd;A1A2A2S13S19Vc;A1S19Vd;A1A2A2").
Lemma cell_eqb_sound : ltac2:(tb__ "0|0|
S7S7S57S43Se6R2R1A2S48A3S57S7R3R2A3F_;Fd;Fc;").
Proof.
  intros [o w v] [o' w' v'] H. unfold cell_eqb in H. cbn in H.
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply sv_eqb_sound in H1. apply Z.eqb_eq in H2. apply sv_eqb_sound in H3. subst. reflexivity.
Qed.

Definition dflt_eqb (d e : odefault) : bool := ltac2:(tb__ "0|8|
SfS43Ld;Vd;SfS43Le;M0Ve;S48S49S49S5fS49Ll;M1G1S5eS0S47S45S5eS5eA2M2A1M3S47S28A1M4S49Ltmpl;Lflds;Lcnt;Lesz;M5Xfx6G0Ve;S49S48S49G1G1G5Xfx6G0Ve;S49S49S48G1G1G5Xfx6S5fG0Ve;S49S49S49S5fS1b3R2R1A2Ll';M6S5fS49Ll0;M7G5Xfx6Ll;S5fG0Ve;S49S49S49G7G6G5Xfx6Ll;S5eS0G3G4G0Ve;S49S49S49G1G1S5eS0G3G4S4aS4aS4aS115R8R4A2S13R7R3A2A2Sb5G2Sf9R6R2A4A2Sb5S28S42R5R1A4A2Lt';Lf';Lc';Lz';Xfx6Lt;Lf;Lc;Lz;Xfx6").
Lemma dflt_eqb_sound : ltac2:(tb__ "0|0|
SfSfS57S43Se7R2R1A2S48A3S57SfR3R2A3F_;Fe;Fd;").
Proof.
  intros d e H. destruct d, e; cbn in H; try discriminate; try reflexivity;
    try (apply Pos.eqb_eq in H; subst; reflexivity).
  apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.eqb_eq in H1. apply sv_eqb_sound in H2.
  apply (list_eqb_sound zz_eqb zz_eqb_sound) in H3. apply (list_eqb_sound tf_eqb tf_eqb_sound) in H4.
  subst. reflexivity.
Qed.

Definition sobj_eqb (o o' : sobj) : bool := ltac2:(tb__ "0|0|
S4aS4aS4aS4aS13S1dVo;A1S1dVo';A1A2S13S25Vo;A1S25Vo';A1A2A2S13S24Vo;A1S24Vo';A1A2A2Sb5S7Se6S17Vo;A1S17Vo';A1A4A2Se7SeVo;A1SeVo';A1A2A2").
Lemma sobj_eqb_sound : ltac2:(tb__ "0|0|
S3S3S57S43Sf3R2R1A2S48A3S57S3R3R2A3F_;Fo';Fo;").
Proof.
  intros [b lo hi cs d] [b' lo' hi' cs' d'] H. unfold sobj_eqb in H. cbn in H.
  apply andb_prop in H as [H H5]. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply sv_eqb_sound in H1. apply sv_eqb_sound in H2. apply sv_eqb_sound in H3.
  apply (list_eqb_sound cell_eqb cell_eqb_sound) in H4. apply dflt_eqb_sound in H5. subst. reflexivity.
Qed.

Definition sfcsr_eqb (a b : sfcsr) : bool := ltac2:(tb__ "0|1|
S1bS43La;Va;S1bS43Lb;M0Vb;S48S0S49Lv;X1bx2S0G0Vb;S49S0S13R2R1A2Lv;X1bx2Lu;X1bx2").
Lemma sfcsr_eqb_sound : ltac2:(tb__ "0|0|
S1bS1bS57S43Sf0R2R1A2S48A3S57S1bR3R2A3F_;Fb;Fa;").
Proof. intros [|u] [|v] H; cbn in H; try discriminate; [reflexivity|]. apply sv_eqb_sound in H. subst. reflexivity. Qed.

Definition osv_eqb (a b : option sv) : bool := ltac2:(tb__ "0|2|
S44S0A1M0S43La;Va;S0G0S43Lb;M1Vb;S0S13R2R1A2Lv;S49X44x2Lu;G1Vb;S0S49Ls;S48X44x2X44x2").
Lemma osv_eqb_sound : ltac2:(tb__ "0|1|
S44S0A1M0G0S57S43SebR2R1A2S48A3S57G0R3R2A3F_;Fb;Fa;").
Proof. intros [u|] [v|] H; cbn in H; try discriminate; [|reflexivity]. apply sv_eqb_sound in H. subst. reflexivity. Qed.

Lemma xr_eqb_sound : ltac2:(tb__ "0|1|
S45S0S0A2M0G0S57S43SbbR2R1A2S48A3S57G0R3R2A3F_;Fb;Fa;").
Proof.
  intros [a1 a2] [b1 b2] H. unfold xr_eqb in H. cbn in H. apply andb_prop in H as [H1 H2].
  apply sv_eqb_sound in H1. apply sv_eqb_sound in H2. subst. reflexivity.
Qed.

Section Build.
  Variable segs : list Segment.

  Definition amo_alignedb (facts : list sprop) (ae : sv) (a : Z) : bool := ltac2:(tb__ "0|0|
S43S43L_;S8aVfacts;Vae;Va;A3S48S4aS117Z0Va;A2S117Va;S69Vfacts;Vae;A2A2A2X43x2").

  Definition amo_step (S : sstate) (op : amoop) (wd : awidth) (rd rs1 rs2 : reg) : step_out := ltac2:(tb__ "0|4|
S6VS;A1S5eS63VS;Vrs1;A2S0S43S61L_;S50S18fS4VS;A1R1S7aVwd;A1A3A1S81S87A1M0S44S0A1S61Lx;M1S1eVS;A1S0G0Ls;S72S61Lx;S7dVsegs;VS;R1S79Vwd;A1M2S48A5S0S1G1Sb8Vop;Vwd;R2S63VS;Vrs2;A2A4S0S44S1A1S61Lx;S7eR2R4G2R1A4S1S64S62S65R1Vrd;R4A3S110R6Z4A2A2A1LS2;S81S86A1M3X44x2Lnv;G0X44x2LS1;Lv;G3X72x2X44x2X43x2Tae;Tpc;").

  Definition r1_step (S : sstate) (rd rs1 : reg) : option step_out := ltac2:(tb__ "0|d|
S6VS;A1S5eS4VS;A1S47S2A1S63VS;Vrs1;A2S0S43S44S61A1M0L_;M1S71R1A1S4cS61A1SafR2A1Sa6S45S0S5eA2G0Lx;Sd8R2A1S0S5eG1S43S43L_;S4aS4aS117Z0M2R1A2S11aR1S112Z2M3Z28A2A2A2S117Z3S69R5R2A2A2A2Sa7R3R2R1S5S118S112G3Z40A2Z1A2A1A4S49X43x2S5fS43S0L_;S115S119R2Z8A2M4G2A2SdR1A1M5SaS123G5S5G4A1A3X43x2Lg;S5fS0Fg;S44S5fA1G0Lx;M6ScfR4R6R3A3S5fS46S61S64S62S65VS;Vrd;R2R1A1M7A3S110R8Z4M8A2M9A2A1A2Lg;S9VS;A1MaS5fS46S61S64S62S65S15fScaR1R4A2S4eS0S1S6bVS;A1A3MbA2Vrd;G7A3G9A2A1A2Tg;X44x2Tmk;G6Sb6R3R5R4A3S5fS46S61S64S62S65VS;Vrd;G5A3S110R7G8A2McA2A1A2Lg;GaS5fS46S61S64S62S65S15fSc9R1R5A2GbA2Vrd;G5A3GcA2A1A2Tg;X44x2X43x2Lc;Le0;X45x1Tpv;X43x2Te;Tfacts;Tpc;").

  Definition r2_step (S : sstate) (rd rs1 : reg) : option step_out := ltac2:(tb__ "0|1|
S6VS;A1S5eS63VS;Vrs1;A2S0S44S5fA1S44S61A1Lx;Sb6SafS4VS;A1M0A1G0R1A3S5fS46S61S64S62S65VS;Vrd;SaS12eR2SabR1A1A3A3S110R3Z4A2A2A1A2Lg;S4cS61A1X44x2Te;Tpc;").

  Fixpoint xb_facts (pv : prov) (X : list (sv * sv)) (e v : sv) : list sprop :=
    match X with
    | [] => []
    | (b, _) :: rest =>
        if (3 <=? align_sv (pv_facts pv) b) &&& puleq pv b 0 e
        then SPUle b v :: xb_facts pv rest e v else xb_facts pv rest e v
    end.

  Definition andm8_step (A : axst) (rd rs1 : reg) (imm : bv 12) : option step_out := ltac2:(tb__ "0|4|
Sa3VA;A1S1S63R1Vrs1;A2S0S43S44S61A1L_;M0S54S71R1A1S115S93Q5Vrd;A2Z0A2A2S4cS61A1M1SafS4R2A1A1Sa6G0Sa7R1R2Z7M2S5S118S112Z2Z40A2M3Z1A2A1A4S84S4R3A1S12aR2S5S113S66Vimm;A1G3A2A1A4S0S46S61S64S15fS55S2S4fS2S10R1R3A2S4fS2S10R3SaS123R1S5G2A1A3A2S52S2A1A3A3S1aaR2SaaVA;A1R3R1A4A3S62S65R4Vrd;R1A3S110S6R4A1Z4A2A2A2A1A2Tv;G1X43x2Tpv;X43x2Te;TS;").

  Definition FA (g' : positive) (t : sv) : list sprop := ltac2:(tb__ "0|1|
S4fS2S10SdVg';A1M0Vt;A2S4fS2S10Vt;SaS123G0S5Z7A1A3A2S4fS2S3fVg';Z3A2S52S2A1A3A3A3").

  Definition shadow_offset_like (t : sv) : bool := ltac2:(tb__ "0|0|
S44SaeA1S43Lx;Sc6Vt;A1SaeSaeS43Lg;R1S5fS5eS4aS117Z0R1A2S11aR1S112Z2Z28A2A2A2Lk;Lg0;S5eS49Lq;Xaex2Lg;S49X44x2").

  Definition andm8_sh_step (A : axst) (rd rs1 : reg) : option step_out := ltac2:(tb__ "0|8|
Sa3VA;A1S1S63R1Vrs1;A2S0S43S44S61A1M0L_;M1S115S93Q5Vrd;A2Z0M2A2S4cS61A1M3S0G0Lx;Sa9VA;A1M4S5eG1S50S115S113R1Z8A2G2A2A1G3S44S0A1G0Lx;S6eG4R2A2S0G1S54S71R1A1S50S1a7R1A1A1A2G3S9R4A1S5fS46S61S64S62S65S15fS18eR1R2A2S4eS0S1S6bR5A1A3A2Vrd;S70S123SdR1A1S5R3A1A3A3S110S6R5A1Z4A2A2A1A2Tg';X43x2Lt;G3X44x2X43x2Lb;S5fG3Li;S121S0S0G3Lb;La;M5Lop;M6G6S125G5Lop;M7G7S43S60S0G3La;Lw;Lsgn;S5fS0S5eG3Lk;Li;Ll;X0x8X43x2Te;TS;").

  Definition r3_out (S : sstate) (rd : reg) (fast : bool) (q8 b l : sv) : step_out := ltac2:(tb__ "0|3|
S6VS;A1S5eS43S61Lfast;Vfast;S64S62S65VS;Vrd;S5Z0A1A3M0S110R1Z4M1A2A2A1S9VS;A1S5fS88S62G0S110R2G1A2M2A2S62S65S15fSfaVq8;Vb;Vl;R1A4S4eS0S1S6bVS;A1A3A2Vrd;SdR1A1A3G2A2A2Tv;X43x2Tpc;").

  Definition r3_step (A : axst) (sgn : bool) (rd rs1 : reg) (imm : bv 12) : option step_out := ltac2:(tb__ "0|a|
Sa3VA;A1S1SafS4R1A1A1Sa6S6aS63R2Vrs1;A2S66Vimm;A1A2S0S44S0A1S44S61A1M0Lx;S6eSa9VA;A1R1A2S0S44Sa5A1G0Lx;Sb2R3R1A2Sa5Sa5G0Lg0;R1S0S44S45S0S0A2M1A1G0Lx;M2Sb7R5SaaVA;A1M3R1Z0M4A4G1G1G0Lp;M5R1S0S0S46S61S18dR9Vrd;Sa7R8R4Z8M6SaS123R2R1A3M7A4R4R2R1A6A2Ll;Lb;X45x1Lp;S4cS61A1M8X44x2Lq8;S5fS0G2Sb7R6G3R1G4A4G1G5R1S0S0S46S61S18dRaVrd;Sa7R9SabR5A1M9G6G7A4G9R2R1A6A2Ll;Lb;X45x1Lp;G8X44x2Le;Lg;S5fS0S5eG2Sb7R7G3R2S114G6R1A2A4G1G5R1S0S0S43G0L_;Sa7RaSabR6A1S110S114G6R4A2G6A2G7A4S46S61S64S62S65RbVrd;S5G4A1A3S110S6RbA1Z4A2A2A1A2G8X43x2Ll;Lb;X45x1Lp;G8X44x2Lk;Le;Lg;Xa5x3Lg0;G8X44x2Loff;G8X44x2Tae;Tpv;TS;").

  Definition q8_of (d : gdesc) : sv := ltac2:(tb__ "0|0|
Sa5S0Ld;Vd;S0R1Lq8;S5fS0SabR2A1Le;Lg;S5fS0S5eS70S123SabR3A1S5S114Z8R1A2A1A3Lk;Le;Lg;Xa5x3").

  Definition xr_lo_ok (pv : prov) (b : sv) (d : gdesc) : bool := ltac2:(tb__ "0|3|
S43S43L_;M0Sa7Vpv;Vb;Z0M1S187Vd;A1A4S48Sa5S43Ld;Vd;S0S49Lq8;S5fS0G0S117Z3S69Sb1Vpv;A1Vb;A2A2M2Sa7Vpv;Vb;G1R1A4S49X43x2Le;Lg;S5fS0S5eG0G2Sa7Vpv;Vb;S11bS114Z8R1A2A1R2A4S49X43x2Lk;Le;Lg;Xa5x3X43x2").
  Definition xr_hi1_ok (pv : prov) (b l : sv) (d : gdesc) : bool := ltac2:(tb__ "0|8|
S43S43L_;M0Sa7Vpv;S187Vd;A1M1Z1M2SaS123Vb;Vl;A3M3A4S48G0Sa5S43Ld;M4Vd;S0S49Lq8;M5S5fS0Sa7Vpv;R1G2G3A4Le;Lg;S5fS0S5eSa7Vpv;R2S110S114Z8R1A2M6G2A2G3A4Lk;Le;Lg;Xa5x3S48G0Sc8Vpv;Vb;Vl;G1Z0M7A5S48G4Vd;G5S5fS0Sc8Vpv;Vb;Vl;R1G7A5Le;Lg;S5fS0S5eSc8Vpv;Vb;Vl;R2G6A5Lk;Le;Lg;Xa5x3X43x2X43x2X43x2").
  Fixpoint find_xr_d (pv : prov) (X : list (sv * sv)) (d : gdesc) : option (sv * sv) :=
    match X with
    | [] => None
    | (b, l) :: rest => if xr_lo_ok pv b d &&& xr_hi1_ok pv b l d then Some (b, l) else find_xr_d pv rest d
    end.

  Definition r3x_step (A : axst) (sz : msize) (rd rs1 : reg) (imm : bv 12) : option step_out := ltac2:(tb__ "0|3|
Sa3VA;A1S1SafS4R1A1A1Sa6S6aS63R2Vrs1;A2S66Vimm;A1A2S0S44S0A1S44S61A1M0Lx;S6eSa9VA;A1R1A2S0S44Sa5A1G0Lx;Sb2R3R1A2Sa5S187R1A1S0S44S45S0S0A2M1A1G0Lx;S18cR5SaaVA;A1R2A3G1G1G0Lp;R1S0S0S43G0L_;Sa7R8R4S114Z8S73Vsz;A1A2SaS123R2R1A3A4S46S61S64S62S65R9Vrd;S5Z0A1A3S110S6R9A1Z4A2A2A1A2S4cS61A1M2X43x2Ll;Lb;X45x1Lp;G2X44x2Tq8;Ld;G2X44x2Loff;G2X44x2Tae;Tpv;TS;").

  Fixpoint fa_target_in (facts : list sprop) (g' : positive) (fs : list sprop) : option sv :=
    match fs with
    | [] => None
    | SPUle (SVar h) t :: fs' =>
        if Pos.eqb h g' && has_facts (FA g' t) facts then Some t else fa_target_in facts g' fs'
    | _ :: fs' => fa_target_in facts g' fs'
    end.
  Definition fa_target (facts : list sprop) (g' : positive) : option sv := ltac2:(tb__ "0|0|
S197Vfacts;Vg';Vfacts;A3").

  Definition r3w_target2 (A : axst) (ae : sv) : option sv := ltac2:(tb__ "0|e|
S0S44S0A1M0Lx;Sa9VA;A1M1S5eS43G0L_;M2S50S115S113R1Z8A2Z0M3A2M4A1S4cS0A1M5G0G0Lx;S6eG1Vae;A2S0S0G0Ls;R1S5eG2S4aS4aS117G3R1A2G4A2S11aR1S112Z2Z3dA2A2A2S46S0S5R1A1A2G5X43x2Ltz;S5fS196S4Sa3VA;A1A1R1A2Lg';S121S0S0G5Lb0;La;M6Lop;M7G7S125G6Lop;M8G8S43S60S0G5La;Lw;Lsgn;M9S5fS0S5eG5Lk;Li;Ll;MaX0x8Ls;G5X44x2X43x2Lb;S5fG5Li;S121S0S0G5Lb;La;MbLop;McGcS125GbLop;MdGdG9GaX0x8").

  Definition r3w_target (A : axst) (ae : sv) : option sv := ltac2:(tb__ "0|a|
S0S44S0A1M0Lae;Vae;S5eS1a3VA;Vae;A2M1Lz;S5fG1Li;M2S121S0S0S121G0Lop;R3G1G1G1G1G1G1G1G1G1S0G0Lb;R1S5eS43G0L_;S115R1S118S112Z2Z40A2Z8A2A2S6eSa9VA;A1R3A2S4cS0A1X43x2Lm;G2S121S0S0G1Lb0;La;M3Lop0;M4G4S125G3Lop0;M5G5S43S60S0G1La;Lw;Lsgn;M6S5fS0S5eG1Lk;Li;Ll;M7X0x8X121xaLb;Lx;Lop;S121S0S0G1Lb;La;M8Lop;S125G8Lop;M9G9G6G7X0x8").

  Definition e64_of (d : gdesc) : sv := ltac2:(tb__ "0|0|
Sa5S0Ld;Vd;S0R1Lq8;S5fS0R1Le;Lg;S5fS0S5eS70S123R2S5S114Z8R1A2A1A3Lk;Le;Lg;Xa5x3").
  Definition blk64_lo_ok (pv : prov) (b x : sv) : bool := ltac2:(tb__ "0|1|
S43S43L_;M0Sa7Vpv;Vb;Z3fVx;A4S48G0S117Z6S69Sb1Vpv;A1Vb;A2A2Sa7Vpv;Vb;Z0Vx;A4S49X43x2X43x2").
  Definition blk64_hi_ok (pv : prov) (b l x : sv) : bool := ltac2:(tb__ "0|2|
S43S43L_;M0Sa7Vpv;Vx;Z40SaS123Vb;Vl;A3M1A4S48G0S117Z6S69Sb1Vpv;A1G1A2A2Sa7Vpv;Vx;Z1G1A4S49X43x2X43x2").
  Definition blk64_ok (pv : prov) (b l : sv) (d : gdesc) : bool := ltac2:(tb__ "0|3|
S43S43L_;M0G0S18bVpv;Vb;S187Vd;A1M1A3S48S18bVpv;Vb;S195Vd;A1M2A3X43x2G0S18aVpv;Vb;Vl;G1A4S48S18aVpv;Vb;Vl;G2A4X43x2S49X43x2").
  Definition base_aligned8 (A : axst) : bool := ltac2:(tb__ "0|2|
S0S43Lx;Sa9VA;A1S5eS115S113R1Z8A2Z0A2Lb;S5fS117Z3M0S69S4Sa3VA;A1A1M1SdR1A1A2A2Li;S121S0S0S117G0S69G1SaR3R2R1A3A2A2Lb;La;Lop;S121S0S0S117G0S69G1S3aR3R2R1A3A2A2Lb;La;Lop;S125S0S0S117G0S69G1S3dR3R2R1A3A2A2Lb;La;Lop;S125S0S0S117G0S69G1S3eR3R2R1A3A2A2Lb;La;Lop;S43S60S0S117G0S69G1S3bR3R2R1A3A2A2La;Lw;Lsgn;S5fS0S5eS117G0S69G1S3cR3R2R1A3A2A2Lk;Li;Ll;X0x8").

  Fixpoint find_xr_lit (X : list (sv * sv)) (w : Z) : option (sv * sv) :=
    match X with
    | [] => None
    | (SLit b, SLit l) :: rest =>
        let b' := b mod 2 ^ 64 in let l' := l mod 2 ^ 64 in
        if (Z.max w b' <? Z.min (w + 64) (b' + l')) && (b' + l' <=? 2 ^ 64) then Some (SLit b, SLit l) else find_xr_lit rest w
    | _ :: rest => find_xr_lit rest w
    end.
  Definition r3w_lit_hit (A : axst) (t : sv) : option (sv * sv) := ltac2:(tb__ "0|8|
S0S44S45S0S0A2M0A1M1Lt;Vt;S5eS43G1L_;S4aS4aS4aS189VA;A1S117Z0M2R1A2A2S115S113R1Z8M3A2G2A2A2S11aR1S112Z2Z3dA2A2A2S198SaaVA;A1S114G3R1A2A2S4cG0A1M4X43x2Ltz;S5fG4Li;S121S0S0G4Lb;La;M5Lop;M6G6S125G5Lop;M7G7S43S60S0G4La;Lw;Lsgn;S5fS0S5eG4Lk;Li;Ll;X0x8").

  Definition r3w_step (A : axst) (sz : msize) (rd rs1 : reg) (imm : bv 12) : option step_out := ltac2:(tb__ "0|7|
Sa3VA;A1S1S124S44S61A1M0Lsz;Vsz;S4cS61A1M1G1G1SafS4R1A1A1Sa6S44S0A1G0Lx;S1a2VA;S6aS63R2Vrs1;A2S66Vimm;A1A2A2S0S43G0L_;M2S50SbS9R3A1R1A2A1G1S44Sa5A1G0Lx;Sb2R2R1A2Sa5S44S45S0S0A2M3A1G0Lx;M4S18cR3SaaVA;A1R1A3G3G3G0Lp;R1S0S0G2S43S43L_;S189VA;A1S193R6R2R1R4A4S49X43x2S46S61S64S62S65R7Vrd;S5Z0A1A3S110S6R7A1Z4M5A2M6A2A1A2S46S61S64S62S65S4eS0S1S6bR7A1A3Vrd;SdS9R7A1A1A3G6A2A1A2X43x2Ll;Lb;X45x1Lp;G4S1a0VA;R2A2G3S46S61S64S62S65S4eS0S1S6bR5A1A3Vrd;SdS9R5A1A1A3S110S6R5A1G5A2A2A1A2Lp;G1X44x2X44x2Ld;G1X44x2X43x2Lt;G1X44x2Tpv;X124x4TS;").

  Definition pow2_log (m : Z) : option Z := ltac2:(tb__ "0|0|
S11eVm;A1S5eS43S44S5eA1L_;S4aS4aS117Z1R1A2S117R1Z3fA2A2S115S112Z2R1A2Vm;A2A2S46S5eR1A2S4cS5eA1X43x2Tk;").

  Definition divpow2_step (S : sstate) (op : mulop) (rd rs1 rs2 : reg) : option step_out := ltac2:(tb__ "0|8|
S0S44S61A1M0Lx;S63VS;Vrs2;A2S5eS44S5eA1G0Lx;S19cS113R1S112Z2Z40A2M1A2A1S5eS125G0Lop;Vop;S4cS61A1M2G2G2G2G2S46S61S64S62S65VS;Vrd;S70S129S63VS;Vrs1;A2M3S5R1A1A3A3S110S6VS;A1Z4A2M4A2A1A2G2S46S61S64S62S65VS;Vrd;S70S12aG3S5S118S113R2G1A2Z1A2A1A3A3G4A2A1A2X125x8Lk;G2X44x2Lm;S5fG2Li;S121S0S0G2Lb;La;M5Lop0;M6G6S125G5Lop0;M7G7S43S60S0G2La;Lw;Lsgn;S5fS0S5eG2Lk;Li;Ll;X0x8").

  Definition x_related (pv : prov) (facts : list sprop) (X : list (sv * sv)) (e : sv) : bool := ltac2:(tb__ "0|1|
S14bS45S0S0A2M0G0Sa7Vpv;S51S0S0R1A3Z0Ve;A4Lr;VX;A3").

  Definition is_zero_lit (v : sv) : bool := ltac2:(tb__ "0|3|
S0S43Lv;Vv;S5eS115S113R1S112Z2Z40A2A2Z0A2Lz;S5fS49Li;S121S0S0S49Lb;La;M0Lop;M1G1S125G0Lop;M2G2S43S60S0S49La;Lw;Lsgn;S5fS0S5eS49Lk;Li;Ll;X0x8").

  Fixpoint store_cells_z (facts : list sprop) (cells : list cell) (off : sv) (k : Z) : list cell * bool :=
    match cells with
    | [] => ([], false)
    | c :: rest =>
        let '(rest', taint) := store_cells_z facts rest off k in
        let z := is_zero_lit (c_val c) in
        match cell_rel facts off k c with
        | CLit d =>
            if lit_overlaps d (c_width c) k then
              let lo_keep := if d <? 0 then [mkCell (c_off c) (- d) (c_val c)] else [] in
              let hi_keep := if k <? d + c_width c
                             then [mkCell (mk_addk off k) (d + c_width c - k)
                                          (mk_alu ALU_SRL (c_val c) (SLit (8 * (k - d))))]
                             else [] in
              (lo_keep ++ hi_keep ++ (if z then c :: rest' else rest'), taint)
            else (c :: rest', taint)
        | CDisj => (c :: rest', taint)
        | CUnk => if z then (c :: rest', taint) else (rest', true)
        end
    end.

  Definition obj_store_z (facts : list sprop) (o : sobj) (off : sv) (k : Z) (v : sv) : sobj := ltac2:(tb__ "0|1|
S45S47S7A1M0S43A2S3Lx;S1a8Vfacts;S17Vo;A1Voff;Vk;A4G0S43S2aS1dVo;A1S25Vo;A1S24Vo;A1S4fS7S1cVoff;Vk;Vv;A3R2A3S43SfLtaint;R1S2eSeVo;A1X43x2A5Ltaint;Lcells';X45x1").

  Definition zst_step (S : sstate) (sz : msize) (rs1 rs2 : reg) (imm : bv 12) : option step_out := ltac2:(tb__ "0|15|
S44S0A1S44S61A1M0Lx;S1eVS;A1S0S4cS61A1M1Ls;S0G0Lx;S63VS;Vrs2;A2S5eS43G0L_;M2S50S115S113R1S112Z2Z40A2A2Z0A2A1G1S44S45S45S4dS3A2M3S0A2M4A1G0Lx;S7cS11VS;A1M5S4VS;A1M6S6aS63VS;Vrs1;A2S66Vimm;A1A2S73Vsz;A1M7U0A5G4G4G0Lp;R1G3S0G3G0Lp0;R2S4dS3S47S7A1M8G0Lx;S17R1A1M9SfG0Lx;SeR1A1MaG2S4aS4aS15GaA1S50S16GaA1A1A2S14bS7S7S199S19R1A1A1Lc;MbG9A3A2S46S61S64S62S6dVS;S6fS3G5R2S3S186G6R1R4G7S5R7A1A5Lo1;A4A2S110S6VS;A1Z4A2McA2A1A2G1X43x2MdS46S61S64S62VS;GcA2A1A2GdS5fG2S4aS4aS15SeR2A1MeA1S50S16GeA1A1A2S14bS7GbS17R2A1A3A2S46S61S64S62S6dVS;S6fS3G5R3S3S186G6R1R5G7S5R8A1A5Lo1;A4A2GcA2A1A2G1X43x2Ll;MfGfS5eS0S47S45S5eS5eA2A1S47S28A1G2S4aS4aS15SeR5A1M10A1S50S16G10A1A1A2S14bS7GbS17R5A1A3A2S46S61S64S62S6dVS;S6fS3G5R6S3S186G6R1R8G7S5RbA1A5Lo1;A4A2GcA2A1A2G1X43x2Ltmpl;Lflds;Lcnt;Lesz;Xfx6S7G8G2S4aS4aS15SeR3A1M11A1S50S16G11A1A1A2S14bS7GbS17R3A1A3A2S46S61S64S62S6dVS;S6fS3G5R4S3S186G6R1R6G7S5R9A1A5Lo1;A4A2GcA2A1A2G1X43x2Ll;Lc;X47x2Lo;Ln;X45x1Loff;Lp0;X45x1Lp;G1X44x2X43x2Lz;S5fG1Li;S121S0S0G1Lb;La;M12Lop;M13G13S125G12Lop;M14G14S43S60S0G1La;Lw;Lsgn;S5fS0S5eG1Lk;Li;Ll;X0x8X44x2").

  Definition or_else (o : option step_out) (d : step_out) : step_out :=
    match o with Some r => r | None => d end.

  Definition sym_stepA (A : axst) : step_outA := ltac2:(tb__ "0|1d|
Sa3VA;A1S1S43SadL_;S18R1A1SacVA;S6cVsegs;R1A2A2M0S44S122A1SadLx;S67Vsegs;S6R1A1A2S122S122SadLi;R1S92Q5A1M1S92Q14A1SacVA;S6cVsegs;R4A2A2M2Limm;Lrd;M3G3G1S92Q15A1G2Limm;Lrd;G1G1S92QcA1M4SacVA;S6cVsegs;R5A2A2M5Limm;Lrs1;Lrd;M6S131G1G1S92QdA1SacVA;S6cVsegs;R6A2M7A2M8Limm;Lrs2;Lrs1;Lc;S124S43G1G1G4S124SadLsz;R5S44S61A1M9SadLx;MaS19fVA;R4R3R2R1A5S61SbfVA;R1A2Lo;SacVA;S6cVsegs;R7A2A2MbX44x2GaS1a4VA;R5R3R2R1A5S61SacVA;R1A2Lo;McGaS1a1VA;R5R3R2R1A5GcGbX44x2X44x2MdGdGdX124x4Limm;Lrs1;Lrd;Lsgn;Lsz;S124G1G1G4SacVA;S185S1abR6R4R3R2R1A5G7A2A2Limm;Lrs2;Lrs1;Lsz;S121G1G1G4S121SadLop;MeR4G8G8G8G8G8G8G8G8G8SacVA;S43S61L_;MfS115S66R1A1M10Z7A2S185S19eR6R3R2A3G7A2GfS115G10N8A2S185G9G9Lx;S191VA;R3R2A3S61S46S61R1A2Lo;S192VA;R3R2R1A4X44x2G7A2G7X43x2X43x2A2X121xaLimm;Lrs1;Lrd;Lop;S121G1G1S92Q6M11A1GeR4G8G8G8G8G8G8SacVA;GfS43S43L_;S115S93G11R1A2Z3A2S1a9SafS4R6A1M12A1G12SaaVA;A1S63R6R2A2A4S49X43x2S185S19dR6R3R2A3G7A2G7X43x2A2G8G8G8X121xaLsh;Lrs1;Lrd;Lop;S121G1G1G1G8Lrs2;Lrs1;Lrd;M13Lop;M14G6S121G1G1G1G8Lshamt;Lrs1;Lrd;Lop;G14S92Q4A1M15G15G15G1G1GbLrs1;Lrd;M16Lsucc;Lpred;Lfm;G6SacVA;S6cVsegs;R2A2A2M17G17S125G1G1G1SacVA;S185S194R6R4R3R2R1A5G7A2A2Lrs2;Lrs1;Lrd;Lop;S125G13Lop;S127S43S43G16Lrl;Laq;Lw;S127S43S43G1G1G1SacVA;S6cVsegs;R8A2A2M18Lrs2;Lrs1;Lrd;Lrl;Laq;Lw;S128S127S43S43G1G1G1SacVA;S190R9R7R6R3R2R1A6A2Lrs2;Lrs1;Lrd;Lrl;Laq;Lwd;Lop;S12bG1G1G4G8Lcsr;M19Lrs1;Lrd;Lop;S12bG1G1G19Luimm;Lrd;Lop;S126G1G1G4G8Limm;M1aLrs1;Lrd;Lfmt;S126G1G1G1aLrs2;Lrs1;Lfmt;S134S126G1G1G1G1S92Q3A1M1bSacVA;S6cVsegs;R9A2A2Lrm;Lrs3;Lrs2;Lrs1;Lrd;Lfmt;Lop;S132S126G1G1G1G1bG18Lrm;Lrs2;Lrs1;Lrd;Lfmt;Lop;S126G1G1G1bG8Lrm;Lrs1;Lrd;Lfmt;S137S126G1G1G1GbLrs2;Lrs1;Lrd;Lfmt;M1cLop;S135G1cLop;S133G1cLop;S12cS12cG1G1G1bGbLrm;Lrs1;Lrd;Lsrc;Ldst;S136S126G1G1G8Lrs1;Lrd;Lfmt;Ldir;S126G1G1G5Lrs1;Lrd;Lfmt;X122x23Li;G0X44x2X43x2TS;").

  Definition is_branch_at (pc : Z) : bool :=
    match instr_at segs pc with Some (Branch _ _ _ _) => true | _ => false end.

  Fixpoint run_past_branch (n : nat) (A : axst) : option axst :=
    match n with
    | O => None
    | S n' =>
        match sym_stepA A with
        | StNextA A' => if is_branch_at (ss_pc (ax_S A)) then Some A' else run_past_branch n' A'
        | _ => None
        end
    end.

  Fixpoint run_to_pc (n : nat) (pc : Z) (A : axst) : option axst :=
    if ss_pc (ax_S A) =? pc then Some A else
    match n with
    | O => None
    | S n' =>
        match sym_stepA A with
        | StNextA A' => run_to_pc n' pc A'
        | _ => None
        end
    end.

  Fixpoint join_regs (base : positive) (r : Z) (l1 l2 : list sv) : list sv :=
    match l1, l2 with
    | a :: t1, b :: t2 =>
        (if sv_eqb a b then a else SVar (Z.to_pos (Zpos base + r))) :: join_regs base (r + 1) t1 t2
    | _, _ => []
    end.

  Definition join2 (g : positive) (A B1 B2 : axst) : option axst := ltac2:(tb__ "0|d|
Sa3VB1;A1S1Sa3VB2;A1S1S1b0S1b0S9R2A1S9R1A1A2Vg;A2S5fS43S44Sa4A1L_;S4aS4aS4aS4aS4aS4aS4aS4aS4aS4aS4aS4aS4aS4aS4aS115S6R3A1M0S6R2A1A2S1c0S56S0S39R3A1M1A2U20M2A2A2S1c0S56S0S39R2A1M3A2G2A2A2Sb5S0S13S38R3A1M4S38R2A1A4A2Sf0S37R3A1M5S37R2A1A2A2SebS1eR3A1M6S1eR2A1A2A2Sb5S3Sf3S11R3A1M7S11R2A1A4A2S14aS2S2S14bS2S36R1A1M8S4R4A1A3Lf;S4Sa3VA;A1A1M9A3A2S14aS2S2S14bS2G8S4R3A1A3Lf;G9A3A2S14aS2S1aVg;A1G9A3A2S50S18R3A1A1A2S50S18R2A1A1A2Sb5S45S0S0A2MaSbbSaaVB1;A1SaaVA;A1MbA4A2Sb5GaSbbSaaVB2;A1GbA4A2S13Sa9VB1;A1Sa9VA;A1McA2A2S13Sa9VB2;A1GcA2A2S46Sa4Sb9VA;S40G0S19bR1Z0G1G3A4G4G5G6G7G9S1b2R1P20A2S49A9A2A2S4cSa4A1X43x2Tbase;TS2;TS1;").

  Definition JOIN_FUEL : nat := 8%nat.

  Definition try_join (A A1 A2 : axst) : option axst := ltac2:(tb__ "0|3|
S44Sa4A1M0G0Lx;M1S1a5S188VA1;A2Sa4G1S1a6S188S6Sa3R1A1A1VA2;A3Sa4S19aS9Sa3VA;A1A1VA;R2R1A4LB2;S4cSa4A1M2X44x2LB1;G2X44x2").

  Fixpoint sym_runA_ref (fuel : nat) (cuts : list Z) (A : axst) (first : bool)
    : option (list leafA) :=
    match fuel with
    | O => if first then None else Some [mkLeafA A RsFuel]
    | S fuel' =>
        if negb first && memZ (ss_pc (ax_S A)) cuts then Some [mkLeafA A RsCut]
        else
          let fork A1 A2 :=
            match sym_runA_ref fuel' cuts A1 false, sym_runA_ref fuel' cuts A2 false with
            | Some l1, Some l2 => Some (l1 ++ l2)
            | _, _ => None
            end in
          match sym_stepA A with
          | StNextA A' => sym_runA_ref fuel' cuts A' false
          | StForkA A1 A2 => fork A1 A2
          | StJoinA A1 A2 =>
              match try_join A A1 A2 with
              | Some M => sym_runA_ref fuel' cuts M false
              | None => fork A1 A2
              end
          | StStopA r => if first then None else Some [mkLeafA A r]
          end
    end.
End Build.

Definition obj_ext (o : sobj) : sv * sv * sv := ltac2:(tb__ "0|0|
S4bS45S0S0A2S0S4bS0S0S1dVo;A1S25Vo;A1A4S24Vo;A1A4").
Definition exts (S : sstate) : list (sv * sv * sv) := map obj_ext (ss_objs S).

Lemma map_ext_list_set : ltac2:(tb__ "0|1|
S47S3A1S4dS3S3S57S44S3A1S14cS3R4R3A3S46S3R2A2A3S57S45S45S0S0A2S0A2M0Sb0R2A1Sb0R3A1A3S57S47G0A1S156S3G0Sb0S75S3R6R5R3A4A4S156S3G0Sb0R6A4A3F_;F_;Fo';Fo;Fn;Fobjs;").
Proof.
  induction objs as [|x objs IH]; intros n o o' Hn He; [destruct n; discriminate|].
  destruct n as [|n]; cbn in Hn |- *.
  - injection Hn as ->. rewrite He. reflexivity.
  - rewrite (IH n o o' Hn He). reflexivity.
Qed.

Lemma map_ext_list_upd : ltac2:(tb__ "0|1|
S47S3A1S4dS3S3Fx;S3S57S45S45S0S0A2S0A2M0Sb0R2R1A1A1Sb0R1A1A3Fo;S57S47G0A1S156S3G0Sb0S6fS3R4R3R2A4A4S156S3G0Sb0R4A4A3F_;Ff;Fn;Fobjs;").
Proof.
  induction objs as [|x objs IH]; intros n f Hf; [destruct n; reflexivity|].
  destruct n as [|n]; cbn; [rewrite Hf; reflexivity|]. rewrite (IH n f Hf). reflexivity.
Qed.

Lemma exts_set_reg : ltac2:(tb__ "0|0|
S1S92Q5A1S0S57S47S45S45S0S0A2S0A2A1Sa8S65R3R2R1A3A1Sa8R3A1A3Fv;Fr;FS;").
Proof. intros. unfold exts. rewrite ss_objs_set_reg. reflexivity. Qed.
Lemma exts_set_pc : ltac2:(tb__ "0|0|
S1S5eS57S47S45S45S0S0A2S0A2A1Sa8S62R2R1A2A1Sa8R2A1A3Fpc;FS;").
Proof. reflexivity. Qed.
Lemma exts_set_freg : ltac2:(tb__ "0|0|
S1S92Q5A1S0S57S47S45S45S0S0A2S0A2A1Sa8S90R3R2R1A3A1Sa8R3A1A3Fv;Fr;FS;").
Proof. reflexivity. Qed.
Lemma exts_add_fact : ltac2:(tb__ "0|0|
S1S2S57S47S45S45S0S0A2S0A2A1Sa8S89R2R1A2A1Sa8R2A1A3Fp;FS;").
Proof. reflexivity. Qed.
Lemma exts_set_resv : ltac2:(tb__ "0|0|
S1S44S0A1S57S47S45S45S0S0A2S0A2A1Sa8S91R2R1A2A1Sa8R2A1A3Fr;FS;").
Proof. reflexivity. Qed.
Lemma exts_fresh : ltac2:(tb__ "0|0|
S1S57S47S45S45S0S0A2S0A2A1Sa8S4eS0S1S6bR1A1A3A1Sa8R1A1A3FS;").
Proof. reflexivity. Qed.

Lemma obj_ext_store : ltac2:(tb__ "0|0|
S47S2A1S3S0S5eS0S57S45S45S0S0A2S0A2Sb0S8eR5R4R3R2R1A5A1Sb0R4A1A3Fv;Fk;Foff;Fo;Ffacts;").
Proof. intros. unfold obj_store. destruct (store_cells facts (ob_cells o) off k). reflexivity. Qed.

Lemma obj_ext_store_z : ltac2:(tb__ "0|0|
S47S2A1S3S0S5eS0S57S45S45S0S0A2S0A2Sb0Sb3R5R4R3R2R1A5A1Sb0R4A1A3Fv;Fk;Foff;Fo;Ffacts;").
Proof. intros. unfold obj_store_z. destruct (store_cells_z facts (ob_cells o) off k). reflexivity. Qed.

Lemma obj_ext_store_d : ltac2:(tb__ "0|0|
S47S2A1S3S0S5eS0S57S45S45S0S0A2S0A2Sb0S8fR5R4R3R2R1A5A1Sb0R4A1A3Fv;Fk;Foff;Fo;Ffacts;").
Proof.
  intros. unfold obj_store_d. pose proof (obj_ext_store facts o off k v) as E.
  destruct (ob_dflt o); exact E.
Qed.

Section Exts.
Variable segs : list Segment.

Lemma sym_store_exts : ltac2:(tb__ "0|0|
S1S0S5eS0S1S57S44S1A1S7eR5R4R3R2A4S46S1R1A2A3S57S47S45S45S0S0A2S0A2A1Sa8R2A1Sa8R6A1A3F_;FS';Fv;Fk;Fae;FS;").
Proof using .
  intros S ae k v S' H. unfold sym_store in H.
  destruct (find_obj (ss_objs S) (ss_facts S) ae k 0) as [[[n o] off]|] eqn:Hfo; [|discriminate].
  destruct (dflt_writable (ob_dflt o)); [|discriminate]. injection H as <-.
  unfold exts. cbn. apply map_ext_list_upd. intros o'. apply obj_ext_store_d.
Qed.

Lemma load_fresh_exts : ltac2:(tb__ "0|0|
S1S4dS3S0S5eS43S60S0S1S57S44S3A1S14cS3S11R9A1R8A3S46S3R7A2A3S57S72S8dRaR9R8R7R6R5R4A7S74R3R2A2A3S57S47S45S45S0S0A2S0A2A1Sa8R3A1Sa8RbA1A3F_;F_;FS';Fv;Fw;Fsgn;Fk;Foff;Fo;Fn;FS;").
Proof using .
  intros S n o off k sgn w v S' Hn H. unfold load_fresh, fresh in H.
  destruct (dflt_writable (ob_dflt o)); apply lrok_inj in H as [_ <-]; [|reflexivity].
  unfold exts. cbn. apply (map_ext_list_set _ _ o); [exact Hn | reflexivity].
Qed.

Lemma load_arr_exts : ltac2:(tb__ "0|0|
S1S4dS3S0S5eS43S60S5eS0S47S45S5eS5eA2A1S47S28A1S0S1S57S44S3A1S14cS3S11RdA1RcA3S46S3RbA2A3S57S72S8bReRdRcRbRaR9R8R7R6R5R4AbS74R3R2A2A3S57S47S45S45S0S0A2S0A2A1Sa8R3A1Sa8RfA1A3F_;F_;FS';Fv;Ftmpl;Fflds;Fcnt;Fesz;Fw;Fsgn;Fk;Foff;Fo;Fn;FS;").
Proof using .
  intros S n o off k sgn w esz cnt flds tmpl v S' Hn H. unfold load_arr in H.
  destruct (lin_decomp _ _ _) as [[idx c]|]; [|exact (load_fresh_exts _ _ _ _ _ _ _ _ _ Hn H)].
  destruct (fld_index flds c k); [|exact (load_fresh_exts _ _ _ _ _ _ _ _ _ Hn H)].
  destruct (uleq _ _ _ _); [|exact (load_fresh_exts _ _ _ _ _ _ _ _ _ Hn H)].
  apply lrok_inj in H as [_ <-]. unfold exts. cbn. apply (map_ext_list_set _ _ o); [exact Hn | reflexivity].
Qed.

Lemma load_dflt_exts : ltac2:(tb__ "0|0|
S1S4dS3S0S5eS43S60S0S1S57S44S3A1S14cS3S11R9A1R8A3S46S3R7A2A3S57S72S8cRaR9R8R7R6R5R4A7S74R3R2A2A3S57S47S45S45S0S0A2S0A2A1Sa8R3A1Sa8RbA1A3F_;F_;FS';Fv;Fw;Fsgn;Fk;Foff;Fo;Fn;FS;").
Proof using .
  intros S n o off k sgn w v S' Hn H. unfold load_dflt in H.
  destruct (ob_dflt o); try exact (load_fresh_exts _ _ _ _ _ _ _ _ _ Hn H).
  exact (load_arr_exts _ _ _ _ _ _ _ _ _ _ _ _ _ Hn H).
Qed.

Lemma sym_load_exts : ltac2:(tb__ "0|0|
S1S0S5eS43S0S1S57S72S7dVsegs;R6R5R4R3A5S74R2R1A2A3S57S47S45S45S0S0A2S0A2A1Sa8R2A1Sa8R7A1A3F_;FS';Fv;Fsgn;Fk;Fae;FS;").
Proof using .
  intros S ae k sgn v S' H. unfold sym_load in H. lazy zeta in H. revert H.
  destruct (match ae with SLit a => ro_load segs (a mod 2 ^ 64) (Z.to_nat k) | _ => None end) as [z|]; intros H.
  { apply lrok_inj in H as [_ <-]. reflexivity. }
  destruct (find_obj (ss_objs S) (ss_facts S) ae k 0) as [[[n o] off]|] eqn:Hfo.
  - destruct (find_obj_spec _ _ _ _ _ _ _ _ Hfo) as (i & Hni & Hn & _). cbn in Hni. subst i.
    destruct (read_cells (ss_facts S) (ob_cells o) off k CRNone);
      try (apply lrok_inj in H as [_ <-]; reflexivity); try exact (load_dflt_exts _ _ _ _ _ _ _ _ _ Hn H).
    + destruct (ob_dflt o).
      * exact (load_fresh_exts _ _ _ _ _ _ _ _ _ Hn H).
      * apply lrok_inj in H as [_ <-]. reflexivity.
      * revert H. destruct (ob_base o) as [zb| | | | | | |]; try (intros H; exact (load_fresh_exts _ _ _ _ _ _ _ _ _ Hn H)).
        destruct zb; try (intros H; exact (load_fresh_exts _ _ _ _ _ _ _ _ _ Hn H)).
        destruct off; try (intros H; exact (load_fresh_exts _ _ _ _ _ _ _ _ _ Hn H)).
        destruct (image_load segs _ (Z.to_nat k)); [|discriminate].
        intros H. apply lrok_inj in H as [_ <-]. reflexivity.
      * apply lrok_inj in H as [_ <-]. reflexivity.
      * apply lrok_inj in H as [_ <-]. reflexivity.
      * exact (load_arr_exts _ _ _ _ _ _ _ _ _ _ _ _ _ Hn H).
    + revert H. destruct (tile_cells 9 _ 0 k); intros H; [|exact (load_dflt_exts _ _ _ _ _ _ _ _ _ Hn H)].
      apply lrok_inj in H as [_ <-]. reflexivity.
  - destruct (ss_lenient S ||| ro_span segs (ss_facts S) ae k); [|discriminate]. unfold fresh in H.
    apply lrok_inj in H as [_ <-]. reflexivity.
Qed.

Definition exts_kept (S : sstate) (o : step_out) : Prop := ltac2:(tb__ "0|3|
S61OLo;Vo;S1S57S47S45S45S0S0A2S0A2A1M0Sa8R1A1Sa8VS;A1M1A3M2LS';S1S1S58S57G0Sa8R2A1G1A3G2A2LS2;LS1;S68S5aLr;X61x3").

Lemma sym_step_exts : ltac2:(tb__ "0|0|
S1S14dR1S6cVsegs;R1A2A2FS;").
Proof using .
  intros S. unfold sym_step.
  destruct (instr_at segs (ss_pc S)) as [i|]; [|exact I].
  destruct i; try exact I; cbn [exts_kept]; rewrite ?exts_set_pc, ?exts_set_reg, ?exts_set_freg; try reflexivity.
  - destruct (mk_addk (get_reg S rs1) (immI imm)); try exact I. cbn [exts_kept]. rewrite exts_set_pc, exts_set_reg. reflexivity.
  - destruct (decide_branch S c (get_reg S rs1) (get_reg S rs2)); cbn [exts_kept]; rewrite ?exts_set_pc, ?exts_add_fact; repeat split; reflexivity.
  - destruct (sym_load segs S (mk_addk (get_reg S rs1) (immI imm)) (msz sz) signed) as [v S'|] eqn:Hl; [|exact I].
    cbn [exts_kept]. rewrite exts_set_pc, exts_set_reg. eapply sym_load_exts; eauto.
  - destruct (ss_resv S); [exact I|].
    destruct (sym_store S _ _ _) as [S'|] eqn:Hs; [|exact I]. cbn [exts_kept]. rewrite exts_set_pc. eapply sym_store_exts; eauto.
  -   destruct (addr_aligned _ _ _); [|exact I]. cbn [negb].
    destruct (sym_load segs S (get_reg S rs1) (amo_k w) true) as [v S'|] eqn:Hl; [|exact I].
    cbn [exts_kept]. rewrite exts_set_pc, exts_set_resv, exts_set_reg. eapply sym_load_exts; eauto.
  -   destruct (addr_aligned _ _ _); [|exact I]. cbn [negb].
    destruct (ss_resv S) as [e|].
    + destruct (sv_eqb e (get_reg S rs1)); [|exact I].
      destruct (sym_store (set_resv S None) _ _ _) as [S'|] eqn:Hs; [|exact I]. cbn [exts_kept].
      rewrite exts_set_pc, exts_set_reg. rewrite (sym_store_exts _ _ _ _ _ Hs). reflexivity.
    + cbn [exts_kept]. rewrite exts_set_pc, exts_set_reg. reflexivity.
  -   unfold sym_csr. destruct (ss_fcsr S); [|exact I].
    destruct ((bv_unsigned csr =? 2) && _)%bool; [cbn [exts_kept]; rewrite exts_set_pc, exts_set_reg; reflexivity|].
    destruct (bv_unsigned csr =? 1); [|exact I]. cbn [exts_kept fresh fst snd]. rewrite exts_set_pc, exts_set_reg. reflexivity.
  -   unfold sym_csr. destruct (ss_fcsr S); [|exact I].
    destruct ((bv_unsigned csr =? 2) && _)%bool; [cbn [exts_kept]; rewrite exts_set_pc, exts_set_reg; reflexivity|].
    destruct (bv_unsigned csr =? 1); [|exact I]. cbn [exts_kept fresh fst snd]. rewrite exts_set_pc, exts_set_reg. reflexivity.
  -   destruct fmt.
    + destruct (sym_load segs S (mk_addk (get_reg S rs1) (immI imm)) 4 false) as [v S'|] eqn:Hl; [|exact I].
      cbn [exts_kept]. rewrite exts_set_pc, exts_set_freg. eapply sym_load_exts; eauto.
    + destruct (sym_load segs S (mk_addk (get_reg S rs1) (immI imm)) 8 true) as [v S'|] eqn:Hl; [|exact I].
      cbn [exts_kept]. rewrite exts_set_pc, exts_set_freg. eapply sym_load_exts; eauto.
  -   destruct (ss_resv S); [exact I|].
    destruct (sym_store S _ _ _) as [S'|] eqn:Hs; [|exact I]. cbn [exts_kept]. rewrite exts_set_pc. eapply sym_store_exts; eauto.
  -   destruct (rm_ok S rm); [|exact I]. reflexivity.
  -   destruct (rm_ok S rm); [|exact I]. reflexivity.
  -   destruct (rm_ok S rm); [|exact I]. reflexivity.
  -   destruct (frm0b S); [|exact I]. reflexivity.
  -   destruct (frm0b S); [|exact I]. reflexivity.
  -   destruct (frm0b S); [|exact I]. cbn [exts_kept havoc_reg_b fresh fst snd]. rewrite exts_set_pc, exts_set_reg. reflexivity.
  -   destruct (rm_ok S rm); [|exact I]. cbn [negb].
    destruct (fcvt_fty dst && (fcvt_fty src || fcvt_ity src))%bool; [reflexivity|].
    destruct (fcvt_ity dst && fcvt_fty src)%bool; [|exact I]. cbn [exts_kept havoc_reg fresh fst snd]. rewrite exts_set_pc, exts_set_reg. reflexivity.
  -   destruct dir, fmt; cbn [exts_kept]; rewrite ?exts_set_pc, ?exts_set_reg, ?exts_set_freg; reflexivity.
  -   destruct (frm0b S); [|exact I]. cbn [exts_kept havoc_reg fresh fst snd]. rewrite exts_set_pc, exts_set_reg. reflexivity.
Qed.

Lemma amo_step_exts : ltac2:(tb__ "0|1|
S1S128S127S92Q5A1M0G0G0S14dR6SccVsegs;R6R5R4R3R2R1A7A2Frs2;Frs1;Frd;Fwd;Fop;FS;").
Proof using .
  intros S op wd rd rs1 rs2. unfold amo_step.
  destruct (negb (amo_alignedb _ _ _)); [exact I|].
  destruct (ss_resv S); [exact I|].
  destruct (sym_load segs S (get_reg S rs1) (amo_k wd) true) as [v S1|] eqn:Hl; [|exact I].
  destruct (amo_sv op wd v (get_reg S rs2)) as [nv|]; [|exact I].
  destruct (sym_store S1 _ _ _) as [S2|] eqn:Hs; [|exact I]. cbn [exts_kept].
  rewrite exts_set_pc, exts_set_reg. rewrite (sym_store_exts _ _ _ _ _ Hs). eapply sym_load_exts; eauto.
Qed.

Lemma amo_sv_below : ltac2:(tb__ "0|0|
S5fS128S127S0S0S0S57S43SbR6R3A2S48A3S57S43SbR7R3A2S48A3S57S44S0A1Sb8R7R6R5R4A4S46S0R3A2A3S57S43SbR9R4A2S48A3F_;F_;F_;Fnv;Fsrc;Fold;Fwd;Fop;Fn;").
Proof using .
  intros n op wd old src nv Ho Hs H. destruct op, wd; cbn in H; try discriminate; injection H as <-; cbn; rewrite ?Ho, ?Hs; reflexivity.
Qed.

Definition shape_kept (S : sstate) (o : step_out) : Prop := ltac2:(tb__ "0|3|
S61OLo;Vo;S1S58S1aeS9VS;A1M0S9R1A1A2S57S43S18R1A1S18VS;A1M1A3A2M2LS';S1S1S58S58S1aeG0S9R2A1A2S57S43S18R2A1G1A3A2G2A2LS2;LS1;S68S5aLr;X61x3").

Lemma amo_step_shape : ltac2:(tb__ "0|1|
S1S128S127S92Q5A1M0G0G0S14eR6SccVsegs;R6R5R4R3R2R1A7A2Frs2;Frs1;Frd;Fwd;Fop;FS;").
Proof using .
  intros S op wd rd rs1 rs2. unfold amo_step.
  destruct (negb (amo_alignedb _ _ _)); [exact I|].
  destruct (ss_resv S); [exact I|].
  destruct (sym_load segs S (get_reg S rs1) (amo_k wd) true) as [v S1|] eqn:Hl; [|exact I].
  destruct (amo_sv op wd v (get_reg S rs2)) as [nv|]; [|exact I].
  destruct (sym_store S1 _ _ _) as [S2|] eqn:Hs; [|exact I]. cbn.
  rewrite ss_next_set_reg, ss_lenient_set_reg.
  destruct (sym_store_shape _ _ _ _ _ Hs) as [-> ->].
  exact (sym_load_next segs _ _ _ _ _ _ Hl).
Qed.

Definition stepA_inv (A A' : axst) : Prop := ltac2:(tb__ "0|3|
S58S1aeS9Sa3VA;A1M0A1S9Sa3VA';A1M1A1A2S58S57S43S18G1A1S18G0A1A3S58S57S47S45S0S0A2M2A1SaaVA';A1SaaVA;A1A3S58S57S0Sa9VA';A1Sa9VA;A1A3S57S47S45G2S0A2A1Sa8G1A1Sa8G0A1A3A2A2A2A2").

Definition stepA_kept (A : axst) (o : step_outA) : Prop := ltac2:(tb__ "0|2|
SadOLo;Vo;Sa4S150VA;R1A2M0LA';Sa4Sa4S58S150VA;R2A2G0A2LA2;LA1;M1G1S68S5aLr;Xadx4").

Lemma lift_out_kept : ltac2:(tb__ "0|0|
Sa4S61S14eSa3R2A1R1A2S14dSa3R3A1R2A2S14fR4SacR4R3A2A2F_;F_;Fo;FA;").
Proof using .
  intros A o Hs He. destruct o; cbn in *.
  - destruct Hs as [H1 H2]. repeat split; assumption || reflexivity.
  - destruct Hs as [[H1 H2] [H3 H4]]. destruct He as [E1 E2]. repeat split; assumption || reflexivity.
  - exact I.
Qed.

Lemma exts_add_facts : ltac2:(tb__ "0|0|
S47S2A1S1S57S47S45S45S0S0A2S0A2A1Sa8S15fR2R1A2A1Sa8R1A1A3FS;FF;").
Proof. reflexivity. Qed.

Lemma r1_step_kept : ltac2:(tb__ "0|1|
S1S92Q5A1M0G0S61S57S44S61A1Sc1R4R3R2A3S46S61R1A2A3S58S14eR5R2A2S14dR5R2A2A2F_;Fo;Frs1;Frd;FS;").
Proof using .
  intros S rd rs1 o H. unfold r1_step in H.
  destruct (is_lit (get_reg S rs1)); [discriminate|].
  destruct (split_lit (get_reg S rs1)) as [e0 c].
  match type of H with (if ?cnd then _ else _) = _ => destruct cnd end.
  - destruct (find_granule_eq _ (ss_facts S) e0) as [g|]; injection H as <-; cbn [shape_kept exts_kept].
    + rewrite exts_set_pc, exts_set_reg. split; [|reflexivity]. cbn. rewrite ss_next_set_reg, ss_lenient_set_reg. split; [lia|reflexivity].
    + rewrite exts_set_pc, exts_set_reg. split; [|reflexivity].
      cbn. rewrite ss_next_set_reg, ss_lenient_set_reg. cbn. split; [lia|reflexivity].
  - destruct (find_granule _ (ss_facts S) (get_reg S rs1)) as [g|]; injection H as <-; cbn [shape_kept exts_kept].
    + rewrite exts_set_pc, exts_set_reg. split; [|reflexivity]. cbn. rewrite ss_next_set_reg, ss_lenient_set_reg. split; [lia|reflexivity].
    + rewrite exts_set_pc, exts_set_reg. split; [|reflexivity].
      cbn. rewrite ss_next_set_reg, ss_lenient_set_reg. cbn. split; [lia|reflexivity].
Qed.

Lemma r2_step_kept : ltac2:(tb__ "0|1|
S1S92Q5A1M0G0S61S57S44S61A1Sd6R4R3R2A3S46S61R1A2A3S58S14eR5R2A2S14dR5R2A2A2F_;Fo;Frs1;Frd;FS;").
Proof using .
  intros S rd rs1 o H. unfold r2_step in H.
  destruct (find_granule _ (ss_facts S) _) as [g|]; [|discriminate].
  injection H as <-. cbn [shape_kept exts_kept].
  rewrite exts_set_pc, exts_set_reg. split; [|reflexivity]. cbn. rewrite ss_next_set_reg, ss_lenient_set_reg. split; [lia|reflexivity].
Qed.

Lemma andm8_step_kept : ltac2:(tb__ "0|2|
Sa4S92Q5A1M0G0S92QcA1S61S57S44S61A1SbdR5R4R3R2A4S46S61R1A2A3S58S14eSa3R6A1M1R2A2S14dG1R2A2A2F_;Fo;Fimm;Frs1;Frd;FA;").
Proof.
  intros A rd rs1 imm o H. unfold andm8_step in H. set (S := ax_S A) in *.
  destruct (is_lit (get_reg S rs1) || (bv_unsigned rd =? 0)); [discriminate|].
  destruct (puleq _ _ _ _); [|discriminate]. injection H as <-.
  cbn [shape_kept exts_kept]. unfold add_facts. cbn. rewrite ss_next_set_reg, ss_lenient_set_reg.
  split; [split; [lia | reflexivity]|]. unfold exts. cbn. pose proof (exts_set_reg S rd (mk_slt_f (ss_facts S) ALU_AND (get_reg S rs1) (SLit (immI imm mod 2 ^ 64)))) as E.
  unfold exts in E. exact E.
Qed.

Lemma andm8_sh_step_kept : ltac2:(tb__ "0|2|
Sa4S92Q5A1M0G0S61S57S44S61A1ScdR4R3R2A3S46S61R1A2A3S58S14eSa3R5A1M1R2A2S14dG1R2A2A2F_;Fo;Frs1;Frd;FA;").
Proof.
  intros A rd rs1 o H. unfold andm8_sh_step in H.
  destruct (bv_unsigned rd =? 0); [discriminate|].
  destruct (ax_base A); try discriminate. destruct (negb _); [discriminate|].
  destruct (rel_offset _ _) as [t|]; [|discriminate]. destruct (is_lit t || _); [discriminate|]. injection H as <-.
  cbn [shape_kept exts_kept]. rewrite exts_set_pc, exts_set_reg, exts_add_facts. split; [|apply exts_fresh].
  cbn. rewrite ss_next_set_reg, ss_lenient_set_reg. cbn. split; [lia | reflexivity].
Qed.

Lemma r3_out_kept : ltac2:(tb__ "0|1|
S1S92Q5A1S43S0S0S0S58S14eR6Sc2R6R5R4R3R2R1A6M0A2S14dR6G0A2A2Fl;Fb;Fq8;Ffast;Frd;FS;").
Proof using .
  intros S rd fast q8 b l. unfold r3_out. destruct fast; cbn [shape_kept exts_kept].
  - rewrite exts_set_pc, exts_set_reg. split; [|reflexivity]. cbn. rewrite ss_next_set_reg, ss_lenient_set_reg. split; [lia|reflexivity].
  - rewrite !exts_set_pc, !exts_set_reg. split; [|split; reflexivity].
    cbn. rewrite !ss_next_set_reg, !ss_lenient_set_reg. cbn. repeat split; try reflexivity; lia.
Qed.

Lemma r3_step_kept : ltac2:(tb__ "0|2|
Sa4S43S92Q5A1M0G0S92QcA1S61S57S44S61A1Sc3R6R5R4R3R2A5S46S61R1A2A3S58S14eSa3R7A1M1R2A2S14dG1R2A2A2F_;Fo;Fimm;Frs1;Frd;Fsgn;FA;").
Proof using .
  intros A sgn rd rs1 imm o H. unfold r3_step in H.
  destruct (rel_offset _ _) as [off|]; [|discriminate].
  destruct (granule_of _ off) as [[q8|g e|g e k]|]; [| | |discriminate].
  - destruct (find_xr _ _ _ _) as [[b l]|]; [|discriminate]. injection H as <-. apply r3_out_kept.
  - destruct (find_xr _ _ _ _) as [[b l]|]; [|discriminate]. injection H as <-. apply r3_out_kept.
  - destruct (find_xr _ _ _ _) as [[b l]|]; [|discriminate].
    match type of H with (if ?c then _ else _) = _ => destruct c; [|discriminate] end.
    injection H as <-. cbn [shape_kept exts_kept].
    rewrite exts_set_pc, exts_set_reg. split; [|reflexivity]. cbn. rewrite ss_next_set_reg, ss_lenient_set_reg. split; [lia|reflexivity].
Qed.

Lemma or_else_kept : ltac2:(tb__ "0|2|
Sa4S44S61A1M0S61S61S57G0R3S46S61R1A2A3S58S14eSa3R5A1M1R2A2S14dG1R2A2A2F_;Fr;S14eSa3R4A1R2A2S14dG1R3A2S14fR6SacR6SeaR5R4A2A2A2F_;F_;F_;Fd;Fo;FA;").
Proof using .
  intros A o d Ho Hs He. destruct o as [r|]; cbn.
  - destruct (Ho r eq_refl) as [H1 H2]. apply lift_out_kept; assumption.
  - apply lift_out_kept; assumption.
Qed.

Lemma lift_out_j_kept : ltac2:(tb__ "0|0|
Sa4S61S14eSa3R2A1R1A2S14dSa3R3A1R2A2S14fR4SbfR4R3A2A2F_;F_;Fo;FA;").
Proof using .
  intros A o Hs He. destruct o; cbn in *.
  - destruct Hs as [H1 H2]. repeat split; assumption || reflexivity.
  - destruct Hs as [[H1 H2] [H3 H4]]. destruct He as [E1 E2]. repeat split; assumption || reflexivity.
  - exact I.
Qed.

Lemma r3x_step_kept : ltac2:(tb__ "0|2|
Sa4S124S92Q5A1M0G0S92QcA1S61S57S44S61A1Sc5R6R5R4R3R2A5S46S61R1A2A3S58S14eSa3R7A1M1R2A2S14dG1R2A2A2F_;Fo;Fimm;Frs1;Frd;Fsz;FA;").
Proof.
  intros A sz rd rs1 imm o H. unfold r3x_step in H.
  destruct (rel_offset _ _) as [off|]; [|discriminate].
  destruct (granule_of _ off) as [d|]; [|discriminate].
  destruct (find_xr_d _ _ _) as [[b l]|]; [|discriminate].
  destruct (puleq _ _ _ _); [|discriminate]. injection H as <-.
  exact (r3_out_kept (ax_S A) rd true (q8_of d) b l).
Qed.

Lemma r3w_step_kept : ltac2:(tb__ "0|2|
Sa4S124S92Q5A1M0G0S92QcA1S61S57S44S61A1Sc4R6R5R4R3R2A5S46S61R1A2A3S58S14eSa3R7A1M1R2A2S14dG1R2A2A2F_;Fo;Fimm;Frs1;Frd;Fsz;FA;").
Proof.
  intros A sz rd rs1 imm o H. unfold r3w_step in H.
  destruct sz; try discriminate.
  destruct (r3w_target _ _) as [off|]; [|discriminate].
  destruct (negb _); [discriminate|].
  destruct (granule_of _ off) as [d|]; [|discriminate].
  destruct (find_xr_d _ _ _) as [[b l]|].
  - destruct (base_aligned8 A &&& _).
    + injection H as <-. exact (r3_out_kept (ax_S A) rd true (q8_of d) b l).
    + injection H as <-. cbn [shape_kept exts_kept]. rewrite exts_set_pc, exts_set_reg. split; [|apply exts_fresh].
      cbn. rewrite ss_next_set_reg, ss_lenient_set_reg. cbn. split; [lia | reflexivity].
  - destruct (r3w_lit_hit A off); [|discriminate].
    injection H as <-. cbn [shape_kept exts_kept]. rewrite exts_set_pc, exts_set_reg. split; [|apply exts_fresh].
    cbn. rewrite ss_next_set_reg, ss_lenient_set_reg. cbn. split; [lia | reflexivity].
Qed.

Lemma divpow2_step_kept : ltac2:(tb__ "0|1|
S1S125S92Q5A1M0G0G0S61S57S44S61A1SceR6R5R4R3R2A5S46S61R1A2A3S58S14eR7R2A2S14dR7R2A2A2F_;Fo;Frs2;Frs1;Frd;Fop;FS;").
Proof using .
  intros S op rd rs1 rs2 o H. unfold divpow2_step in H.
  destruct (get_reg S rs2); try discriminate. destruct (pow2_log _) as [k|]; [|discriminate].
  destruct op; try discriminate; injection H as <-; cbn [shape_kept exts_kept];
    rewrite exts_set_pc, exts_set_reg; (split; [|reflexivity]); cbn; rewrite ss_next_set_reg, ss_lenient_set_reg; (split; [lia|reflexivity]).
Qed.

Lemma zst_step_kept : ltac2:(tb__ "0|1|
S1S124S92Q5A1M0G0S92QcA1S61S57S44S61A1Se0R6R5R4R3R2A5S46S61R1A2A3S58S14eR7R2A2S14dR7R2A2A2F_;Fo;Fimm;Frs2;Frs1;Fsz;FS;").
Proof using .
  intros S sz rs1 rs2 imm o H. unfold zst_step in H.
  destruct (ss_resv S); [discriminate|]. destruct (get_reg S rs2); try discriminate.
  destruct (negb _); [discriminate|]. destruct (find_obj _ _ _ _ _) as [[[n o1] off]|]; [|discriminate].
  assert (GEN : forall o', (if dflt_writable (ob_dflt o1) && negb (is_arr (ob_dflt o1)) && existsb (fun c => is_zero_lit (c_val c)) (ob_cells o1)
                     then Some (StNext (set_pc (set_objs S (list_upd (ss_objs S) n
                             (fun o2 => obj_store_z (ss_facts S) o2 off (msz sz) (SLit z)))) (ss_pc S + 4)))
                     else None) = Some o' -> shape_kept S o' /\ exts_kept S o').
  { intros o' Ho'. destruct (_ && _); [|discriminate]. injection Ho' as <-.
    cbn [shape_kept exts_kept]. rewrite exts_set_pc. split; [cbn; split; [lia|reflexivity]|].
    unfold exts. cbn. apply map_ext_list_upd. intros o2. apply obj_ext_store_z. }
  destruct (ob_cells o1); [|exact (GEN o H)]. destruct (ob_dflt o1); try exact (GEN o H). injection H as <-.
  cbn [shape_kept exts_kept]. rewrite exts_set_pc. split; [|reflexivity]. cbn. split; [lia|reflexivity].
Qed.

Lemma sym_stepA_kept : ltac2:(tb__ "0|0|
Sa4S14fR1SdaVsegs;R1A2A2FA;").
Proof using .
  intros A. unfold sym_stepA.
  destruct (ss_lenient (ax_S A)) eqn:EL;
    pose proof (sym_step_shape segs (ax_S A)) as Hs; pose proof (sym_step_exts (ax_S A)) as He; [apply lift_out_kept; assumption|].
  destruct (instr_at segs (ss_pc (ax_S A))) as [i|]; [|apply lift_out_kept; assumption].
  destruct i; try (apply lift_out_kept; assumption).
  -   destruct sz;
      [ destruct (r3_step A signed rd rs1 imm) as [o|] eqn:Hr3; [|apply lift_out_kept; assumption];
        destruct (r3_step_kept _ _ _ _ _ _ Hr3) as [H1 H2]; apply lift_out_j_kept; assumption | | |];
      (destruct (r3x_step A _ rd rs1 imm) as [o|] eqn:Hr3;
         [destruct (r3x_step_kept _ _ _ _ _ _ Hr3) as [H1 H2]; apply lift_out_kept; assumption|];
       destruct (r3w_step A _ rd rs1 imm) as [o|] eqn:Hr4; [|apply lift_out_kept; assumption];
       destruct (r3w_step_kept _ _ _ _ _ _ Hr4) as [H1 H2]; apply lift_out_kept; assumption).
  -   apply or_else_kept; [intros r Hr; eapply zst_step_kept; exact Hr | assumption | assumption].
  -   destruct op; try (apply lift_out_kept; assumption).
    destruct (immI imm =? 7); [apply or_else_kept; [intros r Hr; eapply r2_step_kept; exact Hr | assumption | assumption]|].
    destruct (immI imm =? -8); [|apply lift_out_kept; assumption].
    apply or_else_kept; [| assumption | assumption].
    intros r Hr. destruct (andm8_sh_step A rd rs1) as [o|] eqn:Hsh8.
    + injection Hr as <-. eapply andm8_sh_step_kept; exact Hsh8.
    + eapply andm8_step_kept; exact Hr.
  -   destruct op; try (apply lift_out_kept; assumption).
    destruct ((bv_unsigned shamt =? 3) &&& _); [|apply lift_out_kept; assumption].
    apply or_else_kept; [intros r Hr; eapply r1_step_kept; exact Hr | assumption | assumption].
  -   apply or_else_kept; [intros r Hr; eapply divpow2_step_kept; exact Hr | assumption | assumption].
  -   apply lift_out_kept; [apply amo_step_shape | apply amo_step_exts].
Qed.

End Exts.

Definition shadow_addr (off : Z) (a : Z) : word := ltac2:(tb__ "0|0|
S94Q40S110Voff;S119Va;Z8A2A2A2").

Definition word_byte (z : Z) (j : Z) : word := ltac2:(tb__ "0|1|
S94Q40S110S114S119Vz;Z8M0A2G0A2Vj;A2A2").

Definition word_ok (rho : valuation) (objs : list sobj) (z : Z) : Prop := ltac2:(tb__ "0|2|
S5eS58S111Z0R1A2S116R1Z8A2A2S58S27Vrho;Vobjs;SdbVz;R2A2M0A3S5cS57S44S92Q8A1M1A1S34Vrho;G0A2S4cG1A1A3A1A2F_;Fj;").

Definition xr_ok (rho : valuation) (objs : list sobj) (off : Z) (r : sv * sv) : Prop := ltac2:(tb__ "0|9|
S93Q40M0ScVrho;S51S0S0Vr;A3A2A2S5eS93G0ScVrho;S4eS0S0Vr;A3A2A2S5eS58S57S5eS113R2Z8M1A2Z0M2A3S58S111S110R2R1A2S112Z2Z40A2M3A2S5eS58S111R3R1A2S116R1S110R3R2A2A2A2S58S58S111G2S110Voff;S119R2G1A2A2M4A2S116G4G3A2A2S58S27Vrho;Vobjs;Sf1Voff;R2A2A3S58Sf5Vrho;Vobjs;G4A3S5bS92Q8M5A1M6G6S58S57S44G6A1S34Vrho;Sf1Voff;R3A2A2S46G6R1A2A3S59S57S5eS93G5R1A2M7G2A3S58S57S5eG7S113S110R5R4A2M8G1A2A3S57S5eS119R3G1A2S119G8G1A2A3A2A2A2Lv;A2A2A2A2F_;Fa;A2A2TL;TB;").

Lemma word_byte_self : ltac2:(tb__ "0|1|
S5eS111Z0R1A2S57S92Q40M0A1SdbR2S113R2Z8A2A2S94G0R2A2A3F_;Fz;").
Proof. intros z Hz. unfold word_byte. f_equal. pose proof (Z.div_mod z 8 ltac:(lia)). lia. Qed.

Lemma word_ok_outside : ltac2:(tb__ "0|0|
S8S47S3A1S5eS111Z0R1A2Sf5R4R3R2A3S27R5R4S94Q40R3A2A3F_;F_;Fz;Fobjs;Frho;").
Proof.
  intros rho objs z Hz H. rewrite <- (word_byte_self z Hz). apply (proj1 (H (z mod 8) ltac:(pose proof (Z.mod_pos_bound z 8 ltac:(lia)); lia))).
Qed.

Lemma word_byte_range : ltac2:(tb__ "0|6|
S5eS5eS58S111Z0M0R2A2M1S116R2S112Z2Z40A2M2A2A2S58G1S116R2Z8M3A2A2S58S58S111G0S110S114S119R4G3A2G3A2M4R3A2M5A2S116G5G2A2A2S58S57S5eS93Q40SdbR4R3A2A2G5A3S58S111G4R4A2S116R4S110G4G3A2A2A2A2A2F_;F_;Fj;Fz;").
Proof.
  intros z j Hz Hj. pose proof (Z.div_mod z 8 ltac:(lia)). pose proof (Z.mod_pos_bound z 8 ltac:(lia)).
  assert (B : 0 <= z / 8 * 8 + j < 2 ^ 64).
  { split; [nia|]. assert (z / 8 <= (2 ^ 64 - 1) / 8) by (apply Z.div_le_mono; lia). change ((2 ^ 64 - 1) / 8) with (2 ^ 61 - 1) in H1. lia. }
  split; [exact B|]. split; [unfold word_byte; rewrite Z_to_bv_unsigned; apply bv_wrap_small; change (bv_modulus 64) with (2 ^ 64); lia | lia].
Qed.

Lemma word_outside_aligned_range : ltac2:(tb__ "0|5|
S5eS5eS5eS5eS111Z0M0R4A2M1S58G1S116R4Z8M2A2A2S57S5eS113R4G2A2G0A3M3G3S5cS58S111R6R8A2S116R8R5A2A2A1S5cS58S111R7S110S114S119R9G2A2G2A2R8A2M4A2S116G4R6A2A2A1F_;F_;F_;F_;F_;Fhi;Flo;Fj;Fz;").
Proof.
  intros z j lo hi Hz Hj Hlo Hhi Hout Hin.
  pose proof (Z.div_mod z 8 ltac:(lia)). pose proof (Z.mod_pos_bound z 8 ltac:(lia)).
  pose proof (Z.div_mod lo 8 ltac:(lia)). rewrite Hlo in H1. pose proof (Z.div_mod hi 8 ltac:(lia)). rewrite Hhi in H2.
  apply Hout. nia.
Qed.

Definition shadow_ok (rho : valuation) (A : axst) : Prop := ltac2:(tb__ "0|0|
S155S45S0S0A2SddVrho;S11Sa3VA;A1A1S93Q40ScVrho;Sa9VA;A1A2A2A3SaaVA;A1A3").

Lemma outside_all_exts : ltac2:(tb__ "0|2|
S5fS8S8S47S3A1M0G0S92Q40A1S57S47S45S45S0S0A2S0A2M1A1S156S3G1Sb0R2A4S156S3G1Sb0R3A4A3S57S43S14aS3S26R7A1R4A3S48A3S2cR8R7R6A3S27R8R6R4A3S27R8R6R5A3F_;F_;F_;F_;Fa;Fobjs';Fobjs;Frho';Frho;Fn;").
Proof.
  intros n rho rho' objs. induction objs as [|o t IH]; intros [|o' t'] a Hm Hwf Hag Hout; cbn [map] in Hm; try discriminate.
  - constructor.
  - assert (Ho : obj_ext o' = obj_ext o) by (injection Hm; intros; unfold obj_ext; congruence).
    assert (Ht : map obj_ext t' = map obj_ext t) by (injection Hm; intros; assumption).
    cbn in Hwf. apply andb_prop in Hwf as [Hwo Hwt].
    inversion Hout; subst. constructor.
    + cbn zeta in *.
      assert (E : obj_range rho' o' = obj_range rho o).
      { rewrite <- (obj_range_agree n rho rho' o Hag Hwo).
        destruct o as [b lo hi cs d], o' as [b' lo' hi' cs' d']. unfold obj_ext in Ho. cbn in Ho. inversion Ho; subst. reflexivity. }
      rewrite E. assumption.
    + apply IH; assumption.
Qed.

Lemma xr_ok_stable : ltac2:(tb__ "0|3|
S5fS8S8S47S3A1M0G0S5eS45S0S0A2M1S2cR7R6R5A3S57S43Sf6R8R2A2S48A3S57S47S45G1S0A2M2A1S156S3G2Sb0R5A4S156S3G2Sb0R6A4A3S57S43S14aS3S26RaA1R7A3S48A3SddRaR8R6R5A4SddRaR8R7R6A4F_;F_;F_;F_;F_;Fr;Foff;Fobjs';Fobjs;Frho';Frho;Fn;").
Proof.
  intros n rho rho' objs objs' off [b l] Hag Hb Hm Hwf H. unfold xr_below in Hb. cbn [fst snd] in Hb.
  apply andb_prop in Hb as [Hb Hl].
  unfold xr_ok in H |- *. cbn [fst snd] in H |- *.
  rewrite <- (eval_agree n rho rho' b Hag Hb), <- (eval_agree n rho rho' l Hag Hl).
  destruct H as (H8 & Hnw & H). split; [exact H8|]. split; [exact Hnw|].
  intros a Ha. destruct (H a Ha) as (Hoff & Hout & Hw & v & Hv & Henc).
  split; [exact Hoff|]. split; [eapply outside_all_exts; eauto|]. split.
  - intros j Hj. destruct (Hw j Hj) as [Ho Hr]. split; [eapply outside_all_exts; eauto|].
    destruct Hag as (_ & _ & Hrm). rewrite <- Hrm. exact Hr.
  - exists v. split; [|exact Henc]. destruct Hag as (_ & _ & Hrm). rewrite <- Hrm. exact Hv.
Qed.

Lemma shadow_ok_stable : ltac2:(tb__ "0|2|
Sa4Sa4S8S8S2cS9Sa3R4A1A1R2R1A3S57S43Sb4R5A1S48A3S57S43S22Sa3R6A1A1S48A3S57S47S45S0S0A2M0A1SaaR6A1SaaR7A1A3S57S0Sa9R7A1Sa9R8A1A3S57S47S45G0S0A2A1Sa8Sa3R8A1A1Sa8Sa3R9A1A1A3Sf2R8RaA2M1G1F_;F_;F_;F_;F_;F_;F_;Frho';Frho;FA';FA;").
Proof.
  intros A A' rho rho' Hag Hwf Hswf HX Hb He H. unfold shadow_ok in H |- *.
  unfold axwf in Hwf. apply andb_prop in Hwf as [HwX Hwb].
  rewrite HX, Hb. rewrite <- (eval_agree _ rho rho' _ Hag Hwb).
  apply Forall_forall. intros r Hr. pose proof (proj1 (Forall_forall _ _) H r Hr) as Hok.
  eapply (xr_ok_stable (ss_next (ax_S A))); [exact Hag | | exact He | apply swf_objs; exact Hswf | exact Hok].
  exact (proj1 (forallb_forall _ _) HwX r Hr).
Qed.

Lemma axwf_stable : ltac2:(tb__ "0|0|
Sa4Sa4S57S43Sb4R2A1S48A3S1aeS9Sa3R3A1A1S9Sa3R2A1A1A2S57S47S45S0S0A2A1SaaR3A1SaaR4A1A3S57S0Sa9R4A1Sa9R5A1A3S57S43Sb4R5A1S48A3F_;F_;F_;F_;FA';FA;").
Proof.
  intros A A' H Hle HX Hb. unfold axwf in H |- *. rewrite HX, Hb. apply andb_prop in H as [H1 H2].
  apply andb_true_intro. split.
  - apply forallb_forall. intros r Hr. pose proof (proj1 (forallb_forall _ _) H1 r Hr) as Hr'.
    unfold xr_below in Hr' |- *. apply andb_prop in Hr' as [Ha Hb']. apply andb_true_intro.
    split; eapply sv_below_mono; eauto.
  - eapply sv_below_mono; eauto.
Qed.

Section RSound.
Variable segs : list Segment.

Lemma U_SLit : ltac2:(tb__ "0|0|
S8S5eS58S111Z0R1A2S116R1S112Z2Z40A2A2A2S57S5eS120R3S5R2A1A2R2A3F_;Fz;Frho;").
Proof. intros rho z Hz. unfold U. cbn [eval]. rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite two64. apply Z.mod_small. exact Hz. Qed.

Lemma U_g8 : ltac2:(tb__ "0|0|
S8S5fS111S120R2SdR1A1A2S118S112Z2Z3dA2Z1A2A2S57S5eS120R3SabR2A1A2S114Z8S120R3SdR2A1A2A2A3F_;Fg;Frho;").
Proof.
  intros rho g Hq. unfold U in *. cbn [eval g8] in Hq |- *. rewrite sll_val. change (3 mod 64) with 3.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
  pose proof (urange (rw rho g)). rewrite Z.mod_small by lia. lia.
Qed.

Lemma U_add : ltac2:(tb__ "0|0|
S8S0S0S57S5eS120R3SaS123R2R1A3A2S113S110S120R3R2A2S120R3R1A2A2S112Z2Z40A2A2A3Fb;Fa;Frho;").
Proof. intros. unfold U. cbn [eval]. apply add_val. Qed.

Definition pv_ok (rho : valuation) (pv : prov) : Prop := ltac2:(tb__ "0|2|
S58S155S2S14Vrho;A1Sb1Vpv;A1A3S58S1bfVrho;SecVpv;A1M0A2S58S1bfVrho;SedVpv;A1M1A2S58S15bSeeVpv;A1G0A2S15bSefVpv;A1G1A2A2A2A2A2").

Lemma mk_prov_ok : ltac2:(tb__ "0|0|
S8S47S2A1S155S2S14R2A1R1A3S15dR3SafR2A1A2F_;Ffacts;Frho;").
Proof.
  intros rho facts Hf. split; [exact Hf|]. split; [apply ctx0_dg_ok; exact Hf|]. split; [apply mk_dig_ok; exact Hf|].
  split; right; reflexivity.
Qed.

Lemma puleq_sound : ltac2:(tb__ "0|0|
S8Sa6S0S5eS0S15dR5R4A2S57S43Sa7R5R4R3R2A4S48A3S111S110S120R7R5A2R4A2S120R7R3A2A2F_;F_;Fb;Fk;Fa;Fpv;Frho;").
Proof.
  intros rho pv a k b (Hf & Hc & Hd & Hu0 & Hud) H. unfold puleq in H.
  rewrite (uleq_d_o_eq _ _ _ _ _ Hu0), (uleq_d_o_eq _ _ _ _ _ Hud) in H.
  apply lazy_orb_prop in H as [H|H];
    [exact (uleq_d_sound rho _ a k b Hc H) | exact (uleq_d_sound rho _ a k b Hd H)].
Qed.

Lemma lazy_andb_prop : ltac2:(tb__ "0|0|
S43S43S57S43S43S43L_;R2R1S49X43x2S48A3S58S57S43R3S48A3S57S43R2S48A3A2F_;Fb;Fa;").
Proof. intros [|] [|] H; cbn in H; auto; discriminate. Qed.

Lemma has_facts_sound : ltac2:(tb__ "0|1|
S8S47S2A1M0G0S155S2S14R3A1R1A3S57S43SbeR3R2A2S48A3S155S2S14R5A1R4A3F_;F_;Ffacts;Ffs;Frho;").
Proof.
  intros rho fs facts Hf H. unfold has_facts in H. apply Forall_forall. intros f Hin.
  pose proof (proj1 (forallb_forall _ _) H f Hin) as Hx. apply existsb_exists in Hx as (f' & Hf' & Heq).
  apply sprop_eqb_sound in Heq. subst f'. exact (proj1 (Forall_forall _ _) Hf _ Hf').
Qed.

Lemma granule_facts_sound : ltac2:(tb__ "0|6|
S8S5fS0S111S120R3SabR2A1A2S120R3R1A2A2S111S120R4R2A2S120R4SaS123SabR3A1S5Z7M0A1A3A2A2S111S120R5SdR4A1A2S118S112Z2Z3dA2Z1A2M1A2S58S57S5eS120R6SdR5A1A2M2S119S120R6R4A2M3Z8M4A2A3S58S58S111S114G4G2A2M5G3A2S111G3S110G5G0A2A2A2S111G2G1A2A2A2F_;F_;F_;Fe;Fg;Frho;").
Proof.
  intros rho g e A1 A2 A3.
  rewrite (U_g8 rho g) in A1 by lia.
  assert (E7 : U rho (SAlu ALU_ADD (g8 g) (SLit 7)) = 8 * U rho (SVar g) + 7).
  { rewrite U_add, (U_g8 rho g) by lia. rewrite (U_SLit rho 7) by lia. pose proof (urange (rw rho g)). unfold U in A3 |- *. cbn [eval] in A3 |- *.
    rewrite Z.mod_small; lia. }
  rewrite E7 in A2. split; [|lia].
  apply (Z.div_unique (U rho e) 8 (U rho (SVar g)) (U rho e - 8 * U rho (SVar g))); lia.
Qed.

Lemma granule_ok_sound : ltac2:(tb__ "0|4|
S8Sa6S5fS0S15dR4R3A2S57S43Sd3R4R3R2A3S48A3S58S57S5eS120R6SdR4A1A2M0S119S120R6R3A2M1Z8M2A2A3S58S58S111S114G2G0A2M3G1A2S111G1S110G3Z7A2A2A2S111G0S118S112Z2Z3dA2Z1A2A2A2A2F_;F_;Fe;Fg;Fpv;Frho;").
Proof.
  intros rho pv g e Hpv H. pose proof Hpv as (Hf & _ & _). unfold granule_ok in H. apply lazy_orb_prop in H as [H|H].
  - pose proof (has_facts_sound rho _ _ Hf H) as HF. unfold F8 in HF.
    inversion HF as [|? ? A1 HF2]; subst. inversion HF2 as [|? ? A2 HF3]; subst. inversion HF3 as [|? ? A3 _]; subst.
    cbn [holds] in A1, A2, A3. apply granule_facts_sound; unfold U; try exact A1; try exact A2.
    change (eval rho (SLit (2 ^ 61 - 1))) with (Z_to_bv 64 (2 ^ 61 - 1)) in A3. exact A3.
  - apply lazy_andb_prop in H as [H H3]. apply lazy_andb_prop in H as [H1 H2].
    pose proof (puleq_sound rho pv _ _ _ Hpv H1) as A1. pose proof (puleq_sound rho pv _ _ _ Hpv H2) as A2.
    pose proof (puleq_sound rho pv _ _ _ Hpv H3) as A3. rewrite (U_SLit rho (2 ^ 61 - 1)) in A3 by lia.
    apply granule_facts_sound; lia.
Qed.

Lemma granule_eq_ok_sound : ltac2:(tb__ "0|1|
S8Sa6S5fS0S15dR4R3A2S57S43Sd1R4R3R2A3S48A3S14R6S1fSabR4A1R3A2A2S58S57S5eS120R7R4A2S114Z8S120R7SdR5A1A2M0A2A3S111G0S118S112Z2Z3dA2Z1A2A2A2F_;F_;F_;Fe0;Fg;Fpv;Frho;").
Proof.
  intros rho pv g e0 Hpv H He. pose proof Hpv as (Hf & _ & _). unfold granule_eq_ok in H.
  assert (A3 : U rho (SVar g) <= 2 ^ 61 - 1).
  { apply lazy_orb_prop in H as [H|H].
    - pose proof (has_facts_sound rho _ _ Hf H) as HF. unfold FE in HF.
      inversion HF as [|? ? _ HF2]; subst. inversion HF2 as [|? ? A3 _]; subst. cbn [holds] in A3.
      unfold U. cbn [eval]. change (eval rho (SLit (2 ^ 61 - 1))) with (Z_to_bv 64 (2 ^ 61 - 1)) in A3. exact A3.
    - pose proof (puleq_sound rho pv _ _ _ Hpv H) as A3. rewrite (U_SLit rho (2 ^ 61 - 1)) in A3 by lia. lia. }
  cbn [holds] in He. fold (g8 g) in He. split; [|exact A3].
  rewrite <- (U_g8 rho g) by lia. unfold U. rewrite He. reflexivity.
Qed.

Local Ltac lit3 z REST H :=
  destruct (Z.eq_dec z 3) as [->|Hz];
  [| destruct z as [|p|p]; try (apply REST; exact H); destruct p as [p|p|]; try (apply REST; exact H);
     try (destruct p as [p|p|]; try (apply REST; exact H)); try (destruct p; try (apply REST; exact H)); exfalso; apply Hz; reflexivity].

Lemma find_granule_In : ltac2:(tb__ "0|0|
Sa6S47S2A1S0S5fS57S44S5fA1Sb6R4R3R2A3S46S5fR1A2A3S58S57S43Sd3R5R2R3A3S48A3S5bS0S0S149S2S10SabR3A1R1A2R5A3Le';A2A2F_;Fg;Fe;Ffacts;Fpv;").
Proof.
  intros pv facts e g. induction facts as [|f rest IH]; intros H; [discriminate|].
  cbn [find_granule] in H.
  assert (REST : find_granule pv rest e = Some g -> granule_ok pv g e = true /\ exists e', In (SPUle (g8 g) e') (f :: rest)).
  { intros Hr. destruct (IH Hr) as [A [e' B]]. split; [exact A | exists e'; right; exact B]. }
  destruct f; try (apply REST; exact H).
  destruct a; try (apply REST; exact H). destruct op; try (apply REST; exact H).
  destruct a1; try (apply REST; exact H). destruct a2; try (apply REST; exact H).
  lit3 z REST H.
  destruct (sv_eqb b e &&& granule_ok pv i e) eqn:E; [|apply REST; exact H].
  injection H as ->. apply lazy_andb_prop in E as [E1 E2]. split; [exact E2 | exists b; left; reflexivity].
Qed.

Lemma find_granule_eq_sound : ltac2:(tb__ "0|0|
Sa6S47S2A1S0S5fS57S44S5fA1ScfR4R3R2A3S46S5fR1A2A3S58S57S43Sd1R5R2R3A3S48A3S149S2S1fSabR2A1R3A2R4A3A2F_;Fg;Fe0;Ffacts;Fpv;").
Proof.
  intros pv facts e0 g. induction facts as [|f rest IH]; intros H; [discriminate|].
  cbn [find_granule_eq] in H.
  assert (REST : find_granule_eq pv rest e0 = Some g -> granule_eq_ok pv g e0 = true /\ In (SPEq (g8 g) e0) (f :: rest)).
  { intros Hr. destruct (IH Hr) as [A B]. split; [exact A | right; exact B]. }
  destruct f; try (apply REST; exact H).
  destruct a; try (apply REST; exact H). destruct op; try (apply REST; exact H).
  destruct a1; try (apply REST; exact H). destruct a2; try (apply REST; exact H).
  lit3 z REST H.
  destruct (sv_eqb b e0 &&& granule_eq_ok pv i e0) eqn:E; [|apply REST; exact H].
  injection H as ->. apply lazy_andb_prop in E as [E1 E2]. apply sv_eqb_sound in E1. subst b.
  split; [exact E2 | left; reflexivity].
Qed.

Lemma granule_expr_sound : ltac2:(tb__ "0|2|
Sa6S47S2A1S5fS53S0S0A2M0S57S44G0A1Sd2R4R3R2A3S46G0R1A2A3G0OLr;R2S0S58S57S43Sd3R6R4R1A3S48A3S149S2S10SabR4A1M1R1A2R5A3A2Le;S0S58S57S43Sd1R6R4R1A3S48A3S149S2S1fG1R1A2R5A3A2Le0;X53x2F_;Fr;Fg;Ffacts;Fpv;").
Proof.
  intros pv facts g r. induction facts as [|f rest IH]; intros H; [discriminate|].
  cbn [granule_expr] in H.
  assert (REST : granule_expr pv rest g = Some r ->
            match r with
            | inl e => granule_ok pv g e = true /\ In (SPUle (g8 g) e) (f :: rest)
            | inr e0 => granule_eq_ok pv g e0 = true /\ In (SPEq (g8 g) e0) (f :: rest)
            end).
  { intros Hr. pose proof (IH Hr) as X. destruct r; destruct X as [A B]; split; [exact A | right; exact B | exact A | right; exact B]. }
  destruct f; try (apply REST; exact H).
  - destruct a; try (apply REST; exact H). destruct op; try (apply REST; exact H).
    destruct a1; try (apply REST; exact H). destruct a2; try (apply REST; exact H).
    lit3 z REST H.
    destruct (Pos.eqb i g &&& granule_ok pv g b) eqn:E; [|apply REST; exact H].
    injection H as <-. apply lazy_andb_prop in E as [E1 E2]. apply Pos.eqb_eq in E1. subst i. split; [exact E2 | left; reflexivity].
  - destruct a; try (apply REST; exact H). destruct op; try (apply REST; exact H).
    destruct a1; try (apply REST; exact H). destruct a2; try (apply REST; exact H).
    lit3 z REST H.
    destruct (Pos.eqb i g &&& granule_eq_ok pv g b) eqn:E; [|apply REST; exact H].
    injection H as <-. apply lazy_andb_prop in E as [E1 E2]. apply Pos.eqb_eq in E1. subst i. split; [exact E2 | left; reflexivity].
Qed.

Lemma fact_below_parts : ltac2:(tb__ "0|0|
S5fS47S2A1S2S57S43S14aS2S1aR3A1R2A3S48A3S149S2R2R3A3S57S43S1aR5R3A2S48A3F_;F_;Fp;Ffacts;Fn;").
Proof. intros n facts p Hwf Hin. exact (proj1 (forallb_forall _ _) Hwf _ Hin). Qed.

Lemma g8_fact_bounds : ltac2:(tb__ "0|0|
S5fS47S2A1S5fS0S57S43S14aS2S1aR4A1R3A3S48A3S149S2S10SabR3A1R2A2R4A3S58S1afR4R6A2S57S43SbR6R3A2S48A3A2F_;F_;Fe;Fg;Ffacts;Fn;").
Proof.
  intros n facts g e Hwf Hin. pose proof (fact_below_parts _ _ _ Hwf Hin) as H.
  cbn in H. apply andb_prop in H as [H1 H2]. apply andb_prop in H1 as [H1 _]. split; [apply Pos.ltb_lt; exact H1 | exact H2].
Qed.

Lemma g8_eqfact_bounds : ltac2:(tb__ "0|0|
S5fS47S2A1S5fS0S57S43S14aS2S1aR4A1R3A3S48A3S149S2S1fSabR3A1R2A2R4A3S58S1afR4R6A2S57S43SbR6R3A2S48A3A2F_;F_;Fe;Fg;Ffacts;Fn;").
Proof.
  intros n facts g e Hwf Hin. pose proof (fact_below_parts _ _ _ Hwf Hin) as H.
  cbn in H. apply andb_prop in H as [H1 H2]. apply andb_prop in H1 as [H1 _]. split; [apply Pos.ltb_lt; exact H1 | exact H2].
Qed.

Lemma swf_facts : ltac2:(tb__ "0|0|
S1S57S43S22R1A1S48A3S57S43S14aS2S1aS9R2A1A1S4R2A1A3S48A3F_;FS;").
Proof.
  intros S H. unfold swf in H. repeat (apply andb_prop in H as [H ?]). assumption.
Qed.

Lemma xr_rel_hit_sound : ltac2:(tb__ "0|1|
S8Sa6S0S0S0S5eS15dR6R5A2S57S43Sc8R6R5R4R3R2A5S48A3S58S111S110S120R8R6A2S11bR3A1A2S120R8R4A2M0A2S111S110G0S110R3Z1A2A2S120R8SaS123R6R5A3A2A2A2F_;F_;Fd;Fe;Fl;Fb;Fpv;Frho;").
Proof.
  intros rho pv b l e d Hpv H. unfold xr_rel_hit in H.
  destruct (rel_offset b e) as [off|] eqn:Hro; [|discriminate].
  apply lazy_andb_prop in H as [Hd H]. apply Z.leb_le in Hd. apply lazy_andb_prop in H as [H1 H2].
  pose proof (puleq_sound rho _ _ _ _ Hpv H1) as P1. pose proof (puleq_sound rho _ _ _ _ Hpv H2) as P2.
  pose proof (rel_offset_sound rho _ _ _ Hro) as Ue.
  pose proof (urange (eval rho b)) as Rb. change (bv_unsigned (eval rho b)) with (U rho b) in Rb.
  pose proof (urange (eval rho l)) as Rl. change (bv_unsigned (eval rho l)) with (U rho l) in Rl.
  pose proof (urange (eval rho off)) as Ro. change (bv_unsigned (eval rho off)) with (U rho off) in Ro.
  assert (Us : U rho (SAlu ALU_SUB (SLit (2 ^ 64 - 1)) b) = 2 ^ 64 - 1 - U rho b).
  { unfold U. cbn [eval]. rewrite sub_val. change (bv_unsigned (Z_to_bv 64 (2 ^ 64 - 1))) with (2 ^ 64 - 1).
    fold (U rho b). apply Z.mod_small. lia. }
  rewrite Us in P2.
  assert (Ue' : U rho e = U rho b + U rho off) by (rewrite Ue; apply Z.mod_small; lia).
  rewrite U_add. rewrite (Z.mod_small (U rho b + U rho l)) by lia. lia.
Qed.

Lemma find_xr_sound : ltac2:(tb__ "0|2|
S8Sa6S47S45S0S0A2M0A1S0S5eS0S0S15dR7R6A2S57S44G0A1Sb7R7R6R5R4A4S46G0S4bS0S0R3R2A4A2A3S58S149G0S4bS0S0R4R3A4R7A3S58S111S110S120R9R4A2S11bR5A1A2S120R9R6A2M1A2S111S110G1S110R5Z1A2A2S120R9SaS123R4R3A3A2A2A2A2F_;F_;Fl;Fb;Fd;Fe;FX;Fpv;Frho;").
Proof.
  intros rho pv X e d b l Hpv. induction X as [|[b0 l0] rest IH]; intros H; [discriminate|].
  cbn [find_xr] in H.
  destruct ((puleq pv b0 (- d) e &&& puleq pv e (d + 1) (SAlu ALU_ADD b0 l0)) ||| xr_rel_hit pv b0 l0 e d) eqn:E.
  - injection H as <- <-. split; [left; reflexivity|]. apply lazy_orb_prop in E as [E|E].
    + apply lazy_andb_prop in E as [E1 E2]. split; [exact (puleq_sound rho _ _ _ _ Hpv E1) | exact (puleq_sound rho _ _ _ _ Hpv E2)].
    + exact (xr_rel_hit_sound rho pv _ _ e d Hpv E).
  - destruct (IH H) as (A & B & C). split; [right; exact A|]. split; assumption.
Qed.

Lemma split_lit_sound : ltac2:(tb__ "0|0|
S8S0S0S5eS57S45S0S5eA2Sd8R3A1S4bS0S5eR2R1A4A3S58S57S5eS120R5R4A2S113S110S120R5R3A2R2A2S112Z2Z40A2A2A3S5fS57S43SbR1R5A2S48A3S57S43SbR2R5A2S48A3F_;Fn;A2F_;Fc;Fe0;Fe;Frho;").
Proof.
  intros rho e e0 c H. unfold split_lit in H.
  assert (DFLT : (e, 0) = (e0, c) -> U rho e = (U rho e0 + c) mod 2 ^ 64 /\ (forall n, sv_below n e = true -> sv_below n e0 = true)).
  { intros E. injection E as <- <-. split; [|auto]. rewrite Z.add_0_r. symmetry. apply Z.mod_small. apply urange. }
  destruct e; try (apply DFLT; exact H). destruct op; try (apply DFLT; exact H). destruct e2; try (apply DFLT; exact H).
  injection H as <- <-. split.
  - rewrite U_add. assert (UL : U rho (SLit z) = z mod 2 ^ 64).
    { unfold U. cbn [eval]. rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite two64. reflexivity. }
    rewrite UL. rewrite Zplus_mod_idemp_r. reflexivity.
  - intros n Hb. cbn in Hb. apply andb_prop in Hb as [Hb _]. exact Hb.
Qed.

Lemma srl3_val : ltac2:(tb__ "0|2|
S8S0S92Q6M0A1S57S5eS93G0R1A2Z3A3S57S5eS93Q40M1S1b5S129ScR4R3A2S1bdG0G1R2A3A3A2S119S120R4R3A2Z8A2A3F_;Fsh;Fe;Frho;").
Proof.
  intros rho e sh Hsh. change (zext 64 sh) with (Z_to_bv 64 (bv_unsigned sh)). rewrite Hsh, srl_val. change (3 mod 64) with 3.
  rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Lemma case_r1_val : ltac2:(tb__ "0|3|
S1S92Q5A1M0G0S92Q6M1A1S0S8S47S153A1M2S143S154S57S44S122A1S67Vsegs;S6R9A1A2S46S122S130S129R8R7R6A4A2A3S57S5eS93G1R7A2Z3A3S57S43SbS9RbA1R7A2S48A3S57S5eS120R7R8A2S119S120R7S63RcRaA2A2Z8A2A3S12Vsegs;R8RdS4bG2S151R7S152R6R5A2A4A4S142Vsegs;ReS62S65ReRdRaA3S110S6ReA1Z4A2A2R9R8R7R6A7F_;F_;F_;F_;F_;Fmd;Fms;Ftr;Frho;Fe;Fsh;Frs1;Frd;FS;").
Proof.
  intros S rd rs1 sh e rho tr ms md Hi Hsh Hb Hv Hsm.
  eapply step_rd_sound; [exact Hsm | exact Hi | discriminate | reflexivity | eapply npc_eq; eauto | exact Hb |].
  apply bv_eq. change (bv_unsigned (eval rho e)) with (U rho e). rewrite Hv.
  rewrite (rget_match segs rho S tr ms md rs1 Hsm). symmetry. apply srl3_val. exact Hsh.
Qed.

Lemma case_r1_freshF : ltac2:(tb__ "0|7|
S1S92Q5A1M0G0S92Q6M1A1S47S2A1S5fS0F_;S92Q40M2A1M3S8S47S153A1M4S143S154S57S44S122A1S67Vsegs;S6RbA1A2S46S122S130S129RaR9R8A4A2A3S57S5eS93G1R9A2Z3A3S12Vsegs;R6RdS4bG4S151R5S152R4R3A2A4A4S9ReA1S5fS1beR8R1R9A3S8S58S155S2S14R1A1RcA3S58S57S43S14aS2S1aS1b1R2A1M5A1RcA3S48A3S58S57S43SbG5RbR2A1M6A2S48A3S57G3ScR1G6A2S1b5S129ScR9S63R10ReA2A2S1bdG1G2RdA3A3A3A2A2A2Trho';Tg;S142Vsegs;RfS62S65S15fRbS4eS0S1S6bRfA1A3A2ReRaS9RfA1A1A3S110S6RfA1Z4A2A2R8R7R6R5A7F_;F_;F_;F_;Fmd;Fms;Ftr;Frho;Fgval;Fmk;FF;Fsh;Frs1;Frd;FS;").
Proof.
  intros S rd rs1 sh F mk gval rho tr ms md Hi Hsh Hsm (HF & HFb & Hmk & Hval).
  pose proof (smatch_swf segs _ _ _ Hsm) as Hwf.
  set (g := ss_next S) in *. set (rho' := ext1 rho g gval) in *.
  pose proof (ext1_agree rho g gval) as Hag. fold rho' in Hag.
  pose proof (smatch_agree segs rho rho' S _ Hag Hsm) as Hsm1.
  assert (HsmF : smatch segs rho' (snd (fresh S)) (tr, mkCfg ms md)).
  { destruct Hsm1 as (_ & Hpc & Hpend & Hhalt & Hrom & Hroc & Hr1 & Hfr1 & Hc1 & Hv1 & Hm1 & Hfa1).
    unfold smatch. cbn [fst snd cfg_ms cfg_model fresh ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next ss_lenient].
    split; [apply swf_fresh; exact Hwf|]. repeat (split; [assumption|]). exact Hfa1. }
  set (S1 := add_facts F (snd (fresh S))).
  assert (Hsm2 : smatch segs rho' S1 (tr, mkCfg ms md)).
  { unfold S1. apply smatch_add_facts; [exact HsmF | exact HF | exact HFb]. }
  pose proof (smatch_swf segs _ _ _ Hsm2) as Hwf2.
  pose proof Hsm2 as Hsm3. destruct Hsm3 as (_ & Hpc & _ & _ & _ & _ & Hr1 & Hfr1 & Hc1 & Hv1 & _).
  cbn [fst snd cfg_ms cfg_model] in *.
  eapply (next_rel_core1 segs rho rho' S S1); try eassumption.
  - discriminate.
  - cbn [exec]. reflexivity.
  - cbn. rewrite ss_next_set_reg. cbn. lia.
  - rewrite swf_set_pc. apply swf_set_reg; [exact Hwf2|]. cbn. exact Hmk.
  - cbn [ss_pc set_pc]. unfold rset, with_pc, with_regs, core_of; destruct (is_x0 rd); cbn [c_pc]; unfold ms_pc in Hpc; rewrite Hpc; apply pc_plus'.
  - eapply (regs_match_same rho' (set_reg S1 rd (mk g))); [| reflexivity | reflexivity].
    eapply (regs_match_rset_gen rho' S1 _ ms); [exact Hwf2 | exact Hr1 | | cbn [ms_regs ms_of]; apply c_regs_rset; reflexivity].
    rewrite Hval. rewrite (rget_match segs rho S tr ms md rs1 Hsm). reflexivity.
  - eapply fregs_match_same; [exact Hfr1 | | cbn [ss_fregs set_pc]; rewrite ss_fregs_set_reg; reflexivity].
    unfold rset; destruct (is_x0 rd); reflexivity.
  - cbn [ss_fcsr set_pc]. rewrite ss_fcsr_set_reg. unfold fcsr_match in Hc1 |- *. unfold rset; destruct (is_x0 rd); cbn; exact Hc1.
  - cbn [ss_resv set_pc]. rewrite ss_resv_set_reg. unfold resv_match in Hv1 |- *. unfold rset; destruct (is_x0 rd); cbn; exact Hv1.
  - cbn [ss_objs set_pc]. rewrite ss_objs_set_reg. reflexivity.
  - cbn [ss_facts set_pc]. rewrite ss_facts_set_reg. reflexivity.
Qed.

Lemma case_opimm_freshF : ltac2:(tb__ "0|7|
S1S121S92Q5A1M0G0S92QcM1A1S47S2A1S5fS0F_;S92Q40M2A1M3S8S47S153A1M4S143S154S57S44S122A1S67Vsegs;S6RcA1A2S46S122S12fRbRaR9R8A4A2A3S12Vsegs;R5RdS4bG4S151R4S152R3R2A2A4A4S9ReA1S5fS1beR7R1R8A3S8S58S155S2S14R1A1RbA3S58S57S43S14aS2S1aS1b1R2A1M5A1RbA3S48A3S58S57S43SbG5RaR2A1M6A2S48A3S57G3ScR1G6A2S1b5RfScR8S63R10RdA2A2S1bcG1G2RcA3A3A3A2A2A2Trho';Tg;S142Vsegs;RfS62S65S15fRaS4eS0S1S6bRfA1A3A2RdR9S9RfA1A1A3S110S6RfA1Z4A2A2R7R6R5R4A7F_;F_;F_;Fmd;Fms;Ftr;Frho;Fgval;Fmk;FF;Fimm;Frs1;Frd;Fop;FS;").
Proof.
  intros S op rd rs1 imm F mk gval rho tr ms md Hi Hsm (HF & HFb & Hmk & Hval).
  pose proof (smatch_swf segs _ _ _ Hsm) as Hwf.
  set (g := ss_next S) in *. set (rho' := ext1 rho g gval) in *.
  pose proof (ext1_agree rho g gval) as Hag. fold rho' in Hag.
  pose proof (smatch_agree segs rho rho' S _ Hag Hsm) as Hsm1.
  assert (HsmF : smatch segs rho' (snd (fresh S)) (tr, mkCfg ms md)).
  { destruct Hsm1 as (_ & Hpc & Hpend & Hhalt & Hrom & Hroc & Hr1 & Hfr1 & Hc1 & Hv1 & Hm1 & Hfa1).
    unfold smatch. cbn [fst snd cfg_ms cfg_model fresh ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next ss_lenient].
    split; [apply swf_fresh; exact Hwf|]. repeat (split; [assumption|]). exact Hfa1. }
  set (S1 := add_facts F (snd (fresh S))).
  assert (Hsm2 : smatch segs rho' S1 (tr, mkCfg ms md)).
  { unfold S1. apply smatch_add_facts; [exact HsmF | exact HF | exact HFb]. }
  pose proof (smatch_swf segs _ _ _ Hsm2) as Hwf2.
  pose proof Hsm2 as Hsm3. destruct Hsm3 as (_ & Hpc & _ & _ & _ & _ & Hr1 & Hfr1 & Hc1 & Hv1 & _).
  cbn [fst snd cfg_ms cfg_model] in *.
  eapply (next_rel_core1 segs rho rho' S S1); try eassumption.
  - discriminate.
  - cbn [exec]. reflexivity.
  - cbn. rewrite ss_next_set_reg. cbn. lia.
  - rewrite swf_set_pc. apply swf_set_reg; [exact Hwf2|]. cbn. exact Hmk.
  - cbn [ss_pc set_pc]. unfold rset, with_pc, with_regs, core_of; destruct (is_x0 rd); cbn [c_pc]; unfold ms_pc in Hpc; rewrite Hpc; apply pc_plus'.
  - eapply (regs_match_same rho' (set_reg S1 rd (mk g))); [| reflexivity | reflexivity].
    eapply (regs_match_rset_gen rho' S1 _ ms); [exact Hwf2 | exact Hr1 | | cbn [ms_regs ms_of]; apply c_regs_rset; reflexivity].
    rewrite Hval. rewrite (rget_match segs rho S tr ms md rs1 Hsm). reflexivity.
  - eapply fregs_match_same; [exact Hfr1 | | cbn [ss_fregs set_pc]; rewrite ss_fregs_set_reg; reflexivity].
    unfold rset; destruct (is_x0 rd); reflexivity.
  - cbn [ss_fcsr set_pc]. rewrite ss_fcsr_set_reg. unfold fcsr_match in Hc1 |- *. unfold rset; destruct (is_x0 rd); cbn; exact Hc1.
  - cbn [ss_resv set_pc]. rewrite ss_resv_set_reg. unfold resv_match in Hv1 |- *. unfold rset; destruct (is_x0 rd); cbn; exact Hv1.
  - cbn [ss_objs set_pc]. rewrite ss_objs_set_reg. reflexivity.
  - cbn [ss_facts set_pc]. rewrite ss_facts_set_reg. reflexivity.
Qed.

Lemma div8_bounds : ltac2:(tb__ "0|5|
S5eS58S111Z0M0R1A2S116R1S112Z2M1Z40A2A2A2S58S58S111S114Z8M2S119R2G2A2M3A2M4R2A2S111R2S110G4Z7A2A2A2S58S111G0G3A2S111G3S118S112G1Z3dA2Z1A2A2A2A2F_;Fx;").
Proof.
  intros x Hx. pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)).
  split; [lia|]. split; [apply Z.div_pos; lia|].
  assert (x / 8 < 2 ^ 61) by (apply Z.div_lt_upper_bound; [lia|]; change (8 * 2 ^ 61) with (2 ^ 64); lia). lia.
Qed.

Lemma case_r1 : ltac2:(tb__ "0|3|
S1S92Q5A1M0G0S92Q6M1A1S61S8S47S153A1M2S143S154S57S44S122A1S67Vsegs;S6R9A1A2S46S122S130S129R8R7R6A4A2A3S57S5eS93G1R7A2Z3A3S57S44S61A1Sc1RbRaR9A3S46S61R7A2A3S12Vsegs;R7RcS4bG2S151R6S152R5R4A2A4A4S61OLo;R9S1S142Vsegs;ReR1R9R8R7R6A7LS';S1S1S5dLS2;LS1;S68S5dLr;X61x3F_;F_;F_;F_;Fmd;Fms;Ftr;Frho;Fo;Fsh;Frs1;Frd;FS;").
Proof.
  intros S rd rs1 sh o rho tr ms md Hi Hsh H Hsm.
  pose proof (smatch_swf segs _ _ _ Hsm) as Hwf. pose proof (smatch_facts segs _ _ _ Hsm) as Hf.
  pose proof (swf_facts S Hwf) as Hwff. pose proof (mk_prov_ok rho _ Hf) as Hpv.
  assert (He : sv_below (ss_next S) (get_reg S rs1) = true) by (apply get_reg_below; exact Hwf).
  unfold r1_step in H. destruct (is_lit (get_reg S rs1)); [discriminate|].
  destruct (split_lit (get_reg S rs1)) as [e0 c] eqn:Hsl.
  destruct (split_lit_sound rho _ _ _ Hsl) as [Ue He0b]. pose proof (He0b _ He) as He0.
  pose proof (urange (eval rho e0)) as Re0. pose proof (urange (eval rho (get_reg S rs1))) as Re.
  match type of H with (if ?cnd then _ else _) = _ => destruct cnd eqn:Hc end.
  -
    apply lazy_andb_prop in Hc as [Hc Hnw]. apply andb_prop in Hc as [Hc Hal]. apply andb_prop in Hc as [Hc0 Hc1].
    apply Z.leb_le in Hc0. apply Z.ltb_lt in Hc1. apply Z.leb_le in Hal.
    pose proof (puleq_sound rho _ _ _ _ Hpv Hnw) as A3. rewrite U_SLit in A3 by lia.
    destruct (align_sv_sound rho (ss_facts S) e0 Hf) as [_ Hdiv].
    assert (H8 : U rho e0 mod 8 = 0).
    { unfold U. apply Z.mod_divide; [lia|]. eapply Z.divide_trans; [|exact Hdiv]. exists (2 ^ (align_sv (ss_facts S) e0 - 3)).
      change 8 with (2 ^ 3). rewrite <- Z.pow_add_r by lia. f_equal. lia. }
    assert (Uex : U rho (get_reg S rs1) = U rho e0 + c) by (rewrite Ue; apply Z.mod_small; unfold U in *; lia).
    set (q := U rho e0 / 8).
    pose proof (Z.div_mod (U rho e0) 8 ltac:(lia)) as D0. fold q in D0. rewrite H8 in D0.
    assert (Hq61 : 0 <= q <= 2 ^ 61 - 1) by (unfold q; pose proof (div8_bounds (U rho e0) ltac:(unfold U; lia)); lia).
    assert (VAL : U rho (get_reg S rs1) / 8 = q + c / 8).
    { rewrite Uex. rewrite D0. rewrite Z.add_0_r.
      replace (8 * q + c) with (c + q * 8) by lia. rewrite Z.div_add by lia. lia. }
    assert (MK : forall rho' g, U rho' (SVar g) = q ->
              U rho' (if c / 8 =? 0 then SVar g else SAlu ALU_ADD (SVar g) (SLit (c / 8))) = q + c / 8).
    { intros rho' g Hg. destruct (c / 8 =? 0) eqn:E.
      - apply Z.eqb_eq in E. rewrite E. lia.
      - rewrite U_add, Hg, U_SLit by (pose proof (Z.div_pos c 8); pose proof (Z.div_lt_upper_bound c 8 (2 ^ 40)); lia).
        apply Z.mod_small. pose proof (Z.div_pos c 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_mono c (2 ^ 40) 8 ltac:(lia) ltac:(lia)).
        change (2 ^ 40 / 8) with (2 ^ 37) in *. lia. }
    destruct (find_granule_eq _ (ss_facts S) e0) as [g|] eqn:Hfg; injection H as <-.
    +
      destruct (find_granule_eq_sound _ _ _ _ Hfg) as [Hok Hin].
      destruct (g8_eqfact_bounds _ _ _ _ Hwff Hin) as [Hgb _].
      destruct (granule_eq_ok_sound rho _ _ _ Hpv Hok (proj1 (Forall_forall _ _) Hf _ Hin)) as [Hge _].
      eapply case_r1_val; [exact Hi | exact Hsh | | | exact Hsm].
      * destruct (c / 8 =? 0); cbn; rewrite ?andb_true_r; apply Pos.ltb_lt; exact Hgb.
      * rewrite VAL. apply MK. lia.
    +
      apply (case_r1_freshF S rd rs1 sh (FE (ss_next S) e0) (fun g => if c / 8 =? 0 then SVar g else SAlu ALU_ADD (SVar g) (SLit (c / 8))) (Z_to_bv 64 q) rho tr ms md Hi Hsh Hsm).
      cbn zeta. set (g := ss_next S). set (rho' := ext1 rho g (Z_to_bv 64 q)).
      assert (Hg : U rho' (SVar g) = q).
      { unfold U, rho'. cbn [eval]. rewrite ext1_at. rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite two64. apply Z.mod_small. lia. }
      assert (Ee0 : eval rho' e0 = eval rho e0) by (symmetry; eapply eval_agree; [apply ext1_agree | exact He0]).
      split; [|split; [|split]].
      * assert (E8 : U rho' (g8 g) = U rho e0).
        { rewrite U_g8 by lia. rewrite Hg. lia. }
        unfold FE. constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]; cbn [holds eval]; fold (g8 g).
        -- apply bv_eq. change (bv_unsigned (eval rho' (g8 g))) with (U rho' (g8 g)). rewrite E8, Ee0. reflexivity.
        -- unfold U in Hg. cbn [eval] in Hg. rewrite Hg. rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite two64. rewrite Z.mod_small; lia.
        -- change (bv_unsigned (eval rho' (g8 g))) with (U rho' (g8 g)). rewrite E8, Ee0. unfold U. lia.
        -- change (bv_unsigned (eval rho' (g8 g))) with (U rho' (g8 g)). rewrite E8, Ee0. unfold U. lia.
      * unfold FE, g8. cbn [forallb sprop_below sv_below]. fold g.
        rewrite !(sv_below_mono g (Pos.succ g) e0 ltac:(lia) He0). rewrite !(proj2 (Pos.ltb_lt g (Pos.succ g))) by lia. reflexivity.
      * destruct (c / 8 =? 0); cbn; rewrite ?andb_true_r; apply Pos.ltb_lt; lia.
      * apply bv_eq. pose proof (MK rho' g Hg) as M. unfold U in M. rewrite M. rewrite srl3_val by exact Hsh. symmetry. exact VAL.
  -
    clear Hc. destruct (find_granule _ (ss_facts S) (get_reg S rs1)) as [g|] eqn:Hfg; injection H as <-.
    + destruct (find_granule_In _ _ _ _ Hfg) as [Hok [e' Hin]].
      destruct (granule_ok_sound rho _ _ _ Hpv Hok) as [Hq _].
      destruct (g8_fact_bounds _ _ _ _ Hwff Hin) as [Hgb _].
      eapply case_r1_val; [exact Hi | exact Hsh | cbn; apply Pos.ltb_lt; exact Hgb | exact Hq | exact Hsm].
    + set (q := U rho (get_reg S rs1) / 8).
      pose proof (div8_bounds (U rho (get_reg S rs1)) ltac:(unfold U; apply urange)) as [Hq1 Hq2]. fold q in Hq1, Hq2.
      apply (case_r1_freshF S rd rs1 sh (F8 (ss_next S) (get_reg S rs1)) SVar (Z_to_bv 64 q) rho tr ms md Hi Hsh Hsm).
      cbn zeta. set (g := ss_next S). set (rho' := ext1 rho g (Z_to_bv 64 q)). set (e := get_reg S rs1) in *.
      assert (Hg : U rho' (SVar g) = q).
      { unfold U, rho'. cbn [eval]. rewrite ext1_at. rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite two64. apply Z.mod_small. lia. }
      assert (Ee : eval rho' e = eval rho e) by (symmetry; eapply eval_agree; [apply ext1_agree | exact He]).
      assert (U8 : U rho' (g8 g) = 8 * q) by (rewrite U_g8 by lia; lia).
      split; [|split; [|split]].
      * unfold F8. constructor; [|constructor; [|constructor; [|constructor]]]; cbn [holds eval]; fold (g8 g).
        -- change (bv_unsigned (eval rho' (g8 g))) with (U rho' (g8 g)). rewrite U8, Ee. unfold q, U in *. lia.
        -- rewrite Ee, add_val. change (bv_unsigned (eval rho' (g8 g))) with (U rho' (g8 g)). rewrite U8.
           change (bv_unsigned (Z_to_bv 64 7)) with 7. unfold q, U in *. rewrite Z.mod_small; lia.
        -- unfold U in Hg. cbn [eval] in Hg. rewrite Hg. rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite two64. rewrite Z.mod_small; lia.
      * unfold F8, g8. cbn [forallb sprop_below sv_below]. fold g.
        rewrite !(sv_below_mono g (Pos.succ g) e ltac:(lia) He). rewrite (proj2 (Pos.ltb_lt g (Pos.succ g))) by lia. reflexivity.
      * cbn. apply Pos.ltb_lt. lia.
      * apply bv_eq. unfold U in Hg. cbn [eval] in Hg |- *. rewrite Hg. symmetry. apply srl3_val. exact Hsh.
Qed.

Lemma case_r2 : ltac2:(tb__ "0|3|
S1S92Q5A1M0G0S92QcA1S5fS8S47S153A1M1S143S154S57S44S122A1S67Vsegs;S6R9A1A2S46S122S12fS12aR8R7R6A4A2A3S57S5eS66R7A1Z7A3S57S44S5fA1Sb6SafS4RbA1M2A1G2S63RbR9A2A3S46S5fR7A2A3S12Vsegs;R7RcS4bG1S151R6S152R5R4A2A4A4S142Vsegs;RdS62S65RdRcSaS12eS63RdRbA2SabR9A1A3A3S110S6RdA1Z4A2A2R8R7R6R5A7F_;F_;F_;F_;Fmd;Fms;Ftr;Frho;Fg;Fimm;Frs1;Frd;FS;").
Proof.
  intros S rd rs1 imm g rho tr ms md Hi Himm Hfg Hsm.
  pose proof (smatch_swf segs _ _ _ Hsm) as Hwf. pose proof (smatch_facts segs _ _ _ Hsm) as Hf.
  destruct (find_granule_In _ _ _ _ Hfg) as [Hok [e' Hin]].
  destruct (granule_ok_sound rho _ _ _ (mk_prov_ok rho _ Hf) Hok) as [Hq [Hb Hq61]].
  pose proof (g8_fact_bounds _ _ _ _ (swf_facts S Hwf) Hin) as [Hg _].
  eapply step_rd_sound; [exact Hsm | exact Hi | discriminate | reflexivity | eapply npc_eq; eauto | |].
  - cbn -[sv_below get_reg]. cbn [sv_below]. rewrite (get_reg_below S rs1 Hwf). cbn. rewrite andb_true_r. apply Pos.ltb_lt. exact Hg.
  - apply bv_eq. cbn [eval]. fold (g8 g). rewrite sub_val.
    change (bv_unsigned (eval rho (g8 g))) with (U rho (g8 g)). rewrite U_g8 by lia.
    rewrite (rget_match segs rho S tr ms md rs1 Hsm). unfold U in *. cbn [eval] in Hq, Hb, Hq61 |- *.
    change (sext 64 imm) with (Z_to_bv 64 (immI imm)). rewrite Himm, and_val.
    change (bv_unsigned (Z_to_bv 64 7)) with (Z.ones 3). rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
    pose proof (urange (eval rho (get_reg S rs1))).
    rewrite (Z.mod_small _ (2 ^ 64)) by lia.
    pose proof (Z.div_mod (bv_unsigned (eval rho (get_reg S rs1))) 8 ltac:(lia)). lia.
Qed.

Lemma xb_facts_sound : ltac2:(tb__ "0|1|
S8Sa6S47S45S0S0A2A1S0S0S15dR5R4A2S57S5eS120R6R2A2S118S120R6R3A2M0S113G0Z8A2A2A3S155S2S14R7A1SdcR6R5R4R3A4A3F_;F_;Fv;Fe;FX;Fpv;Frho;").
Proof.
  intros rho pv X e v Hpv Uv. pose proof Hpv as (Hf & _ & _).
  induction X as [|[b l] rest IH]; [constructor|]. cbn [xb_facts].
  destruct ((3 <=? align_sv (pv_facts pv) b) &&& puleq pv b 0 e) eqn:E; [|exact IH].
  constructor; [|exact IH]. apply lazy_andb_prop in E as [HA HL]. apply Z.leb_le in HA.
  pose proof (puleq_sound rho _ _ _ _ Hpv HL) as P. cbn [holds]. change (bv_unsigned (eval rho b) <= bv_unsigned (eval rho v)) with (U rho b <= U rho v).
  destruct (align_sv_sound rho (pv_facts pv) b Hf) as [_ Hdiv].
  pose proof (urange (eval rho b)) as Rb. change (bv_unsigned (eval rho b)) with (U rho b) in Rb.
  pose proof (urange (eval rho e)) as Re. change (bv_unsigned (eval rho e)) with (U rho e) in Re.
  assert (Hb8 : U rho b mod 8 = 0).
  { apply Z.mod_divide; [lia|]. eapply Z.divide_trans; [|exact Hdiv]. exists (2 ^ (align_sv (pv_facts pv) b - 3)).
    change 8 with (2 ^ 3). rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  pose proof (Z.div_mod (U rho b) 8 ltac:(lia)) as Db. rewrite Hb8, Z.add_0_r in Db.
  pose proof (Z.div_mod (U rho e) 8 ltac:(lia)) as De. pose proof (Z.mod_pos_bound (U rho e) 8 ltac:(lia)).
  assert (U rho b / 8 <= U rho e / 8) by (apply Z.div_le_mono; lia). rewrite Uv. lia.
Qed.

Lemma xb_facts_below : ltac2:(tb__ "0|1|
S5fSa6S47S45S0S0A2M0A1S0S0S57S43S14aG0G0SbR6S51S0S0R1A3A2Lr;R3A3S48A3S57S43SbR6R3A2S48A3S57S43SbR7R3A2S48A3S57S43S14aS2S1aR8A1SdcR7R6R5R4A4A3S48A3F_;F_;F_;Fv;Fe;FX;Fpv;Fn;").
Proof.
  intros n pv X e v HX He Hv. induction X as [|[b l] rest IH]; [reflexivity|].
  cbn [forallb fst] in HX. apply andb_prop in HX as [Hb HX]. cbn [xb_facts].
  destruct ((3 <=? align_sv (pv_facts pv) b) &&& puleq pv b 0 e); [|exact (IH HX)]. cbn [forallb sprop_below]. rewrite Hb, Hv. exact (IH HX).
Qed.

Lemma case_andm8 : ltac2:(tb__ "0|3|
Sa4S92Q5A1M0G0S92QcA1S61S8S47S153A1M1S143S154S57S44S122A1S67Vsegs;S6Sa3R9A1A1A2S46S122S12fS12aR8R7R6A4A2A3S57S5eS66R7A1N8A3S57S44S61A1SbdRbRaR9R8A4S46S61R7A2A3S57S43Sb4RcA1S48A3S12Vsegs;R8Sa3RdA1S4bG1S151R7S152R6R5A2A4A4S61OLo;RaS1S142Vsegs;Sa3RfA1R1RaR9R8R7A7LS';S1S1S59S142Vsegs;Sa3R10A1M2R2RbRaR9R8A7S142Vsegs;G2R1RbRaR9R8A7A2LS2;LS1;S68S5aLr;X61x3F_;F_;F_;F_;F_;Fmd;Fms;Ftr;Frho;Fo;Fimm;Frs1;Frd;FA;").
Proof.
  intros A rd rs1 imm o rho tr ms md Hi Himm H HwfA Hsm. unfold andm8_step in H. set (S := ax_S A) in *.
  destruct (is_lit (get_reg S rs1) || (bv_unsigned rd =? 0)) eqn:Hl; [discriminate|].
  apply orb_false_iff in Hl as [_ Hrd]. apply Z.eqb_neq in Hrd.
  destruct (puleq (mk_prov (ss_facts S)) (get_reg S rs1) 7 (SLit (2 ^ 64 - 1))) eqn:Hnw; [|discriminate]. injection H as <-.
  pose proof (smatch_swf segs _ _ _ Hsm) as Hwf. pose proof (smatch_facts segs _ _ _ Hsm) as Hf.
  pose proof (puleq_sound rho _ _ _ _ (mk_prov_ok rho _ Hf) Hnw) as A3. rewrite U_SLit in A3 by lia.
  set (e := get_reg S rs1) in *. set (v := mk_slt_f (ss_facts S) ALU_AND e (SLit (immI imm mod 2 ^ 64))) in *.
  pose proof (case_opimm segs S ALU_AND rd rs1 imm rho tr ms md Hi Hsm) as NR. fold e v in NR.
  destruct NR as (ms1 & rho' & STEP & Hag & Hle & Hsm1).
  assert (He : sv_below (ss_next S) e = true) by (unfold e; apply get_reg_below; exact Hwf).
  assert (Hv : sv_below (ss_next S) v = true).
  { unfold v. apply mk_slt_f_below; [exact He | reflexivity]. }
  assert (Uv : U rho v = U rho e - U rho e mod 8).
  { unfold v, U. rewrite (mk_slt_f_sound rho) by exact Hf. rewrite and_val. cbn [eval]. rewrite Himm.
    change (bv_unsigned (Z_to_bv 64 (-8 mod 2 ^ 64))) with (2 ^ 64 - 2 ^ 3).
    rewrite land_high_mask; [reflexivity | lia | apply urange]. }
  pose proof (urange (eval rho e)) as Re. change (bv_unsigned (eval rho e)) with (U rho e) in Re.
  pose proof (Z.mod_pos_bound (U rho e) 8 ltac:(lia)) as Me.
  exists ms1, rho'. split; [exact STEP|]. split; [exact Hag|]. split; [cbn; rewrite ss_next_set_reg; lia|].
  pose proof HwfA as W. unfold axwf in W. apply andb_prop in W as [HX _].
  assert (HXb : forallb (fun r : sv * sv => sv_below (ss_next S) (fst r)) (ax_X A) = true).
  { apply forallb_forall. intros r Hr. pose proof (proj1 (forallb_forall _ _) HX r Hr) as Y. unfold xr_below in Y. apply andb_prop in Y as [Y1 _]. exact Y1. }

  pose proof (xb_facts_sound rho (mk_prov (ss_facts S)) (ax_X A) e v (mk_prov_ok rho _ Hf) Uv) as XF.
  pose proof (xb_facts_below (ss_next S) (mk_prov (ss_facts S)) (ax_X A) e v HXb He Hv) as XB.
  assert (XF' : Forall (holds rho') (xb_facts (mk_prov (ss_facts S)) (ax_X A) e v)).
  { apply Forall_forall. intros f Hfz. pose proof (proj1 (Forall_forall _ _) XF f Hfz) as Hh.
    pose proof (proj1 (forallb_forall _ _) XB f Hfz) as Hb.
    exact (proj1 (holds_agree _ rho rho' f Hag Hb) Hh). }
  apply smatch_add_facts; [exact Hsm1 | |].
  - assert (EQe : eval rho' e = eval rho e) by (symmetry; eapply eval_agree; [exact Hag | exact He]).
    assert (EQv : eval rho' v = eval rho v) by (symmetry; eapply eval_agree; [exact Hag | exact Hv]).
    unfold U in *.
    constructor; [|constructor; [|exact XF']]; cbn [holds]; cbn [eval]; rewrite ?add_val, ?EQe, ?EQv.
    + lia.
    + change (bv_unsigned (Z_to_bv 64 7)) with 7. rewrite Z.mod_small by lia. lia.
  - rewrite ss_next_set_pc_reg. change (forallb (sprop_below (ss_next S)) ([SPUle v e; SPUle e (SAlu ALU_ADD v (SLit 7))] ++ xb_facts (mk_prov (ss_facts S)) (ax_X A) e v) = true).
    rewrite forallb_app. apply andb_true_intro. split.
    + cbn [forallb sprop_below]. cbn [sv_below]. rewrite Hv, He. reflexivity.
    + exact XB.
Qed.

Lemma and_m8_shadow : ltac2:(tb__ "0|5|
S5eS5eS57S5eS113R2Z8M0A2Z0M1A3S111G1R3A2M2G2S57S5eS118S113S110R5R4A2S112Z2Z40A2M3A2M4S113G4G0A2A2S113S110S118R4S113R4G0A2A2R5A2G3A2A3F_;F_;F_;FT;FB;").
Proof.
  intros B T HB HB0 HT.
  set (W := B + T). pose proof (Z.mod_pos_bound W (2 ^ 64) ltac:(lia)) as M1.
  assert (R : (W mod 2 ^ 64) mod 8 = T mod 8).
  { rewrite Z.mod_mod_divide by (exists (2 ^ 61); reflexivity). unfold W. rewrite Z.add_mod, HB by lia.
    replace (0 + T mod 8) with (T mod 8) by lia. apply Z.mod_mod. lia. }
  rewrite R. pose proof (Z.mod_pos_bound T 8 ltac:(lia)) as M2.
  assert (GE : T mod 8 <= W mod 2 ^ 64).
  { pose proof (Z.div_mod (W mod 2 ^ 64) 8 ltac:(lia)) as D. rewrite R in D.
    pose proof (Z.div_pos (W mod 2 ^ 64) 8 ltac:(lia) ltac:(lia)). nia. }
  apply (Z.mod_unique _ _ (W / 2 ^ 64)); [left; lia|].
  pose proof (Z.div_mod W (2 ^ 64) ltac:(lia)) as D. unfold W in D |- *. lia.
Qed.

Lemma case_andm8_sh : ltac2:(tb__ "0|3|
Sa4S92Q5A1M0G0S92QcA1S61S8S47S153A1M1S143S154S57S44S122A1S67Vsegs;S6Sa3R9A1A1A2S46S122S12fS12aR8R7R6A4A2A3S57S5eS66R7A1N8A3S57S44S61A1ScdRbRaR9A3S46S61R7A2A3S12Vsegs;R7Sa3RcA1S4bG1S151R6S152R5R4A2A4A4S61OLo;R9S1S142Vsegs;Sa3ReA1R1R9R8R7R6A7LS';S1S1S59S142Vsegs;Sa3RfA1M2R2RaR9R8R7A7S142Vsegs;G2R1RaR9R8R7A7A2LS2;LS1;S68S5aLr;X61x3F_;F_;F_;F_;Fmd;Fms;Ftr;Frho;Fo;Fimm;Frs1;Frd;FA;").
Proof.
  intros A rd rs1 imm o rho tr ms md Hi Himm H Hsm. unfold andm8_sh_step in H.
  set (S := ax_S A) in *.
  destruct (bv_unsigned rd =? 0) eqn:Hrd; [discriminate|]. apply Z.eqb_neq in Hrd.
  destruct (ax_base A) as [bs| | | | | | |] eqn:Hbase; try discriminate.
  destruct (negb (bs mod 8 =? 0)) eqn:Hal; [discriminate|]. apply negb_false_iff in Hal. apply Z.eqb_eq in Hal.
  destruct (rel_offset (SLit bs) (get_reg S rs1)) as [t|] eqn:Hro; [|discriminate].
  destruct (is_lit t || _); [discriminate|]. injection H as <-.
  pose proof (smatch_swf segs _ _ _ Hsm) as Hwf.
  set (e := get_reg S rs1) in *.
  pose proof (rel_offset_sound rho _ _ _ Hro) as Ue. change (bv_unsigned (eval rho e)) with (U rho e) in Ue.
  assert (UB : U rho (SLit bs) = bs mod 2 ^ 64).
  { unfold U. cbn [eval]. rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite two64. reflexivity. }
  assert (Ubs : U rho (SLit bs) mod 8 = 0).
  { rewrite UB. rewrite Z.mod_mod_divide by (exists (2 ^ 61); reflexivity). exact Hal. }
  pose proof (Z.mod_pos_bound bs (2 ^ 64) ltac:(lia)) as Rb. rewrite <- UB in Rb.
  assert (Htb : sv_below (ss_next S) t = true).
  { apply (rel_offset_below (ss_next S) (SLit bs) e t); [apply get_reg_below; exact Hwf | reflexivity | exact Hro]. }
  pose proof (urange (eval rho t)) as Rt. change (bv_unsigned (eval rho t)) with (U rho t) in Rt.
  set (gv := U rho t - U rho t mod 8).
  pose proof (Z.mod_pos_bound (U rho t) 8 ltac:(lia)) as Mt.
  apply (case_opimm_freshF S ALU_AND rd rs1 imm (FA (ss_next S) t) (fun g' => mk_alu ALU_ADD (SVar g') (SLit bs)) (Z_to_bv 64 gv) rho tr ms md Hi Hsm).
  cbn zeta. set (g := ss_next S). set (rho' := ext1 rho g (Z_to_bv 64 gv)).
  assert (Hg : U rho' (SVar g) = gv).
  { unfold U, rho'. cbn [eval]. rewrite ext1_at. rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite two64. apply Z.mod_small. lia. }
  assert (Et : eval rho' t = eval rho t) by (symmetry; eapply eval_agree; [apply ext1_agree | exact Htb]).
  split; [|split; [|split]].
  - unfold FA. constructor; [|constructor; [|constructor; [|constructor]]]; cbn [holds].
    + change (bv_unsigned (eval rho' (SVar g))) with (U rho' (SVar g)). rewrite Hg, Et. fold (U rho t). lia.
    + rewrite Et. cbn [eval]. rewrite add_val. change (bv_unsigned (rw rho' g)) with (U rho' (SVar g)). rewrite Hg.
      change (bv_unsigned (Z_to_bv 64 7)) with 7. fold (U rho t). rewrite Z.mod_small by lia. lia.
    + split; [lia|]. unfold rho'. rewrite ext1_at. rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite two64. rewrite (Z.mod_small gv) by lia.
      unfold gv. change (2 ^ 3) with 8. rewrite Zminus_mod, Z.mod_mod by lia. rewrite Z.sub_diag. reflexivity.
  - unfold FA. cbn [forallb sprop_below sv_below]. fold g.
    rewrite !(sv_below_mono g (Pos.succ g) t ltac:(lia) Htb). rewrite !(proj2 (Pos.ltb_lt g (Pos.succ g))) by lia. reflexivity.
  - apply mk_alu_below; [|reflexivity]. cbn. apply Pos.ltb_lt. lia.
  - rewrite mk_alu_sound. apply bv_eq. rewrite add_val, and_val. change (bv_unsigned (eval rho' (SVar g))) with (U rho' (SVar g)). rewrite Hg. fold e.
    change (bv_unsigned (eval rho e)) with (U rho e). rewrite Ue. change (sext 64 imm) with (Z_to_bv 64 (immI imm)). rewrite Himm.
    change (bv_unsigned (Z_to_bv 64 (-8))) with (2 ^ 64 - 2 ^ 3).
    change (bv_unsigned (eval rho' (SLit bs))) with (U rho (SLit bs)).
    rewrite land_high_mask by (try lia; apply Z.mod_pos_bound; lia). change (2 ^ 3) with 8.
    unfold gv. symmetry. apply and_m8_shadow; [exact Ubs | lia | lia].
Qed.

Lemma bytes_le_to_Z_single : ltac2:(tb__ "0|2|
S92Q8M0A1M1S57S5eS1baS4fG1R1S52G1A1A3A1S93G0R1A2A3Fv;").
Proof. intros v. cbn. rewrite Z.shiftl_0_l, Z.lor_0_r. reflexivity. Qed.

Lemma le_bytes_to_word_single : ltac2:(tb__ "0|2|
S92Q8M0A1M1S57S5eS93Q40S1bbS4fG1R1S52G1A1A3A1A2S93G0R1A2A3Fv;").
Proof.
  intros v. unfold le_bytes_to_word. rewrite bytes_le_to_Z_single, Z_to_bv_unsigned. unfold bv_wrap. rewrite two64.
  pose proof (bv_unsigned_in_range 8 v). change (bv_modulus 8) with 256 in H. apply Z.mod_small. lia.
Qed.

Definition gdesc_sem (rho : valuation) (facts : list sprop) (off : sv) (d : gdesc) : Prop := ltac2:(tb__ "0|a|
Sa5OLd;Vd;S0S58S57S5eS120Vrho;Voff;A2M0S119S120Vrho;R1A2M1Z8M2A2M3A3M4S58S57S5eS113G1G2A2Z0M5A3S116S110G1Z7A2S112Z2Z40A2M6A2A2A2Lq8;S5fS0S58G4S57S5eS120Vrho;SabR2A1A2S114G2G3A2A3A2Le;Lg;S5fS0S5eS58S116G5R1A2S58S116S110S120Vrho;R2A2S114G2R1A2M7A2M8G6A2S58S57S5eG0S119G8G2A2M9A3S57S5eS110S120Vrho;SabR3A1A2G7A2S114G2G9A2A3A2A2A2Lk;Le;Lg;Xa5x3").

Lemma split_gk_var_below : ltac2:(tb__ "0|0|
S5fS0S5fS5eS57S43SbR4R3A2S48A3S57S44SaeA1Sc6R4A1S46SaeSbcR3R2A2A2A3S1afR4R6A2F_;F_;Fk;Fg;Foff;Fn;").
Proof.
  intros n off g k Hb H. unfold split_gk in H. destruct off; try discriminate.
  - injection H as -> _. cbn in Hb. apply Pos.ltb_lt. exact Hb.
  - destruct op; try discriminate. destruct off1; try discriminate.
    + destruct off2; try discriminate. injection H as -> _. cbn in Hb. rewrite ?andb_true_r in Hb. apply Pos.ltb_lt. exact Hb.
    + destruct off2; try discriminate. injection H as -> _. cbn in Hb. rewrite ?andb_true_r in Hb. apply Pos.ltb_lt. exact Hb.
Qed.

Lemma granule_of_sound : ltac2:(tb__ "0|0|
S8Sa6S0Sa5S15dR4R3A2S57S44Sa5A1Sb2R4R3A2S46Sa5R2A2A3S15eR6Sb1R5A1R4R3A4F_;F_;Fd;Foff;Fpv;Frho;").
Proof.
  intros rho pv off d Hpv H. pose proof Hpv as (Hf & _ & _). unfold granule_of in H.
  destruct (split_gk off) as [[g k | q]|] eqn:Hgk; [| |discriminate].
  -
    destruct ((0 <=? k) && (k <? 2 ^ 40)) eqn:Hk; [|discriminate]. cbn [negb] in H.
    apply andb_prop in Hk as [Hk0 Hk1]. apply Z.leb_le in Hk0. apply Z.ltb_lt in Hk1.
    assert (Uoff : U rho off = (U rho (SVar g) + k) mod 2 ^ 64).
    { unfold split_gk in Hgk. destruct off; try discriminate.
      - injection Hgk as E1 E2; subst. rewrite Z.add_0_r. symmetry. apply Z.mod_small. apply urange.
      - destruct op; try discriminate. destruct off1; try discriminate.
        + destruct off2; try discriminate. injection Hgk as E1 E2; subst. rewrite U_add, U_SLit by lia. f_equal; lia.
        + destruct off2; try discriminate. injection Hgk as E1 E2; subst. rewrite U_add, U_SLit by lia. f_equal; lia. }
    destruct (granule_expr pv (pv_facts pv) g) as [[e|e0]|] eqn:Hge.
    3:{
        destruct (puleq pv (SVar g) k (SLit (2 ^ 61 - 1))) eqn:Hb; [|discriminate]. injection H as <-. cbn [gdesc_sem].
        pose proof (puleq_sound rho _ _ _ _ Hpv Hb) as A3. rewrite U_SLit in A3 by lia.
        pose proof (urange (rw rho g)) as Rg. assert (Ug : U rho (SVar g) = bv_unsigned (rw rho g)) by reflexivity.
        assert (U8 : U rho (g8 g) = 8 * U rho (SVar g)) by (apply U_g8; lia).
        assert (Uq8 : U rho (mk_alu ALU_ADD (g8 g) (SLit (8 * k))) = 8 * U rho (SVar g) + 8 * k).
        { unfold U. rewrite mk_alu_sound, add_val. fold (U rho (g8 g)). rewrite U8. cbn [eval]. rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite two64.
          rewrite (Z.mod_small (8 * k)) by lia. apply Z.mod_small. lia. }
        change (addk_base (g8 g) (8 * k)) with (mk_alu ALU_ADD (g8 g) (SLit (8 * k))). rewrite Uq8, Uoff. rewrite (Z.mod_small (U rho (SVar g) + k)) by lia.
        split; [|split; [|lia]].
        - replace (8 * U rho (SVar g) + 8 * k) with ((U rho (SVar g) + k) * 8) by lia. rewrite Z.div_mul by lia. reflexivity.
        - replace (8 * U rho (SVar g) + 8 * k) with ((U rho (SVar g) + k) * 8) by lia. apply Z.mod_mul. lia. }
    + destruct (granule_expr_sound _ _ _ _ Hge) as [Hok Hin].
      destruct (granule_ok_sound rho _ _ _ Hpv Hok) as [Hq [Hb Hq61]].
      pose proof (urange (eval rho e)) as Re.
      destruct (k =? 0) eqn:Ek.
      * apply Z.eqb_eq in Ek. subst k. injection H as <-. cbn [gdesc_sem].
        rewrite Uoff, Z.add_0_r, Z.mod_small by (pose proof (urange (rw rho g)); unfold U; cbn [eval]; lia).
        split; [exact Hq|]. rewrite U_g8 by lia. lia.
      * destruct (puleq pv e (8 * k) (SLit (2 ^ 64 - 1))) eqn:Hnw; [|discriminate]. injection H as <-. cbn [gdesc_sem].
        pose proof (puleq_sound rho _ _ _ _ Hpv Hnw) as A3. rewrite U_SLit in A3 by lia. apply Z.eqb_neq in Ek.
        split; [lia|]. split; [lia|].
        assert (D : (U rho e + 8 * k) / 8 = U rho (SVar g) + k).
        { replace (U rho e + 8 * k) with (U rho e + k * 8) by lia. rewrite Z.div_add by lia. lia. }
        rewrite D. split; [rewrite Uoff; apply Z.mod_small; lia|]. rewrite U_g8 by lia. lia.
    + destruct (granule_expr_sound _ _ _ _ Hge) as [Hok Hin].
      destruct (granule_eq_ok_sound rho _ _ _ Hpv Hok (proj1 (Forall_forall _ _) Hf _ Hin)) as [He0 Hq61].
      destruct (puleq pv e0 (8 * k + 7) (SLit (2 ^ 64 - 1))) eqn:Hnw; [|discriminate]. injection H as <-. cbn [gdesc_sem].
      pose proof (puleq_sound rho _ _ _ _ Hpv Hnw) as A3. rewrite U_SLit in A3 by lia.
      assert (Uq8 : U rho (mk_alu ALU_ADD e0 (SLit (8 * k))) = U rho e0 + 8 * k).
      { unfold U. rewrite mk_alu_sound, add_val. cbn [eval]. rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite two64.
        unfold U in He0, A3, Hq61. cbn [eval] in Hq61. pose proof (urange (eval rho e0)).
        rewrite (Z.mod_small (8 * k)) by lia. apply Z.mod_small. lia. }
      rewrite Uq8, He0. split; [|split; [|lia]].
      * rewrite Uoff. replace (8 * U rho (SVar g) + 8 * k) with ((U rho (SVar g) + k) * 8) by lia. rewrite Z.div_mul by lia.
        apply Z.mod_small. unfold U in *. cbn [eval] in *. pose proof (urange (rw rho g)). lia.
      * replace (8 * U rho (SVar g) + 8 * k) with ((U rho (SVar g) + k) * 8) by lia. apply Z.mod_mul. lia.
  -
    destruct ((0 <=? q) && (q <? 2 ^ 61)) eqn:Hq; [|discriminate]. injection H as <-. cbn [gdesc_sem].
    apply andb_prop in Hq as [Hq0 Hq1]. apply Z.leb_le in Hq0. apply Z.ltb_lt in Hq1.
    unfold split_gk in Hgk. destruct off; try discriminate; [injection Hgk as <- | destruct op; try discriminate; destruct off1; try discriminate; destruct off2; discriminate].
    rewrite !U_SLit by lia. split; [|split; [rewrite Z.mul_comm; apply Z.mod_mul; lia | lia]].
    rewrite Z.mul_comm. rewrite Z.div_mul by lia. reflexivity.
Qed.

Section R3.
Variable A : axst.
Variable rho : valuation.
Variables (tr : list event) (ms : machine_state) (md : Model).
Let S := ax_S A.
Hypothesis Hsm : ltac2:(tb__ "0|0|
S12Vsegs;Vrho;VS;S4bS47S153A1S151Vtr;S152Vms;Vmd;A2A4A4").
Hypothesis Hsh : shadow_ok rho A.
Hypothesis Hwfx : axwf A = true.

Lemma r3_core : ltac2:(tb__ "0|8|
S0S5eS0S0S149S45S0S0A2S4bS0S0R2R1A4SaaVA;A1A3S111S120Vrho;R3A2R4A2S111S110R5Z1M0A2S120Vrho;SaS123R4R3A3A2A2S57S5eS120Vrho;R7A2S113S110S120Vrho;Sa9VA;A1A2S119R6Z8M1A2A2S112Z2Z40A2A2A3S5bS92Q8M2A1M3G3S58S57S44G3A1S144Vms;ScVrho;R9A2A2S46G3R1A2A3S58S111S93G2R1A2M4Z7A2S58S59S57S5eG4Z0M5A3S58S111G0G4A2S57S5eS110S114G1S119R8G1A2A2M6G4A2S120Vrho;SaS123R7R6A3A2M7A3A2A2S111S110G6G1A2G7A2S57S5eS93G2R2A2G5A3F_;A2A2A2Lv;A2F_;F_;F_;F_;Fl;Fb;Fa;Fae;").
Proof.
  intros ae a b l Hin A1 A2 Hae.
  pose proof (proj1 (Forall_forall _ _) Hsh (b, l) Hin) as Hxr. unfold xr_ok in Hxr. cbn [fst snd] in Hxr.
  destruct Hxr as (HB8 & HBL & Hall).
  set (B := bv_unsigned (eval rho b)) in *. set (L := bv_unsigned (eval rho l)) in *.
  pose proof (urange (eval rho b)) as Rb. pose proof (urange (eval rho l)) as Rl. fold B in Rb. fold L in Rl.
  assert (UBL : U rho (SAlu ALU_ADD b l) = B + L).
  { rewrite U_add in A2 |- *. unfold U in A2 |- *. fold B L in A2 |- *.
    destruct (Z.eq_dec (B + L) (2 ^ 64)) as [E|E]; [rewrite E, Z.mod_same in A2 by lia; unfold U in A1; lia|].
    rewrite Z.mod_small; lia. }
  rewrite UBL in A2 |- *. unfold U in A1. fold B in A1.
  destruct (Hall a ltac:(lia)) as (Hoff & Hout & Hw & v & Hrm & Henc).
  assert (Heq : eval rho ae = shadow_addr (bv_unsigned (eval rho (ax_base A))) a).
  { unfold shadow_addr. apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite two64. unfold U in Hae. rewrite Hae. reflexivity. }
  exists v. split.
  { rewrite Heq. pose proof Hsm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & Hfr) & _). cbn [fst snd cfg_ms cfg_model] in Hfr.
    rewrite (Hfr _ Hout). exact Hrm. }
  pose proof (bv_unsigned_in_range 8 v) as Hv8. change (bv_modulus 8) with 256 in Hv8.
  pose proof (Z.mod_pos_bound (B + L) 8 ltac:(lia)) as M1. pose proof (Z.div_mod (B + L) 8 ltac:(lia)) as D1.
  pose proof (Z.div_mod a 8 ltac:(lia)) as Da. pose proof (Z.mod_pos_bound a 8 ltac:(lia)) as Ma.
  split; [destruct Henc as [-> | [-> _]]; lia|].
  split.
  - destruct Henc as [H0 | [Hv Hq']]; [left; exact H0|].
    destruct (Z.eq_dec (bv_unsigned v) 0) as [Z0|Z0]; [left; exact Z0|]. right. split; [lia|].
    rewrite Hq', Hv. lia.
  - intros Hfast. destruct Henc as [H0 | [Hv Hq']]; [exact H0|]. exfalso. rewrite <- Hq' in D1. nia.
Qed.

Lemma case_r3_out : ltac2:(tb__ "0|6|
S43S92Q5A1M0G0S92QcA1S43S0S0S0S92Q8M1A1M2S57S44S122A1S67Vsegs;S6VS;A1A2S46S122S12dS138R9R8R7R6A5A2A3S149S45S0S0A2S4bS0S0R4R3A4SaaVA;A1A3S57S43SbS9VS;A1R6A2S48A3S57S44G2A1S144Vms;ScVrho;S6aS63VS;RaA2S66R9A1A2A2A2S46G2R4A2A3S111S93G1R5A2Z7A2S59S57S5eS93G1R6A2M3Z0M4A3S58S111Z1G3A2S57S5eS110S120Vrho;R9A2G3A2S120Vrho;SaS123R8R7A3A2A3A2A2S57S43RbS48A3S57S5eS93G1R8A2G4A3F_;S61OLx;Sc2VS;RfRcRbRaR9A6S1S142Vsegs;VS;R1Vrho;Vtr;Vms;Vmd;A7M5LS';S1S1S59S142Vsegs;VS;R2Vrho;Vtr;Vms;Vmd;A7G5A2LS2;LS1;S68S5aLr;X61x3F_;F_;F_;F_;F_;F_;F_;Fv;Fl;Fb;Fq8;Ffast;Fimm;Frs1;Frd;Fsgn;").
Proof.
  intros sgn rd rs1 imm fast q8 b l v Hi Hin Hq8b Hmem Hv7 Henc Hfast.
  pose proof (smatch_swf segs _ _ _ Hsm) as Hwf. pose proof (smatch_pcv segs _ _ _ _ _ Hsm) as Hpc.
  set (ae := mk_addk (get_reg S rs1) (immI imm)) in *.
  assert (Haddr : (rget (core_of ms) rs1 + sext 64 imm)%bv = eval rho ae).
  { unfold ae. rewrite mk_addk_sound. rewrite <- (rget_match segs rho S tr ms md rs1 Hsm). reflexivity. }
  assert (Hrd : ov_read_bytes segs (ms_mem ms) (eval rho ae) (Z.to_nat (msz SZ1)) = Some [v]).
  { change (Z.to_nat (msz SZ1)) with 1%nat. cbn [ov_read_bytes]. rewrite Hmem. reflexivity. }
  set (K := fun v0 : word => EDone (rset rd v0 (with_pc (c_pc (core_of ms) + Z_to_bv 64 4)%bv (core_of ms)))).
  destruct (interp_load_val segs SZ1 sgn (eval rho ae) K (ms_mem ms) [v] Hrd) as (VAL & Hint & HVAL).
  assert (UVAL : bv_unsigned VAL = bv_unsigned v).
  { rewrite HVAL. change (8 * Z.to_N (msz SZ1))%N with 8%N.
    rewrite ext_low_small; [apply le_bytes_to_word_single | cbn; lia |].
    rewrite le_bytes_to_word_single. destruct sgn; cbn; lia. }
  set (ms1 := ms_of ms (rset rd VAL (with_pc (Z_to_bv 64 (ss_pc S + 4)) (core_of ms))) (ms_mem ms)).
  assert (STEP : RiscvSemantics.step segs ms = MachineOk ms1).
  { rewrite (step_instr_at segs ms (ss_pc S) _ Hpc Hi ltac:(discriminate)).
    change (exec (Z_to_bv 64 4) (Load SZ1 sgn rd rs1 imm) (core_of ms))
      with (load_val SZ1 sgn (rget (core_of ms) rs1 + sext 64 imm)%bv K).
    rewrite Haddr, Hint. unfold K. cbn [interp_eff0 lift_result].
    change (c_pc (core_of ms)) with (ms_pc_val ms). unfold ms_pc in Hpc. rewrite Hpc, pc_plus'. reflexivity. }
  assert (ZERO : bv_unsigned v = 0 -> next_rel segs S (set_pc (set_reg S rd (SLit 0)) (ss_pc S + 4)) rho tr ms md).
  { intros Hz. exists ms1, rho. split; [exact STEP|]. split; [apply agree_below_refl|]. split; [rewrite ss_next_set_pc_reg; lia|].
    eapply smatch_rd_pc; [exact Hsm | reflexivity |]. apply bv_eq. rewrite UVAL, Hz. reflexivity. }
  unfold r3_out. destruct fast.
  - apply ZERO. apply Hfast. reflexivity.
  - destruct (Z.eq_dec (bv_unsigned v) 0) as [Hz|Hz]; [left; apply ZERO; exact Hz|]. right.
    destruct Henc as [Hz' | [Hv1 Hsum]]; [lia|].
    set (vv := ss_next S). set (rho' := ext1 rho vv VAL).
    pose proof (ext1_agree rho vv VAL) as Hag.
    pose proof (smatch_agree segs rho rho' S _ Hag Hsm) as Hsm1.
    assert (HsmF : smatch segs rho' (snd (fresh S)) (tr, mkCfg ms md)).
    { destruct Hsm1 as (_ & Hpc' & Hpend & Hhalt & Hrom' & Hroc & Hr1 & Hfr1 & Hc1 & Hv1' & Hm1 & Hfa1).
      unfold smatch. cbn [fst snd cfg_ms cfg_model fresh ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next ss_lenient].
      split; [apply swf_fresh; exact Hwf|]. repeat (split; [assumption|]). exact Hfa1. }
    assert (Hbl : sv_below vv b = true /\ sv_below vv l = true).
    { unfold axwf in Hwfx. apply andb_prop in Hwfx as [HX _]. fold S vv in HX.
      pose proof (proj1 (forallb_forall _ _) HX _ Hin) as Hr. unfold xr_below in Hr. cbn [fst snd] in Hr.
      apply andb_prop in Hr as [Hr1 Hr2]. split; assumption. }
    destruct Hbl as [Hbb Hlb].
    assert (Eb : forall x, sv_below vv x = true -> eval rho' x = eval rho x).
    { intros x Hx. symmetry. eapply eval_agree; [exact Hag | exact Hx]. }
    set (S1 := add_facts (F3 q8 b l vv) (snd (fresh S))).
    assert (Hvv : rw rho' vv = VAL) by (unfold rho'; apply ext1_at).
    assert (Hsm2 : smatch segs rho' S1 (tr, mkCfg ms md)).
    { unfold S1. apply smatch_add_facts; [exact HsmF| |].
      - unfold F3. constructor; [|constructor; [|constructor; [|constructor]]]; cbn [holds eval].
        + rewrite Hvv, (Eb q8 Hq8b), (Eb b Hbb), (Eb l Hlb). apply bv_eq. rewrite !add_val.
          change (bv_unsigned (eval rho q8)) with (U rho q8). rewrite UVAL, Hsum.
          unfold U. cbn [eval]. rewrite add_val. apply Z.mod_mod. lia.
        + rewrite Hvv, UVAL. change (bv_unsigned (Z_to_bv 64 1)) with 1. lia.
        + rewrite Hvv, UVAL. change (bv_unsigned (Z_to_bv 64 7)) with 7. lia.
      - unfold F3. cbn [forallb sprop_below sv_below fresh snd ss_next]. fold vv.
        rewrite (sv_below_mono vv (Pos.succ vv) q8 ltac:(lia) Hq8b), (sv_below_mono vv (Pos.succ vv) b ltac:(lia) Hbb),
                (sv_below_mono vv (Pos.succ vv) l ltac:(lia) Hlb).
        rewrite (proj2 (Pos.ltb_lt vv (Pos.succ vv))) by lia. reflexivity. }
    exists ms1, rho'. split; [exact STEP|]. split; [exact Hag|]. split; [cbn; rewrite ss_next_set_reg; cbn; lia|].
    assert (HbelowS : sv_below (ss_next S1) (SVar vv) = true) by (cbn; apply Pos.ltb_lt; lia).
    exact (smatch_rd_pc segs rho' S1 tr ms md rd (SVar vv) VAL (ss_pc S + 4) Hsm2 HbelowS ltac:(cbn [eval]; exact Hvv)).
Qed.

Lemma granule_expr_below : ltac2:(tb__ "0|2|
Sa6S5fS53S0S0A2M0S57S44G0A1Sd2R3S4VS;A1R2A3S46G0R1A2A3S58S1afR3S9VS;A1M1A2S57S43SbG1G0S0Lr;R2S0R1Le;S0R1Le0;X53x2A2S48A3A2F_;Fr;Fg;Fpv;").
Proof using Hsm.
  intros pv g r H. pose proof (swf_facts S (smatch_swf segs _ _ _ Hsm)) as Hwff.
  pose proof (granule_expr_sound _ _ _ _ H) as X. destruct r as [e|e0]; destruct X as [_ Hin].
  - exact (g8_fact_bounds _ _ _ _ Hwff Hin).
  - exact (g8_eqfact_bounds _ _ _ _ Hwff Hin).
Qed.

Lemma case_r3 : ltac2:(tb__ "0|2|
S43S92Q5A1M0G0S92QcA1S61S57S44S122A1S67Vsegs;S6VS;A1A2S46S122S12dS138R5R4R3R2A5A2A3S57S44S61A1Sc3VA;R6R5R4R3A5S46S61R2A2A3S61OLo;R3S1S142Vsegs;VS;R1Vrho;Vtr;Vms;Vmd;A7M1LS';S1S1S59S142Vsegs;VS;R2Vrho;Vtr;Vms;Vmd;A7G1A2LS2;LS1;S68S5aLr;X61x3F_;F_;Fo;Fimm;Frs1;Frd;Fsgn;").
Proof.
  intros sgn rd rs1 imm o Hi H. unfold r3_step in H. fold S in H.
  pose proof (smatch_facts segs _ _ _ Hsm) as Hf. pose proof (smatch_swf segs _ _ _ Hsm) as Hwf.
  set (pv := mk_prov (ss_facts S)) in *. pose proof (mk_prov_ok rho _ Hf) as Hpv. fold pv in Hpv.
  set (ae := mk_addk (get_reg S rs1) (immI imm)) in *.
  destruct (rel_offset (ax_base A) ae) as [off|] eqn:Hro; [|discriminate].
  pose proof (rel_offset_sound rho _ _ _ Hro) as Uae. change (bv_unsigned (eval rho ae)) with (U rho ae) in Uae.
  assert (Hoffb : sv_below (ss_next S) off = true).
  { eapply rel_offset_below; [| | exact Hro].
    - unfold ae. apply mk_addk_below. apply get_reg_below. exact Hwf.
    - unfold axwf in Hwfx. apply andb_prop in Hwfx as [_ Hb]. exact Hb. }
  destruct (granule_of pv off) as [d|] eqn:Hgo; [|discriminate].
  pose proof (granule_of_sound rho _ _ _ Hpv Hgo) as GS.
  destruct d as [q8 | g e | g e k]; cbn [gdesc_sem] in GS.
  -
    destruct (find_xr pv (ax_X A) q8 0) as [[b l]|] eqn:Hfx; [|discriminate]. injection H as <-.
    destruct (find_xr_sound rho _ _ _ _ _ _ Hpv Hfx) as (Hin & A1 & A2).
    destruct GS as (Uoff & Hal & Hnw).
    assert (Hq8b : sv_below (ss_next S) q8 = true).
    { unfold granule_of in Hgo. destruct (split_gk off) as [[g k|q]|] eqn:Hgk; [| |discriminate].
      - destruct (negb _); [discriminate|]. change (pv_facts pv) with (ss_facts S) in Hgo.
        destruct (granule_expr pv (ss_facts S) g) as [[e|e0]|] eqn:Hge; [| | destruct (puleq _ _ _ _); [|discriminate]; injection Hgo as <-; change (addk_base (g8 ?gg) (8 * ?kk)) with (mk_alu ALU_ADD (g8 gg) (SLit (8 * kk))); apply mk_alu_below; [cbn; rewrite andb_true_r; apply Pos.ltb_lt; eapply split_gk_var_below; [exact Hoffb | exact Hgk] | reflexivity]].
        + destruct (k =? 0); [discriminate|]. destruct (puleq _ _ _ _); discriminate.
        + destruct (puleq _ _ _ _); [|discriminate]. injection Hgo as <-.
          destruct (granule_expr_below _ _ _ Hge) as [_ He0]. apply mk_alu_below; [exact He0 | reflexivity].
      - destruct (_ && _); [|discriminate]. injection Hgo as <-. reflexivity. }
    destruct (r3_core ae (U rho q8) b l Hin ltac:(lia) ltac:(lia)) as (v & Hmem & Hv7 & Henc & Hfast).
    { rewrite Uae, Uoff. reflexivity. }
    assert (E8 : 8 * (U rho q8 / 8) = U rho q8) by (pose proof (Z.div_mod (U rho q8) 8 ltac:(lia)); lia).
    rewrite E8 in Henc, Hfast.
    eapply case_r3_out; [exact Hi | exact Hin | exact Hq8b | exact Hmem | exact Hv7 | exact Henc |].
    intros Hfb. apply Hfast. pose proof (puleq_sound rho _ _ _ _ Hpv Hfb). lia.
  -
    destruct (find_xr pv (ax_X A) e 0) as [[b l]|] eqn:Hfx; [|discriminate]. injection H as <-.
    destruct (find_xr_sound rho _ _ _ _ _ _ Hpv Hfx) as (Hin & A1 & A2).
    destruct GS as (Uoff & U8).
    assert (Hgb : (g < ss_next S)%positive).
    { unfold granule_of in Hgo. destruct (split_gk off) as [[g' k|q]|] eqn:Hgk; [| |discriminate].
      - destruct (negb _); [discriminate|]. change (pv_facts pv) with (ss_facts S) in Hgo.
        destruct (granule_expr pv (ss_facts S) g') as [[e'|e0]|] eqn:Hge; [| | destruct (puleq _ _ _ _); discriminate].
        + destruct (k =? 0); [injection Hgo as <- <- | destruct (puleq _ _ _ _); discriminate]. exact (proj1 (granule_expr_below _ _ _ Hge)).
        + destruct (puleq _ _ _ _); discriminate.
      - destruct (_ && _); discriminate. }
    destruct (r3_core ae (U rho e) b l Hin ltac:(lia) ltac:(lia)) as (v & Hmem & Hv7 & Henc & Hfast).
    { rewrite Uae, Uoff. reflexivity. }
    rewrite <- U8 in Henc, Hfast.
    eapply case_r3_out; [exact Hi | exact Hin | cbn; rewrite andb_true_r; apply Pos.ltb_lt; exact Hgb | exact Hmem | exact Hv7 | exact Henc |].
    intros Hfb. apply Hfast. pose proof (puleq_sound rho _ _ _ _ Hpv Hfb). lia.
  -
    destruct (find_xr pv (ax_X A) e (8 * k)) as [[b l]|] eqn:Hfx; [|discriminate].
    destruct (puleq pv (g8 g) (8 * k + 8) (SAlu ALU_ADD b l)) eqn:Hfb; [|discriminate]. injection H as <-.
    destruct (find_xr_sound rho _ _ _ _ _ _ Hpv Hfx) as (Hin & A1 & A2).
    pose proof (puleq_sound rho _ _ _ _ Hpv Hfb) as A3.
    destruct GS as (Hk & Hnw & Uoff & U8).
    destruct (r3_core ae (U rho e + 8 * k) b l Hin ltac:(lia) ltac:(lia)) as (v & Hmem & Hv7 & Henc & Hfast).
    { rewrite Uae, Uoff. reflexivity. }
    pose proof (case_r3_out sgn rd rs1 imm true (g8 g) b l v Hi Hin) as OUT. unfold r3_out in OUT. apply OUT.
    + cbn. unfold granule_of in Hgo. destruct (split_gk off) as [[g' k'|q]|] eqn:Hgk; [| |discriminate].
      * destruct (negb _); [discriminate|]. change (pv_facts pv) with (ss_facts S) in Hgo.
        destruct (granule_expr pv (ss_facts S) g') as [[e'|e0]|] eqn:Hge; [| | destruct (puleq _ _ _ _); discriminate].
        -- destruct (k' =? 0); [discriminate|]. destruct (puleq _ _ _ _); [|discriminate]. injection Hgo as <- <- <-.
           rewrite andb_true_r. apply Pos.ltb_lt. exact (proj1 (granule_expr_below _ _ _ Hge)).
        -- destruct (puleq _ _ _ _); discriminate.
      * destruct (_ && _); discriminate.
    + exact Hmem.
    + exact Hv7.
    + left. apply Hfast. lia.
    + intros _. apply Hfast. lia.
Qed.

Lemma bytes_le_to_Z_zeros : ltac2:(tb__ "0|2|
S4dS57S5eS1baS157S92Q8M0A1S94G0Z0M1A2R1A3A1G1A3Fk;").
Proof using . induction k as [|k IH]; [reflexivity|]. cbn [repeat bytes_le_to_Z]. rewrite IH. reflexivity. Qed.

Lemma ov_read_bytes_zeros : ltac2:(tb__ "0|7|
S92Q40M0A1M1S44S92Q8M2A1M3A1M4Fx;G1S4dS4dS1b4R1R2A2S57G4R5S94G0S110S93G0R4A2S11dR2A1A2A2A1S46G3S94G2Z0A2M5A2A3F_;Fj;S57S44S47G3A1M6A1S147Vsegs;R4R3R2A4S46G6S157G3G5R2A3A2A3F_;Fk;Fa;Fm;").
Proof using .
  intros m a k. revert a. induction k as [|k IH]; intros a H; [reflexivity|].
  cbn [ov_read_bytes repeat].
  pose proof (H 0%nat ltac:(lia)) as H0. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in H0. rewrite H0.
  rewrite (IH (a + 1)%bv); [reflexivity|].
  intros j Hj. rewrite <- (H (Datatypes.S j) ltac:(lia)). f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned, bv_add_unsigned.
  unfold bv_wrap. change (bv_unsigned (1 : word)) with 1. rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.

Lemma q8_of_sound : ltac2:(tb__ "0|3|
Sa6S0Sa5S15dVrho;R3A2S57S47S2A1Sb1R4A1S4VS;A1A3S57S43SbS9VS;A1M0R4A2S48A3S57S44Sa5A1Sb2R6R5A2S46Sa5R4A2A3S58S57S5eS120Vrho;Sc0R5A1M1A2S114Z8S120Vrho;R6A2A2M2A3S58S116S110G2Z7A2S112Z2Z40A2A2S57S43SbG0G1A2S48A3A2A2F_;F_;F_;F_;Fd;Foff;Fpv;").
Proof using Hsm.
  intros pv off d Hpv Hpf Hoffb Hgo. pose proof (granule_of_sound rho _ _ _ Hpv Hgo) as GS.
  pose proof (urange (eval rho off)) as Ro. change (bv_unsigned (eval rho off)) with (U rho off) in Ro.
  destruct d as [q8 | g e | g e k]; cbn [gdesc_sem q8_of] in GS |- *.
  - destruct GS as (Uoff & Hal & Hnw). pose proof (Z.div_mod (U rho q8) 8 ltac:(lia)).
    split; [lia|]. split; [lia|].
    unfold granule_of in Hgo. destruct (split_gk off) as [[g k|q]|] eqn:Hgk; [| |discriminate].
    + destruct (negb _); [discriminate|]. rewrite Hpf in Hgo.
      destruct (granule_expr pv (ss_facts S) g) as [[e|e0]|] eqn:Hge; [| | destruct (puleq _ _ _ _); [|discriminate]; injection Hgo as <-; change (addk_base (g8 ?gg) (8 * ?kk)) with (mk_alu ALU_ADD (g8 gg) (SLit (8 * kk))); apply mk_alu_below; [cbn; rewrite andb_true_r; apply Pos.ltb_lt; eapply split_gk_var_below; [exact Hoffb | exact Hgk] | reflexivity]].
      * destruct (k =? 0); [discriminate|]. destruct (puleq _ _ _ _); discriminate.
      * destruct (puleq _ _ _ _); [|discriminate]. injection Hgo as <-.
        destruct (granule_expr_below _ _ _ Hge) as [_ He0]. apply mk_alu_below; [exact He0 | reflexivity].
    + destruct (_ && _); [|discriminate]. injection Hgo as <-. reflexivity.
  - destruct GS as (Uoff & U8). pose proof (Z.div_mod (U rho e) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (U rho e) 8 ltac:(lia)).
    pose proof (urange (eval rho e)). change (bv_unsigned (eval rho e)) with (U rho e) in H1.
    split; [lia|]. split; [lia|].
    unfold granule_of in Hgo. destruct (split_gk off) as [[g' k|q]|] eqn:Hgk; [| |discriminate].
    + destruct (negb _); [discriminate|]. rewrite Hpf in Hgo.
      destruct (granule_expr pv (ss_facts S) g') as [[e'|e0]|] eqn:Hge; [| | destruct (puleq _ _ _ _); discriminate].
      * destruct (k =? 0); [injection Hgo as <- <- | destruct (puleq _ _ _ _); discriminate].
        cbn. rewrite andb_true_r. apply Pos.ltb_lt. exact (proj1 (granule_expr_below _ _ _ Hge)).
      * destruct (puleq _ _ _ _); discriminate.
    + destruct (_ && _); discriminate.
  - destruct GS as (Hk & Hnw & Uoff & U8).
    pose proof (Z.div_mod (U rho e + 8 * k) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (U rho e + 8 * k) 8 ltac:(lia)).
    assert (Ug : U rho (mk_alu ALU_ADD (g8 g) (SLit (8 * k))) = U rho (g8 g) + 8 * k).
    { unfold U. rewrite mk_alu_sound, add_val. cbn [eval]. rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite two64.
      unfold U in U8, Hnw. pose proof (urange (eval rho (g8 g))). rewrite (Z.mod_small (8 * k)) by lia. apply Z.mod_small. lia. }
    rewrite Ug. split; [lia|]. split; [lia|].
    unfold granule_of in Hgo. destruct (split_gk off) as [[g' k'|q]|] eqn:Hgk; [| |discriminate].
    + destruct (negb _); [discriminate|]. rewrite Hpf in Hgo.
      destruct (granule_expr pv (ss_facts S) g') as [[e'|e0]|] eqn:Hge; [| | destruct (puleq _ _ _ _); discriminate].
      * destruct (k' =? 0); [discriminate|]. destruct (puleq _ _ _ _); [|discriminate]. injection Hgo as <- <- <-.
        apply mk_alu_below; [|reflexivity]. cbn. rewrite andb_true_r. apply Pos.ltb_lt. exact (proj1 (granule_expr_below _ _ _ Hge)).
      * destruct (puleq _ _ _ _); discriminate.
    + destruct (_ && _); discriminate.
Qed.

Lemma find_xr_d_sound : ltac2:(tb__ "0|3|
Sa6S47S45S0S0A2M0A1Sa5S0S0S0S15dVrho;R6A2S57S47S2A1Sb1R7A1S4VS;A1A3S57S43SbS9VS;A1R3A2S48A3S57S44Sa5A1Sb2R9R4A2S46Sa5R7A2A3S57S44G0A1Sd0RaR9R8A3S46G0S4bS0S0R7R6A4A2A3S58S149G0S4bS0S0R8R7A4RaA3S58S111S110S120Vrho;R8A2S11bZ0M1A1A2S120Vrho;Sc0R9A1A2M2A2S111S110G2S110G1Z1A2A2S120Vrho;SaS123R8R7A3A2A2A2A2F_;F_;F_;F_;F_;Foff;Fl;Fb;Fd;FX;Fpv;").
Proof using Hsm.
  intros pv X d b l off Hpv Hpf Hoffb Hgo H.
  pose proof (granule_of_sound rho _ _ _ Hpv Hgo) as GS.
  destruct (q8_of_sound pv off d Hpv Hpf Hoffb Hgo) as (Uq8 & Hnw8 & _).
  pose proof Hpv as (Hf & _ & _).
  assert (LO : forall b0, xr_lo_ok pv b0 d = true -> U rho b0 + - 0 <= U rho (q8_of d)).
  { intros b0 HL. unfold xr_lo_ok in HL. apply lazy_orb_prop in HL as [HL|HL]; [exact (puleq_sound rho _ _ _ _ Hpv HL)|].
    rewrite Uq8.
    pose proof (urange (eval rho b0)) as Rb. change (bv_unsigned (eval rho b0)) with (U rho b0) in Rb.
    destruct d as [q8 | g e | g e k]; [discriminate| |]; cbn [gdesc_sem] in GS;
      apply lazy_andb_prop in HL as [HA HL]; apply Z.leb_le in HA; pose proof (puleq_sound rho _ _ _ _ Hpv HL) as P;
      destruct (align_sv_sound rho (pv_facts pv) b0 Hf) as [_ Hdiv];
      assert (Hb8 : U rho b0 mod 8 = 0) by
        (apply Z.mod_divide; [lia|]; eapply Z.divide_trans; [|exact Hdiv]; exists (2 ^ (align_sv (pv_facts pv) b0 - 3));
         change 8 with (2 ^ 3); rewrite <- Z.pow_add_r by lia; f_equal; lia);
      pose proof (Z.div_mod (U rho b0) 8 ltac:(lia)) as Db; rewrite Hb8, Z.add_0_r in Db.
    - destruct GS as (Uoff & U8). rewrite Uoff.
      pose proof (Z.div_mod (U rho e) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (U rho e) 8 ltac:(lia)).
      assert (U rho b0 / 8 <= U rho e / 8) by (apply Z.div_le_mono; lia). lia.
    - destruct GS as (Hk & Hnw & Uoff & U8). rewrite Uoff.
      pose proof (Z.div_mod (U rho e + 8 * k) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (U rho e + 8 * k) 8 ltac:(lia)).
      assert (U rho b0 / 8 <= (U rho e + 8 * k) / 8) by (apply Z.div_le_mono; lia). lia. }
  assert (HI : forall b0 l0, xr_hi1_ok pv b0 l0 d = true -> U rho (q8_of d) + (0 + 1) <= U rho (SAlu ALU_ADD b0 l0)).
  { intros b0 l0 HH. unfold xr_hi1_ok in HH. apply lazy_orb_prop in HH as [HH|HH]; [exact (puleq_sound rho _ _ _ _ Hpv HH)|].
    apply lazy_orb_prop in HH as [HH|HH].
    - rewrite Uq8.
      destruct d as [q8 | g e | g e k]; [discriminate| |]; cbn [gdesc_sem] in GS; pose proof (puleq_sound rho _ _ _ _ Hpv HH) as P.
      + destruct GS as (Uoff & U8). rewrite Uoff.
        pose proof (Z.div_mod (U rho e) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (U rho e) 8 ltac:(lia)). lia.
      + destruct GS as (Hk & Hnw & Uoff & U8). rewrite Uoff.
        pose proof (Z.div_mod (U rho e + 8 * k) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (U rho e + 8 * k) 8 ltac:(lia)). lia.
    - apply lazy_orb_prop in HH as [HH|HH]; [exact (proj2 (xr_rel_hit_sound rho pv b0 l0 _ 0 Hpv HH))|].
      rewrite Uq8.
      destruct d as [q8 | g e | g e k]; [discriminate| |]; cbn [gdesc_sem] in GS; pose proof (proj2 (xr_rel_hit_sound rho pv b0 l0 _ _ Hpv HH)) as P.
      + destruct GS as (Uoff & U8). rewrite Uoff.
        pose proof (Z.div_mod (U rho e) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (U rho e) 8 ltac:(lia)). lia.
      + destruct GS as (Hk & Hnw & Uoff & U8). rewrite Uoff.
        pose proof (Z.div_mod (U rho e + 8 * k) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (U rho e + 8 * k) 8 ltac:(lia)). lia. }
  revert H. induction X as [|[b0 l0] rest IH]; intros H; [discriminate|]. cbn [find_xr_d] in H.
  destruct (xr_lo_ok pv b0 d &&& xr_hi1_ok pv b0 l0 d) eqn:E.
  - injection H as <- <-. apply lazy_andb_prop in E as [E1 E2]. split; [left; reflexivity|]. split; [exact (LO _ E1) | exact (HI _ _ E2)].
  - destruct (IH H) as (A0 & B0 & C0). split; [right; exact A0|]. split; assumption.
Qed.

Lemma case_r3x : ltac2:(tb__ "0|2|
S124S43S92Q5A1M0G0S92QcA1S61S57S44S122A1S67Vsegs;S6VS;A1A2S46S122S12dR6R5R4R3R2A5A2A3S57S44S61A1Sc5VA;R7R5R4R3A5S46S61R2A2A3S61OLo;R3S1S142Vsegs;VS;R1Vrho;Vtr;Vms;Vmd;A7M1LS';S1S1S59S142Vsegs;VS;R2Vrho;Vtr;Vms;Vmd;A7G1A2LS2;LS1;S68S5aLr;X61x3F_;F_;Fo;Fimm;Frs1;Frd;Fsgn;Fsz;").
Proof.
  intros sz sgn rd rs1 imm o Hi H. unfold r3x_step in H. fold S in H.
  pose proof (smatch_facts segs _ _ _ Hsm) as Hf. pose proof (smatch_swf segs _ _ _ Hsm) as Hwf.
  pose proof (smatch_pcv segs _ _ _ _ _ Hsm) as Hpc.
  set (pv := mk_prov (ss_facts S)) in *. pose proof (mk_prov_ok rho _ Hf) as Hpv. fold pv in Hpv.
  set (ae := mk_addk (get_reg S rs1) (immI imm)) in *.
  destruct (rel_offset (ax_base A) ae) as [off|] eqn:Hro; [|discriminate].
  pose proof (rel_offset_sound rho _ _ _ Hro) as Uae. change (bv_unsigned (eval rho ae)) with (U rho ae) in Uae.
  destruct (granule_of pv off) as [d|] eqn:Hgo; [|discriminate].
  assert (Hoffb : sv_below (ss_next S) off = true).
  { pose proof Hwfx as W. unfold axwf in W. apply andb_prop in W as [_ Hb].
    eapply rel_offset_below; [| exact Hb | exact Hro]. unfold ae. apply mk_addk_below. apply get_reg_below. exact Hwf. }
  destruct (q8_of_sound pv off d Hpv eq_refl Hoffb Hgo) as (Uq8 & Hnw8 & Hq8b).
  set (q8 := q8_of d) in *.
  destruct (find_xr_d pv (ax_X A) d) as [[b l]|] eqn:Hfx; [|discriminate].
  destruct (puleq pv q8 (8 * msz sz) (SAlu ALU_ADD b l)) eqn:Hfb; [|discriminate]. injection H as <-.
  destruct (find_xr_d_sound pv (ax_X A) d b l off Hpv eq_refl Hoffb Hgo Hfx) as (Hin & A1 & A2). fold q8 in A1, A2.
  pose proof (puleq_sound rho _ _ _ _ Hpv Hfb) as A3.
  set (k := Z.to_nat (msz sz)).
  assert (Hk : Z.of_nat k = msz sz /\ 0 < msz sz <= 8) by (subst k; destruct sz; cbn; lia).

  assert (BYTES : forall j, (j < k)%nat -> ms_mem ms (Z_to_bv 64 (bv_unsigned (eval rho ae) + Z.of_nat j)) = Some (Z_to_bv 8 0)).
  { intros j Hj.
    destruct (r3_core (SAlu ALU_ADD ae (SLit (Z.of_nat j))) (U rho q8 + 8 * Z.of_nat j) b l Hin ltac:(lia) ltac:(lia)) as (v & Hmem & _ & _ & Hfast).
    { rewrite U_add, U_SLit by lia. rewrite Uae, Uq8.
      replace (8 * U rho off + 8 * Z.of_nat j) with ((U rho off + Z.of_nat j) * 8) by lia. rewrite Z.div_mul by lia.
      rewrite Zplus_mod_idemp_l. f_equal. lia. }
    assert (Hv0 : bv_unsigned v = 0).
    { apply Hfast. replace (U rho q8 + 8 * Z.of_nat j) with ((U rho off + Z.of_nat j) * 8) by lia. rewrite Z.div_mul by lia. lia. }
    assert (Ea : Z_to_bv 64 (bv_unsigned (eval rho ae) + Z.of_nat j) = eval rho (SAlu ALU_ADD ae (SLit (Z.of_nat j)))).
    { apply bv_eq. rewrite Z_to_bv_unsigned. change (bv_unsigned (eval rho (SAlu ALU_ADD ae (SLit (Z.of_nat j))))) with (U rho (SAlu ALU_ADD ae (SLit (Z.of_nat j)))).
      rewrite U_add, U_SLit by lia. unfold bv_wrap. rewrite two64. reflexivity. }
    rewrite Ea, Hmem. f_equal. apply bv_eq. rewrite Hv0. reflexivity. }
  pose proof (ov_read_bytes_zeros (ms_mem ms) (eval rho ae) k BYTES) as Hrd.
  assert (Haddr : (rget (core_of ms) rs1 + sext 64 imm)%bv = eval rho ae).
  { unfold ae. rewrite mk_addk_sound. rewrite <- (rget_match segs rho S tr ms md rs1 Hsm). reflexivity. }
  set (K := fun v0 : word => EDone (rset rd v0 (with_pc (c_pc (core_of ms) + Z_to_bv 64 4)%bv (core_of ms)))).
  destruct (interp_load_val segs sz sgn (eval rho ae) K (ms_mem ms) (repeat (Z_to_bv 8 0) k) Hrd) as (VAL & Hint & HVAL).
  assert (UVAL : VAL = Z_to_bv 64 0).
  { rewrite HVAL. unfold le_bytes_to_word. rewrite bytes_le_to_Z_zeros. apply ext_low_zero. destruct sz; cbn; lia. }
  set (ms1 := ms_of ms (rset rd VAL (with_pc (Z_to_bv 64 (ss_pc S + 4)) (core_of ms))) (ms_mem ms)).
  assert (STEP : RiscvSemantics.step segs ms = MachineOk ms1).
  { rewrite (step_instr_at segs ms (ss_pc S) _ Hpc Hi ltac:(discriminate)).
    change (exec (Z_to_bv 64 4) (Load sz sgn rd rs1 imm) (core_of ms))
      with (load_val sz sgn (rget (core_of ms) rs1 + sext 64 imm)%bv K).
    rewrite Haddr, Hint. unfold K. cbn [interp_eff0 lift_result].
    change (c_pc (core_of ms)) with (ms_pc_val ms). unfold ms_pc in Hpc. rewrite Hpc, pc_plus'. reflexivity. }
  exists ms1, rho. split; [exact STEP|]. split; [apply agree_below_refl|]. split; [rewrite ss_next_set_pc_reg; lia|].
  eapply smatch_rd_pc; [exact Hsm | reflexivity |]. cbn [eval]. symmetry. exact UVAL.
Qed.

Lemma fa_target_in_sound : ltac2:(tb__ "0|1|
S47S2A1M0S5fG0S0S57S44S0A1S107R4R3R2A3S46S0R1A2A3S57S43SbeSfbR4R2A2R5A2S48A3F_;Ft;Ffs;Fg';Ffacts;").
Proof.
  intros facts g'. induction fs as [|f fs IH]; intros t H; [discriminate|]. cbn [fa_target_in] in H.
  destruct f as [|p0|a0 b0|a b|a1 b1| |i k]; try exact (IH t H). destruct a as [|v| | | | | |]; try exact (IH t H).
  destruct (Pos.eqb v g' && has_facts (FA g' b) facts) eqn:E; [|exact (IH t H)].
  injection H as <-. apply andb_prop in E as [_ E]. exact E.
Qed.

Lemma r3w_target_sound : ltac2:(tb__ "0|3|
Sa4S0S0S155S2S14Vrho;A1S4Sa3R3A1A1A3S57S44S0A1Sd7R4R3A2S46S0R2A2A3S58S111Z0S110S93Q40M0ScVrho;Sa9R5A1A2A2S120Vrho;R3A2A2M1A2S116G1S112Z2Z40A2A2A2S57S5eS93G0ScVrho;R5A2A2S114S119S110S93G0ScVrho;Sa9R6A1A2A2S120Vrho;R4A2A2Z8M2A2G2A2A3F_;F_;F_;Ft;Fae;FA;").
Proof.
  intros A0 ae t Hf H Hrange.
  assert (FORM2 : forall ae', r3w_target2 A0 ae' = Some t ->
            bv_unsigned (eval rho ae') = (bv_unsigned (eval rho (ax_base A0)) + U rho t) / 8 * 8).
  { intros ae' H2. unfold r3w_target2 in H2.
    destruct (ax_base A0) as [bs| | | | | | |] eqn:Hbase; try discriminate.
    destruct (negb (bs mod 8 =? 0)) eqn:Hal; [discriminate|]. apply negb_false_iff in Hal. apply Z.eqb_eq in Hal.
    destruct (rel_offset (SLit bs) ae') as [[tz|g'| | | | | |]|] eqn:Hro; try discriminate.
    {
      destruct ((0 <=? tz) && (tz mod 8 =? 0) && (tz <? 2 ^ 61)) eqn:Hc; [|discriminate]. injection H2 as <-.
      apply andb_prop in Hc as [Hc Hc3]. apply andb_prop in Hc as [Hc1 Hc2].
      apply Z.leb_le in Hc1. apply Z.eqb_eq in Hc2. apply Z.ltb_lt in Hc3.
      assert (Ut : U rho (SLit tz) = tz) by (apply U_SLit; lia). rewrite Ut in Hrange |- *.
      pose proof (rel_offset_sound rho _ _ _ Hro) as Ue. unfold U in Ue at 1. rewrite Ue. rewrite Ut.
      assert (UB : U rho (SLit bs) = bv_unsigned (eval rho (SLit bs))) by reflexivity. rewrite <- UB in Hrange |- *.
      assert (Ubs : U rho (SLit bs) mod 8 = 0).
      { unfold U. cbn [eval]. rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite two64.
        rewrite Z.mod_mod_divide by (exists (2 ^ 61); reflexivity). exact Hal. }
      rewrite Z.mod_small by lia.
      set (X := U rho (SLit bs) + tz).
      assert (HX8 : X mod 8 = 0) by (unfold X; rewrite Z.add_mod, Ubs, Hc2 by lia; reflexivity).
      pose proof (Z.div_mod X 8 ltac:(lia)). lia. }
    unfold fa_target in H2. apply fa_target_in_sound in H2.
    pose proof (has_facts_sound rho _ _ Hf H2) as HF. unfold FA in HF.
    inversion HF as [|? ? F1 HF2]; subst. inversion HF2 as [|? ? F2 HF3]; subst. inversion HF3 as [|? ? F3 _]; subst.
    cbn [holds eval] in F1, F2, F3. rewrite add_val in F2.
    change (bv_unsigned (rw rho g')) with (U rho (SVar g')) in F1, F2, F3.
    change (bv_unsigned (eval rho t)) with (U rho t) in F1, F2.
    change (bv_unsigned (Z_to_bv 64 7)) with 7 in F2. change (2 ^ 3) with 8 in F3. destruct F3 as [_ F3].
    pose proof (urange (rw rho g')) as Rg. change (bv_unsigned (rw rho g')) with (U rho (SVar g')) in Rg.
    pose proof (urange (eval rho t)) as Rt. change (bv_unsigned (eval rho t)) with (U rho t) in Rt.
    pose proof (Z.div_mod (U rho (SVar g')) 8 ltac:(lia)) as Dg. rewrite F3, Z.add_0_r in Dg.
    assert (Hg8 : U rho (SVar g') <= 2 ^ 64 - 8) by lia.
    rewrite Z.mod_small in F2 by lia.
    assert (Eg : U rho (SVar g') = U rho t / 8 * 8).
    { pose proof (Z.div_mod (U rho t) 8 ltac:(lia)) as Dt. pose proof (Z.mod_pos_bound (U rho t) 8 ltac:(lia)) as Mt. nia. }
    pose proof (rel_offset_sound rho _ _ _ Hro) as Ue. unfold U in Ue at 1. rewrite Ue.
    assert (UB : U rho (SLit bs) = bv_unsigned (eval rho (SLit bs))) by reflexivity. rewrite <- UB in Hrange |- *.
    assert (Ubs : U rho (SLit bs) mod 8 = 0).
    { unfold U. cbn [eval]. rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite two64.
      rewrite Z.mod_mod_divide by (exists (2 ^ 61); reflexivity). exact Hal. }
    pose proof (Z.div_mod (U rho (SLit bs)) 8 ltac:(lia)) as Db. rewrite Ubs, Z.add_0_r in Db.
    pose proof (urange (eval rho (SLit bs))) as Rb. change (bv_unsigned (eval rho (SLit bs))) with (U rho (SLit bs)) in Rb.
    rewrite Eg. rewrite Z.mod_small; [|pose proof (Z.div_mod (U rho t) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (U rho t) 8 ltac:(lia)); lia].
    set (B8 := U rho (SLit bs) / 8) in *. rewrite Db.
    replace (8 * B8 + U rho t) with (B8 * 8 + U rho t) by lia. rewrite Z.div_add_l by lia.
    pose proof (Z.div_mod (U rho t) 8 ltac:(lia)). lia. }
  unfold r3w_target in H.
  destruct ae as [| |op x y| | | | |]; try exact (FORM2 _ H). destruct op; try exact (FORM2 _ H).
  destruct y as [m| | | | | | |]; try exact (FORM2 _ H).
  destruct (m =? 2 ^ 64 - 8) eqn:Hm; [|discriminate]. apply Z.eqb_eq in Hm. subst m.
  pose proof (rel_offset_sound rho _ _ _ H) as Ux. change (bv_unsigned (eval rho x)) with (U rho x) in Ux.
  assert (Uxe : U rho x = bv_unsigned (eval rho (ax_base A0)) + U rho t).
  { rewrite Ux. apply Z.mod_small. unfold U in *. exact Hrange. }
  change (bv_unsigned (eval rho (SAlu ALU_AND x (SLit (2 ^ 64 - 8))))) with (U rho (SAlu ALU_AND x (SLit (2 ^ 64 - 8)))).
  unfold U. cbn [eval]. rewrite and_val. fold (U rho x).
  change (bv_unsigned (Z_to_bv 64 (2 ^ 64 - 8))) with (2 ^ 64 - 2 ^ 3). rewrite land_high_mask by (unfold U; try apply urange; lia). rewrite Uxe.
  pose proof (Z.div_mod (bv_unsigned (eval rho (ax_base A0)) + U rho t) 8 ltac:(lia)). change (2 ^ 3) with 8. unfold U in *. lia.
Qed.

Lemma align_sv_mod : ltac2:(tb__ "0|1|
S47S2A1S0S5eS155S2S14Vrho;A1R3A3S111Z0M0R2A2S111R3S69R5R4A2A2S57S5eS113S120Vrho;R5A2S112Z2R4A2A2G0A3F_;F_;F_;Fn;Fe;Ffacts;").
Proof using .
  intros facts e n Hf Hn Hle. destruct (align_sv_sound rho facts e Hf) as [Hr Hdiv].
  apply Z.mod_divide; [apply Z.pow_nonzero; lia|]. eapply Z.divide_trans; [|exact Hdiv].
  exists (2 ^ (align_sv facts e - n)). rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.

Lemma base_aligned8_sound : ltac2:(tb__ "0|0|
S155S2S14Vrho;A1S4VS;A1A3S57S43Se5VA;A1S48A3S57S5eS113S93Q40ScVrho;Sa9VA;A1A2A2Z8A2Z0A3F_;F_;").
Proof using .
  intros Hf H. unfold base_aligned8 in H. fold S in H.
  assert (GEN : forall e, (3 <=? align_sv (ss_facts S) e) = true -> bv_unsigned (eval rho e) mod 8 = 0).
  { intros e He. apply Z.leb_le in He. change 8 with (2 ^ 3). exact (align_sv_mod _ e 3 Hf ltac:(lia) He). }
  destruct (ax_base A) as [bb| | | | | | |]; try exact (GEN _ H).
  apply Z.eqb_eq in H. cbn [eval]. rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite two64.
  rewrite Z.mod_mod_divide by (exists (2 ^ 61); reflexivity). exact H.
Qed.

Lemma e64_of_sound : ltac2:(tb__ "0|2|
Sa6S0Sa5S15dVrho;R3A2S57S47S2A1Sb1R4A1S4VS;A1A3S57S43SbS9VS;A1R4A2S48A3S57S44Sa5A1Sb2R6R5A2S46Sa5R4A2A3S58S57S5eS119S120Vrho;S104R5A1A2Z40M0A2S119S120Vrho;R6A2Z8A2M1A3S57S5eS119S120Vrho;Sc0R5A1A2G0A2G1A3A2F_;F_;F_;F_;Fd;Foff;Fpv;").
Proof using Hsm.
  intros pv off d Hpv Hpf Hoffb Hgo. pose proof (granule_of_sound rho _ _ _ Hpv Hgo) as GS.
  destruct (q8_of_sound pv off d Hpv Hpf Hoffb Hgo) as (Uq8 & Hnw8 & _).
  assert (Q : U rho (q8_of d) / 64 = U rho off / 8).
  { rewrite Uq8. change 64 with (8 * 8). rewrite Z.div_mul_cancel_l by lia. reflexivity. }
  split; [|exact Q].
  destruct d as [q8 | g e | g e k]; cbn [gdesc_sem e64_of] in GS |- *.
  - exact Q.
  - destruct GS as (Uoff & _). rewrite Uoff. change 64 with (8 * 8). rewrite <- Z.div_div by lia. reflexivity.
  - destruct GS as (Hk & Hnw & Uoff & _). rewrite Uoff.
    pose proof (urange (eval rho e)) as Re. change (bv_unsigned (eval rho e)) with (U rho e) in Re.
    replace (U rho (mk_alu ALU_ADD e (SLit (8 * k)))) with (U rho e + 8 * k).
    + change 64 with (8 * 8). rewrite <- Z.div_div by lia. reflexivity.
    + symmetry. unfold U at 1. rewrite mk_alu_sound. change (alu64 ALU_ADD (eval rho e) (eval rho (SLit (8 * k)))) with (eval rho (SAlu ALU_ADD e (SLit (8 * k)))).
      fold (U rho (SAlu ALU_ADD e (SLit (8 * k)))). rewrite U_add, U_SLit by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma blk64_lo_sound : ltac2:(tb__ "0|1|
Sa6S0S0S5eS15dVrho;R4A2S57S43S102R5R4R3A3S48A3S57S5eS119S120Vrho;R4A2Z40M0A2R3A3S111S120Vrho;R6A2S114G0R4A2A2F_;F_;F_;FWq;Fx;Fb;Fpv;").
Proof using .
  intros pv b x Wq Hpv H HW. pose proof Hpv as (Hf & _ & _).
  pose proof (urange (eval rho x)) as Rx. change (bv_unsigned (eval rho x)) with (U rho x) in Rx.
  pose proof (urange (eval rho b)) as Rb. change (bv_unsigned (eval rho b)) with (U rho b) in Rb.
  pose proof (Z.div_mod (U rho x) 64 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound (U rho x) 64 ltac:(lia)) as Mx.
  unfold blk64_lo_ok in H. apply lazy_orb_prop in H as [H|H].
  - pose proof (puleq_sound rho _ _ _ _ Hpv H). subst Wq. lia.
  - apply lazy_andb_prop in H as [HA H]. apply Z.leb_le in HA. pose proof (puleq_sound rho _ _ _ _ Hpv H) as P.
    pose proof (align_sv_mod _ b 6 Hf ltac:(lia) HA) as Hb64. change (2 ^ 6) with 64 in Hb64.
    pose proof (Z.div_mod (U rho b) 64 ltac:(lia)) as Db. rewrite Hb64, Z.add_0_r in Db.
    assert (U rho b / 64 <= U rho x / 64) by (apply Z.div_le_mono; lia). subst Wq. lia.
Qed.

Lemma blk64_hi_sound : ltac2:(tb__ "0|1|
Sa6S0S0S0S5eS15dVrho;R5A2S57S43S101R6R5R4R3A4S48A3S57S5eS119S120Vrho;R4A2Z40M0A2R3A3S111S110S114G0R4A2G0A2S120Vrho;SaS123R7R6A3A2A2F_;F_;F_;FWq;Fx;Fl;Fb;Fpv;").
Proof using .
  intros pv b l x Wq Hpv H HW. pose proof Hpv as (Hf & _ & _).
  pose proof (urange (eval rho x)) as Rx. change (bv_unsigned (eval rho x)) with (U rho x) in Rx.
  set (E := U rho (SAlu ALU_ADD b l)) in *.
  pose proof (urange (eval rho (SAlu ALU_ADD b l))) as RE. change (bv_unsigned (eval rho (SAlu ALU_ADD b l))) with E in RE.
  pose proof (Z.div_mod (U rho x) 64 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound (U rho x) 64 ltac:(lia)) as Mx.
  unfold blk64_hi_ok in H. apply lazy_orb_prop in H as [H|H].
  - pose proof (puleq_sound rho _ _ _ _ Hpv H). subst Wq. fold E in H0. lia.
  - apply lazy_andb_prop in H as [HA H]. apply Z.leb_le in HA. pose proof (puleq_sound rho _ _ _ _ Hpv H) as P. fold E in P.
    pose proof (align_sv_mod _ (SAlu ALU_ADD b l) 6 Hf ltac:(lia) HA) as HE64. change (2 ^ 6) with 64 in HE64. fold E in HE64.
    pose proof (Z.div_mod E 64 ltac:(lia)) as DE. rewrite HE64, Z.add_0_r in DE.
    assert (U rho x / 64 < E / 64).
    { destruct (Z_lt_le_dec (U rho x / 64) (E / 64)) as [Hlt|Hge]; [exact Hlt|]. exfalso.
      assert (E / 64 * 64 <= U rho x / 64 * 64) by nia. lia. }
    subst Wq. nia.
Qed.

Lemma find_xr_lit_sound : ltac2:(tb__ "0|8|
S47S45S0S0A2M0A1S5eS0S0S57S44G0A1S108R4R3A2S46G0S4bS0S0R2R1A4A2A3S5bS5eS5eS5bS5eS5eS58S57S0R5S5R2A1M1A3S58S57S0R4S5R1A1M2A3S58S149G0S4bS0S0G1G2A4R7A3S11fR6S113R2S112Z2Z40M3A2M4A2M5A2S5eS58S111S113R3G4A2M6R1A2S58S111S110R1Z1A2S110G6G5A2M7A2S58S111G7G4A2S58S111R7R1A2S116R1S110R7G3A2A2A2A2A2A2Ta;A2A2A2Llz;A2Lbz;A2F_;Fl;Fb;Fw;FX;").
Proof.
  induction X as [|[b0 l0] rest IH]; intros w b l H; [discriminate|]. cbn [find_xr_lit] in H.
  assert (REST : find_xr_lit rest w = Some (b, l) -> exists bz lz, b = SLit bz /\ l = SLit lz /\ In (SLit bz, SLit lz) ((b0, l0) :: rest)
            /\ let a := Z.max w (bz mod 2 ^ 64) in
               bz mod 2 ^ 64 <= a /\ a + 1 <= bz mod 2 ^ 64 + lz mod 2 ^ 64 /\ bz mod 2 ^ 64 + lz mod 2 ^ 64 <= 2 ^ 64 /\ w <= a < w + 64).
  { intros H'. destruct (IH w b l H') as (bz & lz & E1 & E2 & Hin & R). exists bz, lz. split; [exact E1|]. split; [exact E2|]. split; [right; exact Hin | exact R]. }
  destruct b0 as [bz| | | | | | |]; try exact (REST H). destruct l0 as [lz| | | | | | |]; try exact (REST H).
  destruct ((Z.max w (bz mod 2 ^ 64) <? Z.min (w + 64) (bz mod 2 ^ 64 + lz mod 2 ^ 64)) && (bz mod 2 ^ 64 + lz mod 2 ^ 64 <=? 2 ^ 64)) eqn:E; [|exact (REST H)].
  injection H as <- <-. apply andb_prop in E as [E1 E2]. apply Z.ltb_lt in E1. apply Z.leb_le in E2.
  exists bz, lz. split; [reflexivity|]. split; [reflexivity|]. split; [left; reflexivity|]. cbn zeta.
  pose proof (Z.le_max_l w (bz mod 2 ^ 64)). pose proof (Z.le_max_r w (bz mod 2 ^ 64)).
  pose proof (Z.le_min_l (w + 64) (bz mod 2 ^ 64 + lz mod 2 ^ 64)). pose proof (Z.le_min_r (w + 64) (bz mod 2 ^ 64 + lz mod 2 ^ 64)). lia.
Qed.

Lemma r3w_fresh : ltac2:(tb__ "0|4|
S43S92Q5A1M0G0S92QcA1S0S57S44S122A1S67Vsegs;S6VS;A1M1A2S46S122S12dS141R5R4R3R2A5A2A3S57S0R2S6aS63VS;R4A2S66R3A1A2A3S4dS1b4R1U8A2S5bS92Q8A1M2G2S57S44G2A1S144Vms;S94Q40M3S110S93G3ScVrho;R6A2A2S11dR3A1A2A2A2S46G2R1A2A3Lbb;A2F_;Fj;S142Vsegs;VS;S62S65S4eS0S1S6bVS;A1A3R7SdS9VS;A1A1A3S110G1Z4A2A2Vrho;Vtr;Vms;Vmd;A7F_;F_;F_;Fae;Fimm;Frs1;Frd;Fsgn;").
Proof.
  intros sgn rd rs1 imm ae Hi Eae BY.
  pose proof (smatch_facts segs _ _ _ Hsm) as Hf. pose proof (smatch_swf segs _ _ _ Hsm) as Hwf.
  pose proof (smatch_pcv segs _ _ _ _ _ Hsm) as Hpc.
  assert (Haddr : (rget (core_of ms) rs1 + sext 64 imm)%bv = eval rho ae).
  { subst ae. rewrite mk_addk_sound. rewrite <- (rget_match segs rho S tr ms md rs1 Hsm). reflexivity. }
  assert (GEN : forall k (a0 : Z), (forall j, (j < k)%nat -> exists bb, ms_mem ms (Z_to_bv 64 (a0 + Z.of_nat j)) = Some bb) ->
            exists bs, length bs = k /\ ov_read_bytes segs (ms_mem ms) (Z_to_bv 64 a0) k = Some bs).
  { induction k as [|k IH]; intros a0 Hb; [exists []; split; reflexivity|].
    destruct (Hb 0%nat ltac:(lia)) as [b0 Hb0]. rewrite Z.add_0_r in Hb0.
    destruct (IH (a0 + 1) ltac:(intros j Hj; destruct (Hb (Datatypes.S j) ltac:(lia)) as [bb Hbj]; exists bb; rewrite <- Hbj; f_equal; f_equal; lia)) as (bs & Hlen & Hrd).
    exists (b0 :: bs). split; [cbn; lia|]. cbn [ov_read_bytes]. rewrite Hb0.
    replace (Z_to_bv 64 a0 + 1)%bv with (Z_to_bv 64 (a0 + 1)); [rewrite Hrd; reflexivity|].
    apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_unsigned (1 : word)) with 1.
    rewrite Zplus_mod_idemp_l. reflexivity. }
  destruct (GEN 8%nat (bv_unsigned (eval rho ae)) BY) as (bs & Hlen & Hrd). rewrite Z_to_bv_bv_unsigned in Hrd.
  set (K := fun v0 : word => EDone (rset rd v0 (with_pc (c_pc (core_of ms) + Z_to_bv 64 4)%bv (core_of ms)))).
  destruct (interp_load_val segs SZ8 sgn (eval rho ae) K (ms_mem ms) bs ltac:(exact Hrd)) as (VAL & Hint & HVAL).
  set (ms1 := ms_of ms (rset rd VAL (with_pc (Z_to_bv 64 (ss_pc S + 4)) (core_of ms))) (ms_mem ms)).
  assert (STEP : RiscvSemantics.step segs ms = MachineOk ms1).
  { rewrite (step_instr_at segs ms (ss_pc S) _ Hpc Hi ltac:(discriminate)).
    change (exec (Z_to_bv 64 4) (Load SZ8 sgn rd rs1 imm) (core_of ms))
      with (load_val SZ8 sgn (rget (core_of ms) rs1 + sext 64 imm)%bv K).
    rewrite Haddr, Hint. unfold K. cbn [interp_eff0 lift_result].
    change (c_pc (core_of ms)) with (ms_pc_val ms). unfold ms_pc in Hpc. rewrite Hpc, pc_plus'. reflexivity. }
  set (vv := ss_next S). set (rho' := ext1 rho vv VAL).
  pose proof (ext1_agree rho vv VAL) as Hag.
  pose proof (smatch_agree segs rho rho' S _ Hag Hsm) as Hsm1.
  assert (HsmF : smatch segs rho' (snd (fresh S)) (tr, mkCfg ms md)).
  { destruct Hsm1 as (_ & Hpc' & Hpend & Hhalt & Hrom' & Hroc & Hr1 & Hfr1 & Hc1 & Hv1' & Hm1 & Hfa1).
    unfold smatch. cbn [fst snd cfg_ms cfg_model fresh ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next ss_lenient].
    split; [apply swf_fresh; exact Hwf|]. repeat (split; [assumption|]). exact Hfa1. }
  assert (Hvv : rw rho' vv = VAL) by (unfold rho'; apply ext1_at).
  exists ms1, rho'. split; [exact STEP|]. split; [exact Hag|]. split; [cbn; rewrite ss_next_set_reg; cbn; lia|].
  assert (HbelowS : sv_below (ss_next (snd (fresh S))) (SVar vv) = true) by (cbn; apply Pos.ltb_lt; lia).
  exact (smatch_rd_pc segs rho' (snd (fresh S)) tr ms md rd (SVar vv) VAL (ss_pc S + 4) HsmF HbelowS ltac:(cbn [eval]; exact Hvv)).
Qed.

Lemma case_r3w : ltac2:(tb__ "0|2|
S124S43S92Q5A1M0G0S92QcA1S61S57S44S122A1S67Vsegs;S6VS;A1A2S46S122S12dR6R5R4R3R2A5A2A3S57S44S61A1Sc4VA;R7R5R4R3A5S46S61R2A2A3S61OLo;R3S1S142Vsegs;VS;R1Vrho;Vtr;Vms;Vmd;A7M1LS';S1S1S59S142Vsegs;VS;R2Vrho;Vtr;Vms;Vmd;A7G1A2LS2;LS1;S68S5aLr;X61x3F_;F_;Fo;Fimm;Frs1;Frd;Fsgn;Fsz;").
Proof.
  intros sz sgn rd rs1 imm o Hi H. unfold r3w_step in H. fold S in H.
  destruct sz; try discriminate.
  pose proof (smatch_facts segs _ _ _ Hsm) as Hf. pose proof (smatch_swf segs _ _ _ Hsm) as Hwf.
  pose proof (smatch_pcv segs _ _ _ _ _ Hsm) as Hpc.
  set (ae := mk_addk (get_reg S rs1) (immI imm)) in *.
  set (pv := mk_prov (ss_facts S)) in *. pose proof (mk_prov_ok rho _ Hf) as Hpv. fold pv in Hpv.
  destruct (r3w_target A ae) as [off|] eqn:Htg; [|discriminate].
  destruct (sv_below (ss_next S) off) eqn:Hoffb; [|discriminate]. cbn [negb] in H.
  destruct (granule_of pv off) as [d|] eqn:Hgo; [|discriminate].
  destruct (q8_of_sound pv off d Hpv eq_refl Hoffb Hgo) as (Uq8 & Hnw8 & Hq8b). set (w := q8_of d) in *.
  assert (Uw : U rho w / 8 = U rho off) by (rewrite Uq8, Z.mul_comm, Z.div_mul by lia; reflexivity).
  pose proof Hsm as HsmX. destruct HsmX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & Hfr) & _). cbn [fst snd cfg_ms cfg_model] in Hfr.
  destruct (find_xr_d pv (ax_X A) d) as [[b l]|] eqn:Hfx.
  2:{
    destruct (r3w_lit_hit A off) as [[b l]|] eqn:Hlit; [|discriminate]. injection H as <-.
    unfold r3w_lit_hit in Hlit. destruct off as [tz| | | | | | |]; try discriminate.
    destruct (base_aligned8 A && (0 <=? tz) && (tz mod 8 =? 0) && (tz <? 2 ^ 61)) eqn:Hc; [|discriminate].
    apply andb_prop in Hc as [Hc Hc3]. apply andb_prop in Hc as [Hc Hc2]. apply andb_prop in Hc as [Hb8 Hc1].
    apply Z.leb_le in Hc1. apply Z.eqb_eq in Hc2. apply Z.ltb_lt in Hc3.
    destruct (find_xr_lit_sound _ _ _ _ Hlit) as (bz & lz & -> & -> & Hin & Hr1 & Hr2 & Hr3 & Hr4).
    set (a := Z.max (8 * tz) (bz mod 2 ^ 64)) in *.
    pose proof (proj1 (Forall_forall _ _) Hsh _ Hin) as Hxr. unfold xr_ok in Hxr. cbn [fst snd] in Hxr.
    destruct Hxr as (HB8 & HBL & Hall).
    assert (UB : bv_unsigned (eval rho (SLit bz)) = bz mod 2 ^ 64) by (cbn [eval]; rewrite Z_to_bv_unsigned; unfold bv_wrap; rewrite two64; reflexivity).
    assert (UL : bv_unsigned (eval rho (SLit lz)) = lz mod 2 ^ 64) by (cbn [eval]; rewrite Z_to_bv_unsigned; unfold bv_wrap; rewrite two64; reflexivity).
    rewrite UB, UL in Hall.
    destruct (Hall a ltac:(lia)) as (Hoff & _ & Hw & _).
    pose proof (base_aligned8_sound Hf Hb8) as HB0.
    assert (Ha8 : tz <= a / 8 <= tz + 7).
    { split; [apply Z.div_le_lower_bound; lia | apply Z.div_le_upper_bound; lia]. }
    assert (Ut : U rho (SLit tz) = tz) by (apply U_SLit; lia).
    pose proof (r3w_target_sound A ae (SLit tz) Hf Htg ltac:(rewrite Ut; lia)) as Uae. fold S in Uae. rewrite Ut in Uae.
    apply (r3w_fresh sgn rd rs1 imm ae Hi eq_refl).
    intros j Hj. destruct (Hw (Z.of_nat j) ltac:(lia)) as [Ho Hr]. unfold word_byte in Ho, Hr. rewrite Uae.
    pose proof (Z.div_mod (bv_unsigned (eval rho (ax_base A))) 8 ltac:(lia)) as Dbase. rewrite HB0, Z.add_0_r in Dbase.
    pose proof (Z.div_mod tz 8 ltac:(lia)) as Dt. rewrite Hc2, Z.add_0_r in Dt.
    assert (E1 : (bv_unsigned (eval rho (ax_base A)) + tz) / 8 * 8 = bv_unsigned (eval rho (ax_base A)) + tz).
    { set (X := bv_unsigned (eval rho (ax_base A)) + tz).
      assert (HX8 : X mod 8 = 0) by (unfold X; rewrite Z.add_mod, HB0, Hc2 by lia; reflexivity).
      pose proof (Z.div_mod X 8 ltac:(lia)). lia. }
    assert (E2 : (bv_unsigned (eval rho (ax_base A)) + a / 8) / 8 * 8 = bv_unsigned (eval rho (ax_base A)) + tz).
    { rewrite Dbase at 1. replace (8 * (bv_unsigned (eval rho (ax_base A)) / 8) + a / 8) with ((bv_unsigned (eval rho (ax_base A)) / 8) * 8 + a / 8) by lia.
      rewrite Z.div_add_l by lia.
      assert (a / 8 / 8 = tz / 8) as ->.
      { symmetry. apply Z.div_unique with (r := a / 8 - tz); [left; lia | lia]. }
      lia. }
    rewrite E1. rewrite E2 in Ho, Hr.
    rewrite (Hfr _ Ho). destruct (rm rho _) as [bb|]; [exists bb; reflexivity | congruence]. }
  destruct (find_xr_d_sound pv (ax_X A) d b l off Hpv eq_refl Hoffb Hgo Hfx) as (Hin & A1 & A2). fold w in A1, A2.

  pose proof (proj1 (Forall_forall _ _) Hsh (b, l) Hin) as Hxr. unfold xr_ok in Hxr. cbn [fst snd] in Hxr.
  destruct Hxr as (HB8 & HBL & Hall).
  assert (UBL : U rho (SAlu ALU_ADD b l) = U rho b + U rho l).
  { pose proof A2 as A2'. rewrite U_add in A2' |- *. unfold U in *. pose proof (urange (eval rho b)). pose proof (urange (eval rho l)).
    destruct (Z.eq_dec (bv_unsigned (eval rho b) + bv_unsigned (eval rho l)) (2 ^ 64)) as [E|E]; [rewrite E, Z.mod_same in A2' by lia; lia|].
    rewrite Z.mod_small; lia. }
  rewrite UBL in A2.
  destruct (Hall (U rho w) ltac:(unfold U in *; lia)) as (Hoff & _ & Hw & _).
  rewrite Uw in Hoff, Hw.

  pose proof (r3w_target_sound A ae off Hf Htg Hoff) as Uae. fold S in Uae.
  assert (Haddr : (rget (core_of ms) rs1 + sext 64 imm)%bv = eval rho ae).
  { subst ae. rewrite mk_addk_sound. rewrite <- (rget_match segs rho S tr ms md rs1 Hsm). reflexivity. }
  destruct (base_aligned8 A &&& blk64_ok pv b l d) eqn:Hc; injection H as <-.
  {
    apply lazy_andb_prop in Hc as [Hb8 Hblk]. apply lazy_andb_prop in Hblk as [HLo HHi].
    pose proof (base_aligned8_sound Hf Hb8) as HB0.
    destruct (e64_of_sound pv off d Hpv eq_refl Hoffb Hgo) as [E64 Q64]. fold w in Q64.
    set (Wq := U rho off / 8) in *.
    assert (LO64 : U rho b <= 64 * Wq).
    { apply lazy_orb_prop in HLo as [HL|HL]; [exact (blk64_lo_sound pv b w Wq Hpv HL Q64) | exact (blk64_lo_sound pv b _ Wq Hpv HL E64)]. }
    assert (HI64 : 64 * Wq + 64 <= U rho (SAlu ALU_ADD b l)).
    { apply lazy_orb_prop in HHi as [HH|HH]; [exact (blk64_hi_sound pv b l w Wq Hpv HH Q64) | exact (blk64_hi_sound pv b l _ Wq Hpv HH E64)]. }
    pose proof (Z.div_mod (U rho off) 8 ltac:(lia)) as Doff. pose proof (Z.mod_pos_bound (U rho off) 8 ltac:(lia)) as Moff.
    pose proof (Z.div_mod (bv_unsigned (eval rho (ax_base A))) 8 ltac:(lia)) as Dbase. rewrite HB0, Z.add_0_r in Dbase.
    assert (Uae' : bv_unsigned (eval rho ae) = bv_unsigned (eval rho (ax_base A)) + 8 * Wq).
    { rewrite Uae. subst Wq. rewrite Dbase at 1.
      replace (8 * (bv_unsigned (eval rho (ax_base A)) / 8) + U rho off) with ((bv_unsigned (eval rho (ax_base A)) / 8 * 8 + U rho off)) by lia.
      rewrite Z.div_add_l by lia. lia. }
    assert (BYTES : forall j, (j < 8)%nat -> ms_mem ms (Z_to_bv 64 (bv_unsigned (eval rho ae) + Z.of_nat j)) = Some (Z_to_bv 8 0)).
    { intros j Hj.
      destruct (r3_core (SAlu ALU_ADD ae (SLit (Z.of_nat j))) (64 * Wq + 8 * Z.of_nat j) b l Hin ltac:(lia) ltac:(rewrite UBL; lia)) as (v & Hmem & _ & _ & Hfast).
      { rewrite U_add, U_SLit by lia. unfold U. rewrite Uae'.
        replace (64 * Wq + 8 * Z.of_nat j) with ((8 * Wq + Z.of_nat j) * 8) by lia. rewrite Z.div_mul by lia. f_equal. lia. }
      assert (Hv0 : bv_unsigned v = 0).
      { apply Hfast. replace (64 * Wq + 8 * Z.of_nat j) with ((8 * Wq + Z.of_nat j) * 8) by lia. rewrite Z.div_mul by lia. lia. }
      assert (Ea : Z_to_bv 64 (bv_unsigned (eval rho ae) + Z.of_nat j) = eval rho (SAlu ALU_ADD ae (SLit (Z.of_nat j)))).
      { apply bv_eq. rewrite Z_to_bv_unsigned. change (bv_unsigned (eval rho (SAlu ALU_ADD ae (SLit (Z.of_nat j))))) with (U rho (SAlu ALU_ADD ae (SLit (Z.of_nat j)))).
        rewrite U_add, U_SLit by lia. unfold bv_wrap. rewrite two64. reflexivity. }
      rewrite Ea, Hmem. f_equal. apply bv_eq. rewrite Hv0. reflexivity. }
    pose proof (ov_read_bytes_zeros (ms_mem ms) (eval rho ae) 8%nat BYTES) as Hrd.
    set (K := fun v0 : word => EDone (rset rd v0 (with_pc (c_pc (core_of ms) + Z_to_bv 64 4)%bv (core_of ms)))).
    destruct (interp_load_val segs SZ8 sgn (eval rho ae) K (ms_mem ms) (repeat (Z_to_bv 8 0) 8%nat) Hrd) as (VAL & Hint & HVAL).
    assert (UVAL : VAL = Z_to_bv 64 0).
    { rewrite HVAL. unfold le_bytes_to_word. rewrite bytes_le_to_Z_zeros. apply ext_low_zero. cbn; lia. }
    set (ms1 := ms_of ms (rset rd VAL (with_pc (Z_to_bv 64 (ss_pc S + 4)) (core_of ms))) (ms_mem ms)).
    assert (STEP : RiscvSemantics.step segs ms = MachineOk ms1).
    { rewrite (step_instr_at segs ms (ss_pc S) _ Hpc Hi ltac:(discriminate)).
      change (exec (Z_to_bv 64 4) (Load SZ8 sgn rd rs1 imm) (core_of ms))
        with (load_val SZ8 sgn (rget (core_of ms) rs1 + sext 64 imm)%bv K).
      rewrite Haddr, Hint. unfold K. cbn [interp_eff0 lift_result].
      change (c_pc (core_of ms)) with (ms_pc_val ms). unfold ms_pc in Hpc. rewrite Hpc, pc_plus'. reflexivity. }
    exists ms1, rho. split; [exact STEP|]. split; [apply agree_below_refl|]. split; [rewrite ss_next_set_pc_reg; lia|].
    eapply smatch_rd_pc; [exact Hsm | reflexivity |]. cbn [eval]. symmetry. exact UVAL. }

  assert (BY : forall j, (j < 8)%nat -> exists bb, ms_mem ms (Z_to_bv 64 (bv_unsigned (eval rho ae) + Z.of_nat j)) = Some bb).
  { intros j Hj. destruct (Hw (Z.of_nat j) ltac:(lia)) as [Ho Hr]. unfold word_byte in Ho, Hr. rewrite Uae.
    rewrite (Hfr _ Ho). destruct (rm rho _) as [bb|]; [exists bb; reflexivity | congruence]. }
  exact (r3w_fresh sgn rd rs1 imm ae Hi eq_refl BY).
Qed.

End R3.

End RSound.

Section Sound.
Variable segs : list Segment.

Lemma amo_bytes_AD : ltac2:(tb__ "0|3|
S128S92Q40M0A1M1G1S0S0S0S8S57S44S0A1Sb8R7S13aR4R3A4S46S0R2A2A3S57G1ScR2R5A2R7A3S57G1ScR3R5A2R7A3S57S47S92Q8A1A1S1b9U8M2S93G0S1b6G0RaR9R8A4A2A2S20G2ScR4R5A2A2A3F_;F_;F_;Frho;Fnv;Fvs;Fvo;Fsrc;Fold;Fop;").
Proof.
  intros op old src vo vs nv rho H Ho Hs. unfold enc_bytes.
  destruct op; cbn in H; try discriminate; injection H as <-; cbn [eval]; rewrite ?Ho, ?Hs; reflexivity.
Qed.

Lemma mod32_of_mod64 : ltac2:(tb__ "0|2|
S5eS57S5eS113S113R1S112Z2M0Z40A2A2S112G0Z20A2M1A2S113R1G1A2A3Fz;").
Proof.
  intros z. apply Z.mod_mod_divide. exists (2 ^ 32). reflexivity.
Qed.

Lemma amo_bytes_AW : ltac2:(tb__ "0|4|
S128S92Q20M0A1S92Q40M1A1M2S0S0S0S8S57S44S0A1Sb8R7S13eR4R3A4S46S0R2A2A3S57G2ScR2R5A2S1bcG0G1R7A3A3S57G2ScR3R5A2R7A3S57S47S92Q8A1A1S1b9U4M3S93G0S1b6G0RaR9S1b8R8A1A4A2A2S20G3ScR4R5A2A2A3F_;F_;F_;Frho;Fnv;Fvs;Fvo;Fsrc;Fold;Fop;").
Proof.
  intros op old src vo vs nv rho H Ho Hs. unfold enc_bytes.
  rewrite <- (Z_to_le_bytes_mod 4 (bv_unsigned (amo_val op old (low32 src)))).
  rewrite <- (Z_to_le_bytes_mod 4 (bv_unsigned (eval rho nv))). f_equal.
  change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32).
  destruct op; cbn in H; try discriminate; injection H as <-; cbn [eval amo_val]; rewrite ?Ho, ?Hs.
  -   rewrite low32_umod. rewrite Z.mod_mod by lia. reflexivity.
  -   unfold alu64, alu. rewrite !bv_add_unsigned. unfold bv_wrap.
    change (bv_modulus 32) with (2 ^ 32). change (bv_modulus 64) with (2 ^ 64).
    rewrite low32_umod. transitivity ((bv_unsigned old + bv_unsigned src) mod 2 ^ 32).
    + rewrite Z.mod_mod by lia. rewrite Zplus_mod_idemp_r. reflexivity.
    + rewrite mod32_of_mod64. rewrite <- (Zplus_mod_idemp_l (bv_unsigned (sext 64 old))).
      rewrite (sext64_32_mod old 32) by lia. rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

Lemma amo_alignedb_sound : ltac2:(tb__ "0|0|
S8S1S45S47S153A1S151A2S127S0S12Vsegs;R5R4R3A4S57S43Se4S4R5A1R2S7aR3A1A3S48A3S57S43S1b7R4ScR7R3A2A2S48A3F_;F_;Fae;Fwd;Fw;FS;Frho;").
Proof using .
  intros rho S w wd ae Hsm H. unfold amo_alignedb in H. apply lazy_orb_prop in H as [H|H]; [eapply amo_aligned_of; eauto|].
  apply andb_prop in H as [H0 H1]. apply Z.leb_le in H0. apply Z.leb_le in H1.
  pose proof (smatch_facts segs _ _ _ Hsm) as Hf.
  pose proof (align_sv_mod rho (ss_facts S) ae (amo_log wd) Hf H0 H1) as Hm. unfold U in Hm.
  unfold amo_aligned, amo_bytes. apply Z.eqb_eq. destruct wd; cbn [amo_log] in Hm.
  - change 4 with (2 ^ 2). exact Hm.
  - change 8 with (2 ^ 3). exact Hm.
Qed.

Lemma case_amo : ltac2:(tb__ "0|3|
S1S128S127S43S43S92Q5A1M0G0G0S0S1S0S1S8S47S153A1M1S143S154S57S44S122A1S67Vsegs;S6R10A1A2S46S122S13fRfReRdRcRbRaR9A7A2A3S57S43S18R11A1S49A3S57S43Se4S4R12A1S63R12RcA2S7aR10A1A3S48A3S57S44S0A1M2S1eR13A1S4cS0A1A3S57S72S7dVsegs;R14S63R14ReA2S79R12A1S48A5S74RcRbA2A3S57G2Sb8R14R13RdS63R15ReA2A4S46S0RbA2A3S57S44S1A1S7eRdS63R16R10A2S79R14A1RcA4S46S1RbA2A3S12Vsegs;RbR17S4bG1S151RaS152R9R8A2A4A4S142Vsegs;R18S62S65RdR13R10A3S110S6R18A1Z4A2A2RcRbRaR9A7F_;F_;F_;F_;F_;F_;F_;F_;Fmd;Fms;Ftr;Frho;FS2;Fnv;FS1;Fv;Frs2;Frs1;Frd;Frl;Faq;Fwd;Fop;FS;").
Proof.
  intros S op wd aq rl rd rs1 rs2 v S1 nv S2 rho tr ms md Hi Hlen Hal Hresv Hload Hamo Hst Hsm.
  pose proof Hsm as Hsm0.
  destruct Hsm as (Hwf & Hpc & Hpend & Hhalt & Hrom & Hroc & Hregs & Hfregs & Hfcsr & Hresvm & Hmem & Hfacts).
  cbn [fst snd cfg_ms cfg_model] in *.
  assert (Hae : sv_below (ss_next S) (get_reg S rs1) = true) by (apply get_reg_below; exact Hwf).
  assert (Hsrc : sv_below (ss_next S) (get_reg S rs2) = true) by (apply get_reg_below; exact Hwf).
  assert (Hresv0 : ms_resv ms = None).
  { unfold resv_match in Hresvm. rewrite Hresv in Hresvm. destruct (ms_resv ms); [destruct Hresvm|reflexivity]. }
  pose proof (amo_alignedb_sound rho S _ wd _ Hsm0 Hal) as Hamoal.
  rewrite <- (rget_match segs rho S tr ms md rs1 Hsm0) in Hamoal.

  destruct (sym_load_sound_gen segs rho S tr ms md _ (amo_k wd) true v S1 Hsm0 Hae (amo_k_cases wd) Hload) as [(Hlen' & _) | HLP];
    [rewrite Hlen in Hlen'; discriminate|].
  destruct (load_post_proj segs _ _ _ _ _ _ _ _ _ _ HLP)
    as (bs & rho' & Hrd & Hag & Hnext & Hsm1 & Hev & Hbelow & Hpc1 & Hregs1 & Hfregs1 & Hfcsr1 & Hresv1 & Hfacts1).
  pose proof (smatch_swf segs _ _ _ Hsm1) as Hwf1.
  rewrite <- (ov_read_bytes_rd segs ms) in Hrd by exact Hrom.

  assert (Hae1 : sv_below (ss_next S1) (get_reg S rs1) = true) by (eapply sv_below_mono; [exact Hnext | exact Hae]).
  assert (Hnv1 : sv_below (ss_next S1) nv = true).
  { eapply amo_sv_below; [exact Hbelow | | exact Hamo]. eapply sv_below_mono; [exact Hnext | exact Hsrc]. }
  destruct (sym_store_sound segs S1 _ (amo_k wd) nv S2 rho' tr ms md Hst Hsm1 Hae1 Hnv1 (amo_k_cases wd)) as (Hsok & objs' & ES2 & Hwf2 & Hpost).
  cbn zeta in Hsok, Hpost.
  rewrite <- (eval_agree (ss_next S) rho rho' (get_reg S rs1) Hag Hae) in Hsok, Hpost.
  set (a := eval rho (get_reg S rs1)) in *.
  assert (Ha : rget (core_of ms) rs1 = a) by (unfold a; apply (rget_match segs rho S tr ms md rs1 Hsm0)).
  assert (Hs2 : rget (core_of ms) rs2 = eval rho' (get_reg S rs2)).
  { rewrite (rget_match segs rho S tr ms md rs2 Hsm0). apply (eval_agree (ss_next S) rho rho'); [exact Hag | exact Hsrc]. }
  set (bsw := enc_bytes (Z.to_nat (amo_k wd)) (eval rho' nv)) in *.
  set (m' := write_to_mem (ms_mem ms) a bsw).
  set (old := eval rho' v).
  set (cn := with_pc (Z_to_bv 64 (ss_pc S + 4)) (core_of ms)).
  set (ms0 := ms_of ms cn m').
  set (ms1 := ms_of ms (rset rd old cn) m').
  destruct (Hpost ms0 eq_refl eq_refl) as [Hroc1 Hmem1].
  subst S2.
  exists ms1, rho'. split; [|split; [exact Hag | split; [cbn; rewrite ss_next_set_reg; cbn; lia|]]].
  - rewrite (step_instr_at segs ms (ss_pc S) _ Hpc Hi ltac:(discriminate)).
    cbn [exec]. rewrite Hamoal. cbn [negb].
    assert (Hnpc : (c_pc (core_of ms) + Z_to_bv 64 4)%bv = Z_to_bv 64 (ss_pc S + 4)).
    { cbn [c_pc core_of]. change (ms_pc_val ms) with (ms_pc ms). rewrite Hpc. apply pc_plus'. }
    assert (Hinv : inval_resv (rget (core_of ms) rs1) (with_pc (c_pc (core_of ms) + Z_to_bv 64 4)%bv (core_of ms)) = cn).
    { unfold inval_resv, cn. cbn [c_resv with_pc core_of]. rewrite Hresv0. rewrite Hnpc. reflexivity. }
    rewrite Ha, Hs2.
    destruct wd; cbn [interp_eff0 width_bytes amo_k] in Hsok, Hrd |- *.
    + change (Z.to_nat 4) with 4%nat in Hsok, Hrd, bsw. rewrite Hrd. cbn [interp_eff0 width_bytes]. rewrite Hsok.
      rewrite Ha in Hinv. rewrite Hinv. cbn [interp_eff0].
      rewrite (amo_bytes_AW op _ _ v (get_reg S rs2) nv rho' Hamo); [| rewrite Hev; reflexivity | reflexivity].
      unfold lift_result, ms1, old. rewrite Hev. reflexivity.
    + change (Z.to_nat 8) with 8%nat in Hsok, Hrd, bsw. rewrite Hrd. cbn [interp_eff0 width_bytes]. rewrite Hsok.
      rewrite Ha in Hinv. rewrite Hinv. cbn [interp_eff0].
      rewrite (amo_bytes_AD op _ _ v (get_reg S rs2) nv rho' Hamo); [| rewrite Hev; cbn [ext_low amo_k]; apply sext_64_64 | reflexivity].
      unfold lift_result, ms1, old. rewrite Hev. cbn [ext_low amo_k Z.to_N N.mul]. rewrite sext_64_64. reflexivity.
  - destruct Hsm1 as (_ & _ & _ & _ & _ & _ & Hregs' & Hfregs' & Hfcsr' & Hresvm' & _ & Hfacts').
    cbn [fst snd cfg_ms cfg_model] in *.
    set (Sst := set_objs S1 objs').
    assert (HsmA : smatch segs rho' (set_pc Sst (ss_pc S + 4)) (tr, mkCfg ms0 md)).
    { unfold smatch. cbn [fst snd cfg_ms cfg_model set_pc set_objs ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next Sst].
      split; [rewrite swf_set_pc; exact Hwf2 |].
      split; [reflexivity | split; [reflexivity | split; [exact Hhalt | split; [exact Hrom | split; [exact Hroc1|]]]]].
      split; [eapply regs_match_same; [exact Hregs' | reflexivity | reflexivity]|].
      split; [eapply fregs_match_same; [exact Hfregs' | reflexivity | reflexivity]|].
      split; [unfold fcsr_match in Hfcsr' |- *; destruct (ss_fcsr S1); cbn; exact Hfcsr'|].
      split; [rewrite Hresv1, Hresv; unfold resv_match; cbn; rewrite Hresv0; exact I|].
      split; [exact Hmem1 | exact Hfacts']. }
    assert (HbelowS : sv_below (ss_next (set_pc Sst (ss_pc S + 4))) v = true) by (cbn; exact Hbelow).
    pose proof (smatch_rd_pc segs rho' (set_pc Sst (ss_pc S + 4)) tr ms0 md rd v old (ss_pc S + 4) HsmA HbelowS eq_refl) as HsmB.
    assert (Ems : ms_of ms0 (rset rd old (with_pc (Z_to_bv 64 (ss_pc S + 4)) (core_of ms0))) (ms_mem ms0) = ms1).
    { unfold ms1, ms0, cn, ms_of, rset, with_resv, with_pc, with_regs, core_of. destruct (is_x0 rd); reflexivity. }
    rewrite Ems in HsmB.
    assert (ES : set_pc (set_reg (set_pc Sst (ss_pc S + 4)) rd v) (ss_pc S + 4) = set_pc (set_reg Sst rd v) (ss_pc S + 4)).
    { unfold set_pc, set_reg. destruct (regZ rd =? 0); reflexivity. }
    rewrite ES in HsmB. exact HsmB.
Qed.

Lemma pow2_log_spec : ltac2:(tb__ "0|0|
S5eS5eS57S44S5eA1S10aR2A1S46S5eR1A2A3S58S58S111Z1R2A2S111R2Z3fA2A2S57S5eS112Z2R2A2R3A3A2F_;Fk;Fm;").
Proof.
  intros m k H. unfold pow2_log in H.
  destruct ((1 <=? Z.log2 m) && (Z.log2 m <=? 63) && (2 ^ Z.log2 m =? m)) eqn:E; [|discriminate]. injection H as <-.
  apply andb_prop in E as [E E3]. apply andb_prop in E as [E1 E2].
  apply Z.leb_le in E1. apply Z.leb_le in E2. apply Z.eqb_eq in E3. split; [lia | exact E3].
Qed.

Lemma case_divpow2 : ltac2:(tb__ "0|2|
S1S125S92Q5A1M0G0G0S61S8S47S153A1M1S143S154S57S44S122A1S67Vsegs;S6RaA1A2S46S122S140R9R8R7R6A4A2A3S57S44S61A1SceRbRaR9R8R7A5S46S61R6A2A3S12Vsegs;R6RcS4bG1S151R5S152R4R3A2A4A4S61OLo;R8S1S142Vsegs;ReR1R8R7R6R5A7LS';S1S1S59S142Vsegs;RfR2R9R8R7R6A7S142Vsegs;RfR1R9R8R7R6A7A2LS2;LS1;S68S5aLr;X61x3F_;F_;F_;Fmd;Fms;Ftr;Frho;Fo;Frs2;Frs1;Frd;Fop;FS;").
Proof.
  intros S op rd rs1 rs2 o rho tr ms md Hi H Hsm. unfold divpow2_step in H.
  pose proof (smatch_swf segs _ _ _ Hsm) as Hwf.
  destruct (get_reg S rs2) as [m| | | | | | |] eqn:Hr2; try discriminate.
  destruct (pow2_log (m mod 2 ^ 64)) as [k|] eqn:Hk; [|discriminate].
  destruct (pow2_log_spec _ _ Hk) as [Hk1 Hk2].
  assert (R2 : rget (core_of ms) rs2 = Z_to_bv 64 m).
  { rewrite (rget_match segs rho S tr ms md rs2 Hsm). rewrite Hr2. reflexivity. }
  assert (U2 : bv_unsigned (Z_to_bv 64 m) = 2 ^ k).
  { rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite two64. symmetry. exact Hk2. }
  assert (NZ : (bv_unsigned (Z_to_bv 64 m) =? 0) = false).
  { apply Z.eqb_neq. rewrite U2. pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) ltac:(lia)). lia. }
  pose proof (urange (rget (core_of ms) rs1)) as R1.
  destruct op; try discriminate; injection H as <-; cbn.
  -
    eapply step_rd_sound; [exact Hsm | exact Hi | discriminate | reflexivity | eapply npc_eq; eauto
      | apply mk_alu_below; [apply get_reg_below; exact Hwf | reflexivity] |].
    rewrite mk_alu_sound. rewrite <- (rget_match segs rho S tr ms md rs1 Hsm). cbn [eval]. rewrite R2.
    unfold mul_div. rewrite NZ. apply bv_eq. rewrite srl_val, bv_divu_unsigned, U2.
    rewrite Z.mod_small by lia. rewrite Z.shiftr_div_pow2 by lia. reflexivity.
  -
    eapply step_rd_sound; [exact Hsm | exact Hi | discriminate | reflexivity | eapply npc_eq; eauto
      | apply mk_alu_below; [apply get_reg_below; exact Hwf | reflexivity] |].
    rewrite mk_alu_sound. rewrite <- (rget_match segs rho S tr ms md rs1 Hsm). cbn [eval]. rewrite R2.
    unfold mul_div. rewrite NZ. apply bv_eq. rewrite and_val, bv_modu_unsigned, U2.
    rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite two64.
    assert (Hm1 : (m mod 2 ^ 64 - 1) mod 2 ^ 64 = 2 ^ k - 1).
    { rewrite <- Hk2. pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) ltac:(lia)).
      assert (2 ^ k < 2 ^ 64) by (apply Z.pow_lt_mono_r; lia). rewrite Hk2 in *. apply Z.mod_small.
      pose proof (Z.mod_pos_bound m (2 ^ 64) ltac:(lia)). lia. }
    rewrite Hm1. replace (2 ^ k - 1) with (Z.ones k) by (unfold Z.ones; rewrite Z.shiftl_1_l; lia).
    rewrite Z.land_ones by lia. reflexivity.
Qed.

Lemma nth_error_list_set_same : forall {T} (l : list T) n x y,
  nth_error l n = Some y -> nth_error (list_set l n x) n = Some x.
Proof. induction l as [|h t IH]; intros [|n] x y H; cbn in *; try discriminate; [reflexivity | eapply IH; exact H]. Qed.

Lemma nth_error_list_set_other : forall {T} (l : list T) n i x,
  i <> n -> nth_error (list_set l n x) i = nth_error l i.
Proof. induction l as [|h t IH]; intros [|n] [|i] x Hne; cbn; try reflexivity; [congruence|]. apply IH. lia. Qed.

Lemma nth_error_lt : forall {T} (l : list T) n x, nth_error l n = Some x -> (n < length l)%nat.
Proof. induction l as [|h t IH]; intros [|n] x H; cbn in *; try discriminate; [lia|]. apply IH in H. lia. Qed.

Lemma list_set_set : forall {T} (l : list T) n x y, list_set (list_set l n x) n y = list_set l n y.
Proof. induction l as [|h t IH]; intros [|n] x y; cbn; [reflexivity|reflexivity|reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma Forall_list_set_inv : forall {T} (P : T -> Prop) l n x,
  Forall P (list_set l n x) -> (n < length l)%nat -> P x /\ forall i y, i <> n -> nth_error l i = Some y -> P y.
Proof.
  induction l as [|h t IH]; intros [|n] x H Hn; cbn in *; [lia|lia| |].
  - inversion H; subst. split; [assumption|]. intros [|i] y Hi Hy; [congruence|]. cbn in Hy.
    exact (proj1 (Forall_forall _ _) H3 y (nth_error_In _ _ Hy)).
  - inversion H; subst. destruct (IH n x H3 ltac:(lia)) as [Px Pr]. split; [exact Px|].
    intros [|i] y Hi Hy; cbn in Hy; [injection Hy as <-; exact H2|]. eapply Pr; [|exact Hy]. lia.
Qed.

Lemma Forall_of_nth : forall {T} (P : T -> Prop) (l : list T),
  (forall i y, nth_error l i = Some y -> P y) -> Forall P l.
Proof.
  induction l as [|h t IH]; intros H; constructor; [exact (H 0%nat h eq_refl)|]. apply IH. intros i y Hy. exact (H (Datatypes.S i) y Hy).
Qed.

Lemma store_cells_z_spec : ltac2:(tb__ "0|8|
S47S2A1S47S7A1M0S0S5eS7S149S7R1S51G0S43Sc7R5R4R3R2A4A3A3S5bS7S7S58S149S7R1R6A3S59S58S57S43SbaS19R1A1A1S48A3S57S7R3R1A3M1A2S59S58S57S77S76R7R5R4R1A4S7fA3G1A2S59S5bS5eS5eS58S57S77S76R8R6R5R2A4S80R1A1A3M2S58S57S43S82R1S23R2A1M3R5A3M4S49A3S57S7R4R2A3A2A2Ld;A2S59S5bS5eS5eS58G2S58S57S43G4S48A3M5S58S116R1Z0A2S57S7R4S1cS29R2A1S11bR1A1S19R2A1M6A3A3A2A2A2Ld;A2S5bS5eS5eS58G2S58G5S58S116R5S110R1G3A2M7A2S57S7R4S1cS6aR6R5A2S118G7R5A2S70S129G6S5S114Z8S118R5R1A2A2A1A3A3A3A2A2A2Ld;A2A2A2A2A2A2Lc;A2F_;Fc';Fk;Foff;Fcells;Ffacts;").
Proof using .
  intros facts cells off k. induction cells as [|c rest IH]; intros c' Hin; cbn [store_cells_z] in Hin; [destruct Hin|].
  destruct (store_cells_z facts rest off k) as [rest' taint] eqn:E. cbn [fst] in IH.
  Local Ltac rest_case IH Hin := destruct (IH _ Hin) as (c0 & Hc0 & R); exists c0; split; [right; exact Hc0 | exact R].
  cbn zeta in Hin.
  Local Ltac zero_case c := exists c; split; [left; reflexivity|]; left; auto.
  destruct (cell_rel facts off k c) as [d| |] eqn:Hcr; cbn [fst] in Hin.
  - destruct (lit_overlaps d (c_width c) k) eqn:Ho; cbn [fst] in Hin.
    + apply in_app_or in Hin as [Hin|Hin].
      * destruct (d <? 0) eqn:E1; [|destruct Hin]. apply Z.ltb_lt in E1. destruct Hin as [<-|[]].
        exists c. split; [left; reflexivity|]. right; right; right; left. exists d. auto.
      * apply in_app_or in Hin as [Hin|Hin].
        -- destruct (k <? d + c_width c) eqn:E2; [|destruct Hin]. apply Z.ltb_lt in E2. destruct Hin as [<-|[]].
           exists c. split; [left; reflexivity|]. right; right; right; right. exists d. auto.
        -- destruct (is_zero_lit (c_val c)) eqn:Hz; [destruct Hin as [<-|Hin]; [zero_case c|rest_case IH Hin] | rest_case IH Hin].
    + destruct Hin as [<-|Hin]; [|rest_case IH Hin].
      exists c. split; [left; reflexivity|]. right; right; left. exists d. auto.
  - destruct Hin as [<-|Hin]; [|rest_case IH Hin].
    exists c. split; [left; reflexivity|]. right; left. auto.
  - destruct (is_zero_lit (c_val c)) eqn:Hz; [destruct Hin as [<-|Hin]; [zero_case c|rest_case IH Hin] | rest_case IH Hin].
Qed.

Lemma store_cells_z_notaint : ltac2:(tb__ "0|5|
S47S2A1S47S7A1M0S0S5eS7S57S43S4eG0S43Sc7R5R4R3R2A4A3S49A3S149S7R2R5A3S51G0S43Sc7R7R6R5R4A4A3G0S59S58S57S43SbaS19R4A1A1S48A3S149S7R4R1A3M1A2S59S58S57S77S76R8R6R5R4A4S7fA3G1A2S5bS5eS5eS58S57S77S76R9R7R6R5A4S80R1A1A3S59S58S57S43S82R1S23R5A1M2R6A3M3S49A3S149S7R5R2A3A2S58S57S43G3S48A3S58S116R1Z0A2S149S7S1cS29R6A1S11bR2A1S19R6A1M4A3R3A3F_;S116R6S110R1G2A2A2S149S7S1cS6aR8R7A2S118S110R2S23R6A1A2R7A2S70S129G4S5S114Z8S118R7R2A2A2A1A3A3R3A3F_;A2A2A2A2Ld;A2A2A2Tcells';F_;F_;Fc;Fk;Foff;Fcells;Ffacts;").
Proof using .
  intros facts cells off k. induction cells as [|c0 rest IH]; intros c Ht Hin; [destruct Hin|].
  cbn [store_cells_z] in Ht |- *.
  destruct (store_cells_z facts rest off k) as [rest' taint] eqn:E. cbn [fst snd] in IH.
  set (RES := (let z := is_zero_lit (c_val c0) in
            match cell_rel facts off k c0 with
            | CLit d => if lit_overlaps d (c_width c0) k
                        then ((if d <? 0 then [mkCell (c_off c0) (- d) (c_val c0)] else [])
                              ++ (if k <? d + c_width c0
                                  then [mkCell (mk_addk off k) (d + c_width c0 - k) (mk_alu ALU_SRL (c_val c0) (SLit (8 * (k - d))))]
                                  else []) ++ (if z then c0 :: rest' else rest'), taint)
                        else (c0 :: rest', taint)
            | CDisj => (c0 :: rest', taint)
            | CUnk => if z then (c0 :: rest', taint) else (rest', true)
            end)) in *.
  assert (SUB : forall x, In x rest' -> In x (fst RES)).
  { intros x Hx. subst RES. cbn zeta.
    destruct (cell_rel facts off k c0) as [d| |]; cbn [fst].
    - destruct (lit_overlaps d (c_width c0) k); cbn [fst]; [|right; exact Hx].
      apply in_or_app. right. apply in_or_app. right. destruct (is_zero_lit (c_val c0)); [right|]; exact Hx.
    - right. exact Hx.
    - destruct (is_zero_lit (c_val c0)); [right; exact Hx | exact Hx]. }
  assert (Ht' : taint = false).
  { subst RES. cbn zeta in Ht.
    destruct (cell_rel facts off k c0) as [d| |]; cbn [snd] in Ht.
    - destruct (lit_overlaps d (c_width c0) k); cbn [snd] in Ht; exact Ht.
    - exact Ht.
    - destruct (is_zero_lit (c_val c0)); [exact Ht | discriminate]. }
  destruct Hin as [E0|Hin].
  - subst c0. subst RES. cbn zeta in Ht |- *.
    destruct (cell_rel facts off k c) as [d| |] eqn:Hcr; cbn [fst snd] in Ht |- *.
    + right. right. exists d. split; [reflexivity|].
      destruct (lit_overlaps d (c_width c) k) eqn:Ho; cbn [fst].
      * right. split; [reflexivity|]. split.
        -- intros Hd. apply in_or_app. left. rewrite (proj2 (Z.ltb_lt d 0) Hd). left. reflexivity.
        -- intros Hk. apply in_or_app. right. apply in_or_app. left. rewrite (proj2 (Z.ltb_lt _ _) Hk). left. reflexivity.
      * left. split; [reflexivity|]. left. reflexivity.
    + right. left. split; [reflexivity|]. left. reflexivity.
    + destruct (is_zero_lit (c_val c)) eqn:Hz; [|discriminate]. left. split; [reflexivity|]. left. reflexivity.
  - destruct (IH c Ht' Hin) as [[Hz HinR] | [[Hcr HinR] | (d & Hcr & R)]].
    + left. split; [exact Hz|]. apply SUB. exact HinR.
    + right. left. split; [exact Hcr|]. apply SUB. exact HinR.
    + right. right. exists d. split; [exact Hcr|].
      destruct R as [[Ho HinR] | (Ho & R1 & R2)].
      * left. split; [exact Ho | apply SUB; exact HinR].
      * right. split; [exact Ho|]. split; intros H; apply SUB; auto.
Qed.

Lemma enc_bytes_zero_nth : ltac2:(tb__ "0|5|
S4dS92Q40M0A1S4dS57S5eS93G0R2A2Z0M1A3S1b4R2R4A2S57S92Q8M2A1M3S158G3R3S20R5R4A2S94G2G1A2M4A4G4A3F_;F_;Fj;Fv;Fk;").
Proof using .
  intros k v j Hv Hj. unfold enc_bytes. rewrite Z_to_le_bytes_nth by exact Hj. rewrite Hv, Z.shiftr_0_l. reflexivity.
Qed.

Lemma is_zero_lit_sound : ltac2:(tb__ "0|0|
S8S0S57S43SbaR1A1S48A3S57S5eS93Q40ScR3R2A2A2Z0A3F_;Fv;Frho;").
Proof using .
  intros rho v H. destruct v; cbn in H; try discriminate. apply Z.eqb_eq in H. cbn [eval].
  rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite two64. exact H.
Qed.

Lemma obj_holds_store_z : ltac2:(tb__ "0|3|
S8S5fS143S143S3S47S2A1S0S5eS0S35Vsegs;R7A2S155S2S14RaA1R5A3S2bVsegs;RbR9R7A4S57S43S26RbR8A2S48A3S57S43S15SeR9A1A1S48A3S57S43S16SeRaA1A1S49A3S111S32RfRbA2S21RfR9A2A2S111S110S21R10RaA2R9A2S31R10RcA2A2S116Z0M0RaA2S111RbZ8A2S57S5eS93Q40M1ScR13RbA2A2G0A3S57S92G1A1S44S92Q8A1A1F_;M2S145R11A1S145R12A1A3S57G2S144R12A1S146S144R13A1S30R15S1dR11A1S21R15RfA2A3S20S11cReA1ScR15RdA2A2A3A3S2bVsegs;R16R13Sb3R11R12R10RfReA5A4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fv;Fk;Foff;Ffacts;Fo;Fms';Fms;Fn;Frho;").
Proof using .
  intros rho n ms ms' o facts off k v Hrom Hf Hoh Howf Hdw Hna Hlo Hhi Hk Hk8 Hv0 Hr Hm.
  pose proof Hoh as (Hb & Hw0 & Hcells & Hd & Hdl).
  assert (Hw : forall off0, obj_lo_of rho o <= off0 < obj_hi_of rho o ->
               wview segs (ms_mem ms) (Z_to_bv 64 (bv_unsigned (eval rho (ob_base o)) + off0)) <> None)
    by (intros off0 Hoff0; apply Hw0; [exact Hoff0 | exact Hdw]).
  set (A := soff rho off) in *.
  unfold obj_lo_of, obj_hi_of in *.
  pose proof (soff_range rho (ob_hi o)) as Rhi. pose proof (soff_range rho (ob_lo o)) as Rlo.
  assert (Ha : bv_unsigned (oaddr rho (ob_base o) A) = bv_unsigned (eval rho (ob_base o)) + A)
    by (apply oaddr_unsigned; lia).
  assert (Hlen : length (enc_bytes (Z.to_nat k) (eval rho v)) = Z.to_nat k) by apply enc_bytes_length.
  assert (Hout : forall off', ~ (A <= off' < A + k) -> 0 <= bv_unsigned (eval rho (ob_base o)) + off' < 2 ^ 64 ->
            ms_mem ms' (Z_to_bv 64 (bv_unsigned (eval rho (ob_base o)) + off')) = ms_mem ms (Z_to_bv 64 (bv_unsigned (eval rho (ob_base o)) + off'))).
  { intros off' Hoff' Hrange. rewrite Hm. apply write_to_mem_out.
    - rewrite Ha, Hlen, Z2Nat.id by lia. lia.
    - rewrite Ha, Hlen, Z2Nat.id by lia. rewrite Z_to_bv_unsigned, bv_wrap_small by (rewrite two64; lia). lia. }

  assert (Hin0 : forall off', A <= off' < A + k ->
            rd ms' (Z_to_bv 64 (bv_unsigned (eval rho (ob_base o)) + off')) = Some (Z_to_bv 8 0)).
  { intros off' Hoff'. unfold rd, ms_read_byte. rewrite Hm.
    replace (bv_unsigned (eval rho (ob_base o)) + off') with (bv_unsigned (oaddr rho (ob_base o) A) + Z.of_nat (Z.to_nat (off' - A))) by (rewrite Ha; lia).
    rewrite write_to_mem_in; [| rewrite Ha, Hlen, Z2Nat.id by lia; lia | rewrite Hlen; lia].
    rewrite enc_bytes_zero_nth; [reflexivity | exact Hv0 | lia]. }
  assert (Hrdu : forall off' k', soff rho (ob_lo o) <= off' -> off' + k' <= soff rho (ob_hi o) -> 0 < k' ->
            (off' + k' <= A \/ A + k <= off') ->
            rd_bytes ms' (oaddr rho (ob_base o) off') (Z.to_nat k') = rd_bytes ms (oaddr rho (ob_base o) off') (Z.to_nat k')).
  { intros off' k' H1 H2 H3 H4. apply rd_bytes_unchanged; [exact Hr| |].
    - rewrite oaddr_unsigned by lia. rewrite Z2Nat.id by lia. lia.
    - intros j Hj. rewrite oaddr_unsigned by lia. rewrite <- Z.add_assoc. apply Hout; lia. }

  assert (Hrd' : forall off', soff rho (ob_lo o) <= off' < soff rho (ob_hi o) ->
            exists b, rd ms' (Z_to_bv 64 (bv_unsigned (eval rho (ob_base o)) + off')) = Some b).
  { intros off' Hoff'. destruct (obj_byte_readable segs rho ms o off' n Hrom Howf Hoh Hoff') as [b Hbb].
    unfold rd, ms_read_byte in *. rewrite Hr.
    destruct (ms_mem ms' (Z_to_bv 64 (bv_unsigned (eval rho (ob_base o)) + off'))) as [b'|] eqn:E'; [eexists; reflexivity|].
    rewrite Hm in E'. apply write_to_mem_keeps_none in E'. rewrite E' in Hbb. exists b. exact Hbb. }
  unfold obj_store_z. destruct (store_cells_z facts (ob_cells o) off k) as [cells' taint] eqn:Esc.
  unfold obj_holds, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt].
  split; [exact Hb|]. split.
  { intros off' Hoff' _. rewrite Hm.
    apply wview_mono with (m := ms_mem ms); [|apply Hw; exact Hoff'].
    intros y Hy. apply write_to_mem_grows. exact Hy. }
  split.
  { constructor.
    -
      unfold cell_holds. cbn [c_off c_width c_val]. fold A. split; [lia|]. split; [lia|].
      apply rd_bytes_of_nth; [exact Hlen | rewrite Ha, Z2Nat.id by lia; lia |].
      intros j Hj. unfold rd, ms_read_byte. rewrite Hm, Ha.
      rewrite <- Ha at 1. rewrite write_to_mem_in; [reflexivity | rewrite Ha, Hlen, Z2Nat.id by lia; lia | rewrite Hlen; exact Hj].
    - apply Forall_forall. intros c' Hin'.
      assert (HinC : In c' (fst (store_cells_z facts (ob_cells o) off k))) by (rewrite Esc; exact Hin').
      destruct (store_cells_z_spec _ _ _ _ _ HinC) as (c & Hin & Hcase).
      destruct (obj_wf_cell _ _ _ Howf Hin) as (C1 & C2 & C3 & C4).
      pose proof (proj1 (Forall_forall _ _) Hcells c Hin) as Hch. pose proof Hch as (B1 & B2 & Brd).
      assert (DISJ : (A + k <= soff rho (c_off c) \/ soff rho (c_off c) + c_width c <= A) ->
                     cell_holds rho (ob_base o) (soff rho (ob_lo o)) (soff rho (ob_hi o)) ms' c).
      { intros HD. unfold cell_holds in *. rewrite Hrdu; [exact Hch | lia | lia | lia | lia]. }
      destruct Hcase as [[Hz ->] | [[Hcr ->] | [(d & Hcr & Ho & ->) | [(d & Hcr & Ho & Hdn & ->) | (d & Hcr & Ho & Hkd & ->)]]]].
      +
        pose proof (is_zero_lit_sound rho (c_val c) Hz) as Hcz.
        unfold cell_holds in Hch |- *. split; [exact B1|]. split; [exact B2|].
        assert (Hca : bv_unsigned (oaddr rho (ob_base o) (soff rho (c_off c))) = bv_unsigned (eval rho (ob_base o)) + soff rho (c_off c))
          by (apply oaddr_unsigned; lia).
        apply rd_bytes_of_nth; [apply enc_bytes_length | rewrite Hca, Z2Nat.id by lia; lia |].
        intros j Hj. rewrite Hca. rewrite enc_bytes_zero_nth; [| exact Hcz | exact Hj].
        destruct (Z_lt_le_dec (soff rho (c_off c) + Z.of_nat j) A) as [Hlt|Hge];
          [|destruct (Z_lt_le_dec (soff rho (c_off c) + Z.of_nat j) (A + k)) as [Hlt2|Hge2]].
        * rewrite (rd_unchanged ms ms'); [| rewrite <- Z.add_assoc; apply Hout; lia | exact Hr].
          pose proof (rd_bytes_nth ms (Z.to_nat (c_width c)) _ _ j Brd Hj ltac:(rewrite Hca, Z2Nat.id by lia; lia)) as R.
          rewrite Hca in R. rewrite R. rewrite enc_bytes_zero_nth; [reflexivity | exact Hcz | exact Hj].
        * rewrite <- Z.add_assoc. apply Hin0. lia.
        * rewrite (rd_unchanged ms ms'); [| rewrite <- Z.add_assoc; apply Hout; lia | exact Hr].
          pose proof (rd_bytes_nth ms (Z.to_nat (c_width c)) _ _ j Brd Hj ltac:(rewrite Hca, Z2Nat.id by lia; lia)) as R.
          rewrite Hca in R. rewrite R. rewrite enc_bytes_zero_nth; [reflexivity | exact Hcz | exact Hj].
      + apply DISJ. exact (cell_rel_disj_sound segs rho facts ms o off k c Hf Hoh Hin Hlo Hhi ltac:(lia) Hcr).
      + apply DISJ. pose proof (cell_rel_lit_sound segs rho facts ms o off k c d Hf Hoh Hin Hlo Hhi ltac:(lia) ltac:(lia) Hcr) as E.
        fold A in E. unfold lit_overlaps in Ho. apply Bool.andb_false_iff in Ho.
        destruct Ho as [Ho|Ho]; [apply Z.ltb_ge in Ho | apply Z.ltb_ge in Ho]; lia.
      +
        pose proof (cell_rel_lit_sound segs rho facts ms o off k c d Hf Hoh Hin Hlo Hhi ltac:(lia) ltac:(lia) Hcr) as E.
        fold A in E. unfold lit_overlaps in Ho. apply andb_prop in Ho as [HoA HoB]. apply Z.ltb_lt in HoA. apply Z.ltb_lt in HoB.
        unfold cell_holds. cbn [c_off c_width c_val]. split; [lia|]. split; [lia|].
        rewrite Hrdu by lia.
        rewrite (obj_read_cell segs rho ms o c (soff rho (c_off c)) (- d) Hoh Hin C2) by lia.
        rewrite Z.sub_diag, Z.mul_0_r, Z.shiftr_0_r, Z_to_bv_bv_unsigned. reflexivity.
      +
        pose proof (cell_rel_lit_sound segs rho facts ms o off k c d Hf Hoh Hin Hlo Hhi ltac:(lia) ltac:(lia) Hcr) as E.
        fold A in E. unfold lit_overlaps in Ho. apply andb_prop in Ho as [HoA HoB]. apply Z.ltb_lt in HoA. apply Z.ltb_lt in HoB.
        assert (Eo : soff rho (mk_addk off k) = A + k) by (unfold A; apply soff_mk_addk; lia).
        unfold cell_holds. cbn [c_off c_width c_val]. rewrite Eo. split; [lia|]. split; [lia|].
        rewrite Hrdu by lia.
        rewrite (obj_read_cell segs rho ms o c (A + k) (d + c_width c - k) Hoh Hin C2) by lia.
        f_equal. f_equal. apply bv_eq. rewrite mk_alu_sound.
        change (eval rho (SLit (8 * (k - d)))) with (Z_to_bv 64 (8 * (k - d))).
        rewrite srl_lit_unsigned by lia.
        rewrite Z_to_bv_unsigned. replace (A + k - soff rho (c_off c)) with (k - d) by lia. apply bv_wrap_small. rewrite two64.
        pose proof (urange (eval rho (c_val c))) as Hu. rewrite Z.shiftr_div_pow2 by lia.
        split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|].
        assert (1 <= 2 ^ (8 * (k - d))) by (apply Z.pow_le_mono_r with (a:=2) (b:=0); lia). nia. }
  split.
  2:{ destruct taint; [exact I |]. destruct (ob_dflt o); cbn in Hdl |- *; try exact Hdl; try exact I. discriminate Hna. }
  intros off' Hoff' Hcov.
  assert (Hnot : ~ (A <= off' < A + k)).
  { intros Hx. apply Hcov. unfold covered. apply Exists_cons_hd. unfold in_cell. cbn [c_off c_width]. fold A. lia. }
  pose proof (covered_cons rho _ _ _ Hcov) as Hcov'.
  destruct taint.
  -   cbn. apply Hrd'. exact Hoff'.
  -
    assert (Hold : ~ covered rho (ob_cells o) off').
    { intros Hc. apply Hcov'. unfold covered in Hc |- *. apply Exists_exists in Hc as (c & Hin & Hic).
      assert (Ht : snd (store_cells_z facts (ob_cells o) off k) = false) by (rewrite Esc; reflexivity).
      pose proof (store_cells_z_notaint facts (ob_cells o) off k c Ht Hin) as K. cbn zeta in K. rewrite Esc in K. cbn [fst] in K.
      pose proof (proj1 (Forall_forall _ _) Hcells c Hin) as (B1 & B2 & _).
      destruct (obj_wf_cell _ _ _ Howf Hin) as (C1 & C2 & C3 & C4).
      unfold in_cell in Hic. apply Exists_exists.
      destruct K as [[Hz HinK] | [[Hcr HinK] | (d & Hcr & [[Ho HinK] | (Ho & R1 & R2)])]].
      + exists c. split; [exact HinK | exact Hic].
      + exists c. split; [exact HinK | exact Hic].
      + exists c. split; [exact HinK | exact Hic].
      + pose proof (cell_rel_lit_sound segs rho facts ms o off k c d Hf Hoh Hin Hlo Hhi ltac:(lia) ltac:(lia) Hcr) as E.
        fold A in E. unfold lit_overlaps in Ho. apply andb_prop in Ho as [HoA HoB]. apply Z.ltb_lt in HoA. apply Z.ltb_lt in HoB.
        destruct (Z.lt_ge_cases off' A) as [Hlt|Hge].
        * exists (mkCell (c_off c) (- d) (c_val c)). split; [apply R1; lia|]. unfold in_cell. cbn [c_off c_width]. lia.
        * eexists. split; [apply R2; lia|]. unfold in_cell. cbn [c_off c_width].
          rewrite (soff_mk_addk rho off k) by (fold A; lia). fold A. lia. }
    specialize (Hd off' Hoff' Hold).
    destruct (ob_dflt o); cbn in Hd |- *.
    + destruct Hd as [b Hbb]. exists b. rewrite (rd_unchanged ms ms'); [exact Hbb | apply Hout; lia | exact Hr].
    + rewrite (rd_unchanged ms ms'); [exact Hd | apply Hout; lia | exact Hr].
    + destruct Hd as [Hnone Hib]. split; [|exact Hib]. rewrite Hout by lia. exact Hnone.
    + rewrite (rd_unchanged ms ms'); [exact Hd | apply Hout; lia | exact Hr].
    + rewrite (rd_unchanged ms ms'); [exact Hd | apply Hout; lia | exact Hr].
    + discriminate Hna.
Qed.

Lemma obj_range_store_z : ltac2:(tb__ "0|0|
S8S47S2A1S3S0S5eS0S57S45S5eS5eA2S33R6Sb3R5R4R3R2R1A5A2S33R6R4A2A3Fv;Fk;Foff;Fo;Ffacts;Frho;").
Proof using .
  intros. unfold obj_store_z. destruct (store_cells_z facts (ob_cells o) off k) as [cells' taint]. reflexivity.
Qed.

Lemma mem_match_store_z : ltac2:(tb__ "0|3|
S8S1S143S143S4dS3S0S5eS0S35Vsegs;R7A2S57S43S22R9A1S48A3S155S2S14RbA1S4RaA1A3S2dVsegs;RcS11RbA1RaA4S57S44S3A1S14cS3S11RcA1R9A3S46S3R8A2A3S57S43S15SeR9A1A1S48A3S57S43S16SeRaA1A1S49A3S111S32R10RbA2S21R10RaA2A2S111S110S21R11RbA2RaA2S31R11RcA2A2S116Z0M0RbA2S111RcZ8A2S57S5eS93Q40M1ScR14RcA2A2G0A3S57S92G1A1S44S92Q8A1A1F_;M2S145R12A1S145R13A1A3S57G2S144R13A1S146S144R14A1S30R16S1dR11A1S21R16R10A2A3S20S11cRfA1ScR16ReA2A2A3A3S2dVsegs;R17S6fS3S11R16A1R13S3Sb3S4R17A1R1R12R11R10A5Lo1;A4R14A4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fv;Fk;Foff;Fo;Fn;Fms';Fms;FS;Frho;").
Proof using .
  intros rho S ms ms' n o off k v Hrom Hwf Hf Hmm Hnth Hdw Hna Hlo Hhi Hk Hk8 Hv0 Hr Hm.
  rewrite (list_upd_is_set _ _ _ _ Hnth).
  pose proof (mem_match_nth segs _ _ _ _ _ Hmm Hnth) as Hoh.
  pose proof (swf_obj_nth _ _ _ Hwf Hnth) as Howf.
  destruct Hmm as (Hall & Hpd & Hfr).
  assert (Hlen : length (enc_bytes (Z.to_nat k) (eval rho v)) = Z.to_nat k) by apply enc_bytes_length.
  pose proof (proj1 Hoh) as HB. unfold obj_lo_of, obj_hi_of in *.
  assert (Ha : bv_unsigned (oaddr rho (ob_base o) (soff rho off)) = bv_unsigned (eval rho (ob_base o)) + soff rho off).
  { apply oaddr_unsigned. lia. }
  split; [|split].
  - apply Forall_forall. intros o2 Hin2.
    destruct (In_list_set _ _ _ _ Hin2) as [-> | (m & Hne & Hm2)].
    + eapply obj_holds_store_z; eauto.
    + eapply (obj_holds_frame segs rho (ss_next S)); [exact Hr | exact Hm | rewrite Ha, Hlen, Z2Nat.id by lia; lia | | eapply swf_obj_nth; eauto | ].
      * pose proof (SymSoundW.pairwise_disjoint_nth rho _ _ _ _ _ Hpd Hnth Hm2 ltac:(lia)) as D.
        unfold obj_range, obj_lo_of, obj_hi_of in D |- *. unfold ranges_disjoint in D |- *. cbn [fst snd] in D |- *.
        rewrite Ha, Hlen, Z2Nat.id by lia. lia.
      * exact (proj1 (Forall_forall _ _) Hall o2 (nth_error_In _ _ Hm2)).
  - eapply pairwise_disjoint_set; [exact Hnth | apply obj_range_store_z | exact Hpd].
  - intros a Ha'. apply (proj1 (outside_all_set rho (ss_objs S) n o (obj_store_z (ss_facts S) o off k v) a Hnth (obj_range_store_z _ _ _ _ _ _))) in Ha'.
    rewrite Hm. rewrite write_to_mem_out.
    + apply Hfr. exact Ha'.
    + rewrite Ha, Hlen, Z2Nat.id by lia. lia.
    + rewrite Ha, Hlen, Z2Nat.id by lia.
      pose proof (proj1 (Forall_forall _ _) Ha' o (nth_error_In _ _ Hnth)) as Ho. cbn in Ho.
      unfold obj_range, obj_lo_of, obj_hi_of in Ho. cbn [fst snd] in Ho. lia.
Qed.

Lemma obj_wf_store_z : ltac2:(tb__ "0|0|
S5fS47S2A1S3S0S5eS0S57S43S26R6R4A2S48A3S57S43SbR7R4A2S48A3S57S43SbR8R3A2S48A3S116Z0R5A2S111R6Z8A2S57S43S26RbSb3RaR9R8R7R6A5A2S48A3F_;F_;F_;F_;F_;Fv;Fk;Foff;Fo;Ffacts;Fn;").
Proof using .
  intros n facts o off k v Hwf Hoff Hv Hk Hk8.
  destruct (obj_wf_parts _ _ Hwf) as (Hb & Hlo & Hhi & Hcells).
  pose proof (obj_wf_dflt _ _ Hwf) as Hdwf.
  unfold obj_store_z. destruct (store_cells_z facts (ob_cells o) off k) as [cells' taint] eqn:Esc.
  unfold obj_wf. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt]. rewrite Hb, Hlo, Hhi. cbn [andb forallb].
  rewrite (ltac:(destruct taint; [reflexivity | exact Hdwf]) : dflt_wf n (if taint then DUnknown else ob_dflt o) = true).
  rewrite Bool.andb_true_r.
  apply andb_true_intro. split.
  - apply cell_wf_intro; cbn; auto.
  - apply forallb_forall. intros c' Hin'.
    assert (Hin0 : In c' (fst (store_cells_z facts (ob_cells o) off k))) by (rewrite Esc; exact Hin').
    destruct (store_cells_z_spec _ _ _ _ _ Hin0) as (c & Hin & Hcase).
    destruct (obj_wf_cell _ _ _ Hwf Hin) as (C1 & C2 & C3 & C4).
    destruct Hcase as [[Hz ->] | [[Hcr ->] | [(d & Hcr & Ho & ->) | [(d & Hcr & Ho & Hdn & ->) | (d & Hcr & Ho & Hkd & ->)]]]].
    + exact (proj1 (forallb_forall _ _) Hcells c Hin).
    + exact (proj1 (forallb_forall _ _) Hcells c Hin).
    + exact (proj1 (forallb_forall _ _) Hcells c Hin).
    + unfold lit_overlaps in Ho. apply andb_prop in Ho as [HoA HoB]. apply Z.ltb_lt in HoA. apply Z.ltb_lt in HoB.
      apply cell_wf_intro; cbn; auto; lia.
    + unfold lit_overlaps in Ho. apply andb_prop in Ho as [HoA HoB]. apply Z.ltb_lt in HoA. apply Z.ltb_lt in HoB.
      apply cell_wf_intro; cbn [c_off c_width c_val]; try lia.
      * apply mk_addk_below. exact Hoff.
      * apply mk_alu_below; [exact C4 | reflexivity].
Qed.

Lemma swf_store_z : ltac2:(tb__ "0|0|
S1S4dS3S0S5eS0S57S43S22R6A1S48A3S57S44S3A1S14cS3S11R7A1R6A3S46S3R5A2A3S57S43SbS9R8A1R5A2S48A3S57S43SbS9R9A1R4A2S48A3S116Z0R6A2S111R7Z8A2S57S43S22S6dRcS6fS3S11RcA1RbS3Sb3S4RdA1R1RaR9R8A5Lo1;A4A2A1S48A3F_;F_;F_;F_;F_;F_;Fv;Fk;Foff;Fo;Fn;FS;").
Proof using .
  intros S n o off k v Hwf Hnth Hoff Hv Hk Hk8.
  rewrite (list_upd_is_set _ _ _ _ Hnth).
  pose proof (swf_obj_nth _ _ _ Hwf Hnth) as Howf.
  unfold swf in Hwf |- *. unfold set_objs. cbn [ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next] in *.
  repeat (apply andb_prop in Hwf; destruct Hwf as [Hwf ?]).
  repeat (apply andb_true_intro; split); try assumption.
  apply forallb_list_set; [assumption|]. apply obj_wf_store_z; assumption.
Qed.

Lemma store_z_sound : ltac2:(tb__ "0|7|
S1S0S5eS0S4dS3S0S8S47S153A1M0S143S154S57S44S45S45S4dS3A2M1S0A2M2A1S7cS11RbA1S4RbA1RaR9U0A5S46G2S4bG1S0S4bS4dS3R7R6A4R5A4A2A3S57S43S15SeR7A1A1S48A3S57S43S16SeR8A1A1S49A3S12Vsegs;R7ReS4bG0S151R6S152R5R4A2A4A4S57S43SbS9RfA1ReA2S48A3S57S43SbS9R10A1RdA2S48A3S59S57S5eRfZ1A3S59S57S5eRfZ2A3S59S57S5eRfZ4A3S57S5eRfZ8A3A2A2A2S57S5eS93Q40M3ScRbRfA2A2Z0A3ScRcR12A2S92G3A1M4S20S11cR12A1ScRdR11A2A2S47S92Q8A1M5A1S6fS3S11R15A1R11S3Sb3S4R16A1R1R10R14R13A5Lo1;A4S47S3A1S58S57S43S148Vsegs;S144RdA1R3S11cR14A1A4S48A3S58S57S43S22S6dR16R1A2A1S48A3S143S57G4S44G5A1F_;M6S145R1A1S145ReA1A3S57G6S144R2A1S146S144RfA1R5R4A3A3S58S41Vsegs;R3A2S2dVsegs;R12R4R3A4A2F_;F_;Fms';A2A2Tobjs';Tbs;Ta;F_;F_;F_;F_;F_;F_;F_;F_;Fmd;Fms;Ftr;Frho;Foff;Fo;Fn;Fv;Fk;Fae;FS;").
Proof using .
  intros S ae k v n o off rho tr ms md Hfo Hdw Hna Hsm Hae Hv Hk Hv0.
  pose proof Hsm as Hsm0.
  destruct Hsm as (Hwf & Hpc & Hpend & Hhalt & Hrom & Hroc & Hregs & Hfregs & Hfcsr & Hresvm & Hmem & Hfacts).
  cbn [fst snd cfg_ms cfg_model] in *.
  destruct (k_cases k Hk) as (Hk0 & Hk8 & Hkn & Hw & Hwpos).
  assert (Hlen : length (enc_bytes (Z.to_nat k) (eval rho v)) = Z.to_nat k) by apply enc_bytes_length.
  destruct (find_obj_sound segs rho S tr ms md ae k n o off Hsm0 Hk0 Hfo)
    as (Hnth & Hoh & Howf & Hro & Hib & HU & Hea & Hlo & Hhi).
  pose proof (rel_offset_below (ss_next S) (ob_base o) ae off Hae (proj1 (obj_wf_parts _ _ Howf)) Hro) as Hoff.
  cbn zeta. rewrite Hea. split.
  { eapply obj_store_ok; eauto. }
  split.
  { eapply swf_store_z; eauto. }
  intros ms' Hr Hm. split.
  + eapply (ro_clear_store segs rho ms ms' o (soff rho off) k); eauto.
  + eapply mem_match_store_z; eauto.
Qed.

Lemma case_store_z : ltac2:(tb__ "0|4|
S1S124S92Q5A1M0G0S92QcA1S5eS4dS3S0S8S47S153A1M1S143S154S57S44S122A1S67Vsegs;S6RdA1A2S46S122S139RcRbRaR9A4A2A3S57S44S0A1S1eReA1S4cS0A1A3S57S0S63RfRcA2S5RaA1A3S57S5eS113RbS112Z2Z40A2A2Z0A3S57S44S45S45S4dS3A2M2S0A2M3A1S7cS11R11A1S4R11A1S6aS63R11RfA2S66RdA1A2S73R10A1U0A5S46G3S4bG2S0S4bS4dS3RbRaA4R9A4A2A3S57S43S15SeRbA1A1S48A3S57S43S16SeRcA1A1S49A3S12Vsegs;RbR14S4bG1S151RaS152R9R8A2A4A4S142Vsegs;R15S62S6dR15S6fS3S11R15A1RfS3Sb3S4R16A1R1ReS73R15A1S5R11A1A5Lo1;A4A2S110S6R15A1Z4A2A2RcRbRaR9A7F_;F_;F_;F_;F_;F_;F_;F_;Fmd;Fms;Ftr;Frho;Foff;Fo;Fn;Fz;Fimm;Frs2;Frs1;Fsz;FS;").
Proof using .
  intros S sz rs1 rs2 imm z n o off rho tr ms md Hi Hresv Hr2 Hz Hfo Hdw Hna Hsm.
  pose proof Hsm as Hsm0.
  destruct Hsm as (Hwf & Hpc & Hpend & Hhalt & Hrom & Hroc & Hregs & Hfregs & Hfcsr & Hresvm & Hmem & Hfacts).
  cbn [fst snd cfg_ms cfg_model] in *.
  assert (Hae : sv_below (ss_next S) (mk_addk (get_reg S rs1) (immI imm)) = true) by (apply mk_addk_below, get_reg_below; exact Hwf).
  assert (Hv : sv_below (ss_next S) (SLit z) = true) by reflexivity.
  assert (Hv0 : bv_unsigned (eval rho (SLit z)) = 0).
  { cbn [eval]. rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite two64. exact Hz. }
  destruct (store_z_sound S _ (msz sz) (SLit z) n o off rho tr ms md Hfo Hdw Hna Hsm0 Hae Hv (msz_cases sz) Hv0) as (Hok & Hwf' & Hpost).
  cbn zeta in Hok, Hpost.
  assert (Haddr : (rget (core_of ms) rs1 + sext 64 imm)%bv = eval rho (mk_addk (get_reg S rs1) (immI imm))).
  { rewrite (rget_match segs rho S tr ms md rs1 Hsm0). change (sext 64 imm) with (Z_to_bv 64 (immI imm)).
    rewrite <- mk_addk_sound. reflexivity. }
  assert (Hresv0 : ms_resv ms = None).
  { unfold resv_match in Hresvm. rewrite Hresv in Hresvm. destruct (ms_resv ms); [destruct Hresvm|reflexivity]. }
  set (a := eval rho (mk_addk (get_reg S rs1) (immI imm))) in *.
  set (bs := enc_bytes (Z.to_nat (msz sz)) (eval rho (SLit z))) in *.
  set (m' := write_to_mem (ms_mem ms) a bs).
  set (ms1 := ms_of ms (with_pc (Z_to_bv 64 (ss_pc S + 4)) (core_of ms)) m').
  destruct (Hpost ms1 eq_refl eq_refl) as [Hroc1 Hmem1].
  eapply next_rel_same_rho with (ms' := ms1).
  - rewrite (step_instr_at segs ms (ss_pc S) _ Hpc Hi ltac:(discriminate)).
    change (exec (Z_to_bv 64 4) (Store sz rs1 rs2 imm) (core_of ms))
      with (store_val sz (rget (core_of ms) rs1 + sext 64 imm)%bv (rget (core_of ms) rs2)
              (EDone (inval_resv (rget (core_of ms) rs1 + sext 64 imm)%bv
                        (with_pc (c_pc (core_of ms) + Z_to_bv 64 4)%bv (core_of ms))))).
    rewrite Haddr. rewrite (rget_match segs rho S tr ms md rs2 Hsm0). rewrite Hr2.
    assert (Hinv : inval_resv a (with_pc (c_pc (core_of ms) + Z_to_bv 64 4)%bv (core_of ms))
                   = with_pc (Z_to_bv 64 (ss_pc S + 4)) (core_of ms)).
    { unfold inval_resv, with_pc, with_resv, core_of. cbn. rewrite Hresv0.
      change (ms_pc_val ms) with (ms_pc ms). rewrite Hpc, pc_plus'. reflexivity. }
    destruct sz; cbn [store_val interp_eff0 width_bytes].
    + change (Z.to_nat (msz SZ1)) with 1%nat in Hok. rewrite Hok, Hinv.
      pose proof (store_bytes_enc SZ1 (eval rho (SLit z))) as E. cbn [msz msize_bytes] in E. rewrite E. reflexivity.
    + change (Z.to_nat (msz SZ2)) with 2%nat in Hok. rewrite Hok, Hinv.
      pose proof (store_bytes_enc SZ2 (eval rho (SLit z))) as E. cbn [msz msize_bytes] in E. rewrite E. reflexivity.
    + change (Z.to_nat (msz SZ4)) with 4%nat in Hok. rewrite Hok, Hinv.
      pose proof (store_bytes_enc SZ4 (eval rho (SLit z))) as E. cbn [msz msize_bytes] in E. rewrite E. reflexivity.
    + change (Z.to_nat (msz SZ8)) with 8%nat in Hok. rewrite Hok, Hinv.
      pose proof (store_bytes_enc SZ8 (eval rho (SLit z))) as E. cbn [msz msize_bytes] in E. rewrite E. reflexivity.
  - cbn. lia.
  - unfold smatch. cbn [fst snd cfg_ms cfg_model set_pc set_objs ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next].
    split; [rewrite swf_set_pc; exact Hwf' |].
    split; [reflexivity | split; [reflexivity | split; [exact Hhalt | split; [exact Hrom | split; [exact Hroc1|]]]]].
    split; [exact Hregs|]. split; [exact Hfregs|]. split; [exact Hfcsr|].
    split; [unfold resv_match; rewrite Hresv; cbn; rewrite Hresv0; exact I|].
    split; [exact Hmem1 | exact Hfacts].
Qed.

Lemma obj_holds_drop_zero_cell : ltac2:(tb__ "0|2|
S8S143S0S0S0S0S5eS5eS116Z0M0R2A2S57S5eS113R2S112Z2Z40A2A2G0A3S2bVsegs;RaR9S2aR8R7R6S4fS7S1cR5R4S5R3A1A3S52S7A1M1A3S2fA5A4S2bVsegs;RbRaS2aR9R8R7G1S2fA5A4F_;F_;F_;Fz;Fk;Foff;Fhi;Flo;Fbase;Fms;Frho;").
Proof using .
  intros rho ms base lo hi off k z Hk Hz (Hrng & Hw & Hcells & Hd & _).
  unfold obj_holds. unfold obj_lo_of, obj_hi_of in *. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt] in *.
  split; [exact Hrng|]. split; [exact Hw|]. split; [constructor|]. split; [|exact I].
  intros off0 Hoff0 _.
  inversion Hcells as [|c cs Hc _]; subst. destruct Hc as (Hc1 & Hc2 & Hrd). cbn [c_off c_width c_val] in Hc1, Hc2, Hrd.
  destruct (Z_lt_le_dec off0 (soff rho off)) as [Hlt|Hge]; [|destruct (Z_lt_le_dec off0 (soff rho off + k)) as [Hin|Hout]].
  - apply Hd; [exact Hoff0|]. intros HC. inversion HC as [c0 l0 Hin|c0 l0 Hin]; subst; [unfold in_cell in Hin; cbn in Hin; lia | inversion Hin].
  -
    unfold dflt_holds. set (j := Z.to_nat (off0 - soff rho off)).
    pose proof (rd_bytes_nth ms (Z.to_nat k) (oaddr rho base (soff rho off)) _ j Hrd ltac:(lia)) as R.
    unfold oaddr in R. rewrite Z_to_bv_unsigned in R. unfold bv_wrap in R. rewrite two64 in R.
    pose proof (urange (eval rho base)) as RB.
    rewrite (Z.mod_small (bv_unsigned (eval rho base) + soff rho off)) in R by lia.
    specialize (R ltac:(lia)).
    replace (bv_unsigned (eval rho base) + soff rho off + Z.of_nat j) with (bv_unsigned (eval rho base) + off0) in R by lia.
    rewrite R. f_equal. unfold enc_bytes. rewrite Z_to_le_bytes_nth by lia. cbn [eval].
    rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite two64, Hz, Z.shiftr_0_l. reflexivity.
  - apply Hd; [exact Hoff0|]. intros HC. inversion HC as [c0 l0 Hin2|c0 l0 Hin2]; subst; [unfold in_cell in Hin2; cbn in Hin2; lia | inversion Hin2].
Qed.

Lemma case_zst : ltac2:(tb__ "0|2|
S1S124S92Q5A1M0G0S92QcA1S61S8S47S153A1M1S143S154S57S44S122A1S67Vsegs;S6RaA1A2S46S122S139R9R8R7R6A4A2A3S57S44S61A1Se0RbRaR9R8R7A5S46S61R6A2A3S12Vsegs;R6RcS4bG1S151R5S152R4R3A2A4A4S61OLo;R8S1S142Vsegs;ReR1R8R7R6R5A7LS';S1S1S59S142Vsegs;RfR2R9R8R7R6A7S142Vsegs;RfR1R9R8R7R6A7A2LS2;LS1;S68S5aLr;X61x3F_;F_;F_;Fmd;Fms;Ftr;Frho;Fo;Fimm;Frs2;Frs1;Fsz;FS;").
Proof.
  intros S sz rs1 rs2 imm o rho tr ms md Hi H Hsm. unfold zst_step in H.
  destruct (ss_resv S) eqn:Hresv; [discriminate|].
  destruct (get_reg S rs2) as [z| | | | | | |] eqn:Hr2; try discriminate.
  destruct (z mod 2 ^ 64 =? 0) eqn:Hz; [|discriminate]. cbn [negb] in H. apply Z.eqb_eq in Hz.
  set (ae := mk_addk (get_reg S rs1) (immI imm)) in *.
  destruct (find_obj (ss_objs S) (ss_facts S) ae (msz sz) 0) as [[[n o1] off]|] eqn:Hfo; [|discriminate].

  assert (GEN : forall o', (if dflt_writable (ob_dflt o1) && negb (is_arr (ob_dflt o1)) && existsb (fun c => is_zero_lit (c_val c)) (ob_cells o1)
                     then Some (StNext (set_pc (set_objs S (list_upd (ss_objs S) n
                             (fun o2 => obj_store_z (ss_facts S) o2 off (msz sz) (SLit z)))) (ss_pc S + 4)))
                     else None) = Some o' ->
                match o' with
                | StNext S' => next_rel segs S S' rho tr ms md
                | StFork S1 S2 => next_rel segs S S1 rho tr ms md \/ next_rel segs S S2 rho tr ms md
                | StStop _ => True
                end).
  { intros o' Ho'. destruct (dflt_writable (ob_dflt o1)) eqn:Hdw; [|discriminate].
    destruct (is_arr (ob_dflt o1)) eqn:Hna; [discriminate|].
    destruct (existsb _ (ob_cells o1)); [|discriminate]. injection Ho' as <-.
    eapply case_store_z; eauto. }
  destruct (ob_cells o1) eqn:Hcells; [|exact (GEN o H)]. destruct (ob_dflt o1) eqn:Hdflt; try exact (GEN o H). clear GEN. injection H as <-.
  pose proof (smatch_swf segs _ _ _ Hsm) as Hwf.
  pose proof (msz_cases sz) as Hk. destruct (k_cases (msz sz) Hk) as (Hk0 & _).
  destruct (find_obj_sound segs rho S tr ms md ae (msz sz) n o1 off Hsm Hk0 Hfo) as (Hnth & _).

  assert (Hst : sym_store S ae (msz sz) (SLit z) = Some (set_objs S (list_upd (ss_objs S) n (fun o => obj_store_d (ss_facts S) o off (msz sz) (SLit z))))).
  { unfold sym_store. rewrite Hfo, Hdflt. reflexivity. }
  pose proof (case_store segs S sz rs1 rs2 imm) as CS. rewrite Hr2 in CS. fold ae in CS.
  specialize (CS _ rho tr ms md Hi Hresv Hst Hsm).
  destruct CS as (ms1 & rho' & STEP & Hag & Hle & Hsm1).
  exists ms1, rho'. split; [exact STEP|]. split; [exact Hag|]. split; [cbn; lia|].
  assert (Eo1 : obj_store_d (ss_facts S) o1 off (msz sz) (SLit z) = mkObj (ob_base o1) (ob_lo o1) (ob_hi o1) [mkCell off (msz sz) (SLit z)] DZero).
  { unfold obj_store_d. rewrite Hdflt. unfold obj_store. rewrite Hcells. cbn. rewrite Hdflt. reflexivity. }
  rewrite (list_upd_is_set _ _ _ _ Hnth), Eo1 in Hsm1.
  assert (Eo : o1 = mkObj (ob_base o1) (ob_lo o1) (ob_hi o1) [] DZero) by (destruct o1; cbn in *; subst; reflexivity).
  set (o0 := mkObj (ob_base o1) (ob_lo o1) (ob_hi o1) [mkCell off (msz sz) (SLit z)] DZero) in *.
  destruct Hsm1 as (Hwf1 & Hpc1 & Hpend1 & Hhalt1 & Hrom1 & Hroc1 & Hregs1 & Hfregs1 & Hfcsr1 & Hresv1 & (Hall1 & Hpd1 & Hfr1) & Hfacts1).
  cbn [fst snd cfg_ms cfg_model set_pc set_objs ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next] in *.
  assert (Hlen : (n < length (ss_objs S))%nat) by (eapply nth_error_lt; exact Hnth).
  destruct (Forall_list_set_inv _ _ _ _ Hall1 Hlen) as [Ho0 Hothers].
  assert (ER : obj_range rho' o1 = obj_range rho' o0) by (rewrite Eo; reflexivity).
  assert (OUTS : forall a, outside_all rho' (ss_objs S) a <-> outside_all rho' (list_set (ss_objs S) n o0) a).
  { intros a. unfold outside_all. split; intros HF; apply Forall_of_nth; intros i y Hy.
    - destruct (Nat.eq_dec i n) as [->|Hne].
      + rewrite (nth_error_list_set_same _ _ _ _ Hnth) in Hy. injection Hy as <-. cbn zeta. rewrite <- ER.
        exact (proj1 (Forall_forall _ _) HF o1 (nth_error_In _ _ Hnth)).
      + rewrite nth_error_list_set_other in Hy by exact Hne. exact (proj1 (Forall_forall _ _) HF y (nth_error_In _ _ Hy)).
    - destruct (Nat.eq_dec i n) as [->|Hne].
      + rewrite Hnth in Hy. injection Hy as <-. cbn zeta. rewrite ER.
        exact (proj1 (Forall_forall _ _) HF o0 (nth_error_In _ _ (nth_error_list_set_same _ _ _ _ Hnth))).
      + apply (proj1 (Forall_forall _ _) HF y). apply (nth_error_In _ i). rewrite nth_error_list_set_other by exact Hne. exact Hy. }
  unfold smatch. cbn [fst snd cfg_ms cfg_model set_pc ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next].
  split; [rewrite swf_set_pc; exact Hwf|].
  split; [exact Hpc1|]. split; [exact Hpend1|]. split; [exact Hhalt1|]. split; [exact Hrom1|]. split; [exact Hroc1|].
  split; [exact Hregs1|]. split; [exact Hfregs1|]. split; [exact Hfcsr1|]. split; [exact Hresv1|]. split; [|exact Hfacts1].
  split; [|split].
  - apply Forall_of_nth. intros i y Hy. destruct (Nat.eq_dec i n) as [->|Hne].
    + rewrite Hnth in Hy. injection Hy as <-. rewrite Eo. eapply obj_holds_drop_zero_cell; [exact Hk0 | exact Hz | exact Ho0].
    + eapply Hothers; [exact Hne | exact Hy].
  - pose proof (pairwise_disjoint_set rho' (list_set (ss_objs S) n o0) n o0 o1 (nth_error_list_set_same _ _ _ _ Hnth) ER Hpd1) as P.
    rewrite list_set_set, (list_set_same _ _ _ Hnth) in P. exact P.
  - intros a Ha. apply Hfr1. apply (proj1 (OUTS a)). exact Ha.
Qed.

Theorem sym_stepA_sound : ltac2:(tb__ "0|4|
Sa4S8S47S153A1M0S143S154S57S43S18Sa3R5A1A1S49A3S12Vsegs;R5Sa3R6A1S4bG0S151R4S152R3R2A2A4A4Sf2R6R7A2S57S43Sb4R8A1S48A3SadOLx;SdaVsegs;R9A2Sa4S142Vsegs;Sa3RaA1Sa3R1A1M1R9R8R7R6A7LA';Sa4Sa4S59S142Vsegs;Sa3RbA1M2Sa3R2A1RaR9R8R7A7S142Vsegs;G2G1RaR9R8R7A7A2LA2;LA1;M3G3S68S5aLr;Xadx4F_;F_;F_;F_;Fmd;Fms;Ftr;Frho;FA;").
Proof.
  intros A rho tr ms md Hlen Hsm Hsh Hwfx. unfold sym_stepA. rewrite Hlen.
  pose proof (sym_step_sound segs (ax_S A) rho tr ms md Hsm) as X.
  set (GOAL := fun o : step_out => match o with
                           | StNext S' => next_rel segs (ax_S A) S' rho tr ms md
                           | StFork S1 S2 => next_rel segs (ax_S A) S1 rho tr ms md \/ next_rel segs (ax_S A) S2 rho tr ms md
                           | StStop _ => True end).
  assert (LIFT : forall o, match o with
                           | StNext S' => step_rel segs (ax_S A) S' rho tr ms md
                           | StFork S1 S2 => next_rel segs (ax_S A) S1 rho tr ms md \/ next_rel segs (ax_S A) S2 rho tr ms md
                           | StStop _ => True end ->
                 match lift_out A o with
                 | StNextA A' => next_rel segs (ax_S A) (ax_S A') rho tr ms md
                 | StForkA A1 A2 | StJoinA A1 A2 => next_rel segs (ax_S A) (ax_S A1) rho tr ms md \/ next_rel segs (ax_S A) (ax_S A2) rho tr ms md
                 | StStopA _ => True end).
  { intros o Ho. destruct o; cbn; [exact (step_rel_strict segs _ _ _ _ _ _ Hlen Ho) | exact Ho | exact I]. }
  assert (LIFTG : forall o, GOAL o ->
                 match lift_out A o with
                 | StNextA A' => next_rel segs (ax_S A) (ax_S A') rho tr ms md
                 | StForkA A1 A2 | StJoinA A1 A2 => next_rel segs (ax_S A) (ax_S A1) rho tr ms md \/ next_rel segs (ax_S A) (ax_S A2) rho tr ms md
                 | StStopA _ => True end).
  { intros o Ho. destruct o; cbn; exact Ho. }
  assert (ORELSE : forall o d, (forall r, o = Some r -> GOAL r) ->
                   match d with
                   | StNext S' => step_rel segs (ax_S A) S' rho tr ms md
                   | StFork S1 S2 => next_rel segs (ax_S A) S1 rho tr ms md \/ next_rel segs (ax_S A) S2 rho tr ms md
                   | StStop _ => True end ->
                   match lift_out A (or_else o d) with
                   | StNextA A' => next_rel segs (ax_S A) (ax_S A') rho tr ms md
                   | StForkA A1 A2 | StJoinA A1 A2 => next_rel segs (ax_S A) (ax_S A1) rho tr ms md \/ next_rel segs (ax_S A) (ax_S A2) rho tr ms md
                   | StStopA _ => True end).
  { intros o d Ho Hd. destruct o as [r|]; cbn [or_else]; [apply LIFTG; apply Ho; reflexivity | apply LIFT; exact Hd]. }
  destruct (instr_at segs (ss_pc (ax_S A))) as [i|] eqn:Hi; [|apply LIFT; exact X].
  destruct i; try (apply LIFT; exact X).
  -   destruct sz;
      [ destruct (r3_step A signed rd rs1 imm) as [o|] eqn:Hr3; [|apply LIFT; exact X];
        pose proof (case_r3 segs A rho tr ms md Hsm Hsh Hwfx signed rd rs1 imm o Hi Hr3) as R3;
        destruct o; cbn; exact R3 | | |];
      (destruct (r3x_step A _ rd rs1 imm) as [o|] eqn:Hr3;
        [pose proof (case_r3x segs A rho tr ms md Hsm Hsh Hwfx _ signed rd rs1 imm o Hi Hr3) as R3; destruct o; cbn; exact R3|];
       destruct (r3w_step A _ rd rs1 imm) as [o|] eqn:Hr4; [|apply LIFT; exact X];
       pose proof (case_r3w segs A rho tr ms md Hsm Hsh _ signed rd rs1 imm o Hi Hr4) as R4;
       destruct o; cbn; exact R4).
  -   apply ORELSE; [|exact X]. intros r Hr. unfold GOAL. eapply case_zst; eauto.
  -   destruct op; try (apply LIFT; exact X).
    destruct (immI imm =? 7) eqn:Himm.
    { apply Z.eqb_eq in Himm.
      apply ORELSE; [|exact X]. intros r Hr. unfold r2_step in Hr.
      destruct (find_granule _ _ _) as [g|] eqn:Hfg; [|discriminate]. injection Hr as <-. unfold GOAL.
      eapply case_r2; eauto. }
    destruct (immI imm =? -8) eqn:Him8; [|apply LIFT; exact X]. apply Z.eqb_eq in Him8.
    apply ORELSE; [|exact X]. intros r Hr. unfold GOAL.
    destruct (andm8_sh_step A rd rs1) as [o|] eqn:Hsh8.
    + injection Hr as <-. eapply case_andm8_sh; eauto.
    + eapply case_andm8; eauto.
  -   destruct op; try (apply LIFT; exact X).
    destruct ((bv_unsigned shamt =? 3) &&& x_related (mk_prov (ss_facts (ax_S A))) (ss_facts (ax_S A)) (ax_X A) (get_reg (ax_S A) rs1)) eqn:Hsh3; [|apply LIFT; exact X].
    apply lazy_andb_prop in Hsh3 as [Hsh3 _]. apply Z.eqb_eq in Hsh3.
    apply ORELSE; [|exact X]. intros r Hr. unfold GOAL.
    pose proof (case_r1 segs _ _ _ _ r rho tr ms md Hi Hsh3 Hr Hsm) as R1. destruct r; [exact R1 | destruct R1 | destruct R1].
  -   apply ORELSE; [|exact X]. intros r Hr. unfold GOAL. eapply case_divpow2; eauto.
  -   unfold amo_step.
    destruct (amo_alignedb (ss_facts (ax_S A)) (get_reg (ax_S A) rs1) (amo_log w)) eqn:Hal; [|exact I]. cbn [negb].
    destruct (ss_resv (ax_S A)) eqn:Hr; [exact I|].
    destruct (sym_load segs (ax_S A) (get_reg (ax_S A) rs1) (amo_k w) true) as [v S1|] eqn:Hl; [|exact I].
    destruct (amo_sv op w v (get_reg (ax_S A) rs2)) as [nv|] eqn:Hnv; [|exact I].
    destruct (sym_store S1 (get_reg (ax_S A) rs1) (amo_k w) nv) as [S2|] eqn:Hs; [|exact I].
    cbn. eapply case_amo; eauto.
Qed.

End Sound.

Module StepAFast.

Definition force_u0 (ch : pcache) : pcache := ltac2:(tb__ "0|0|
S44S159A1S95Lx;S97Vch;A1S159Vch;Lu;Sa1Vch;S46S159S15aS9cVch;A1A1A2A2X44x2").
Lemma force_u0_ok : ltac2:(tb__ "0|1|
S95S47S2A1S96R2R1A2S58S96S16cR3A1M0R2A2S57S44S159A1S97G0A1S46S159S15aS7bR2A1A1A2A3A2F_;Ffacts;Fch;").
Proof.
  intros ch facts H. unfold force_u0. destruct (pc_u0 ch) as [u|] eqn:E.
  - split; [exact H|]. rewrite E. destruct (pc_u0_ok _ _ H) as [X|X]; rewrite E in X; [discriminate | exact X].
  - split; [apply set_u0_ok; [exact H | right; rewrite (pc_0_ok _ _ H); reflexivity] |].
    cbn [set_u0 pc_u0]. rewrite (pc_0_ok _ _ H). reflexivity.
Qed.
Lemma force_ud_some : ltac2:(tb__ "0|0|
S95S47S2A1S96R2R1A2S57S44S159A1S9dS99R3R2A2A1S46S159S15aS83R2A1A1A2A3F_;Ffacts;Fch;").
Proof.
  intros ch facts H. unfold force_ud. cbv zeta. pose proof (force_d_ok _ _ H) as H1.
  destruct (pc_ud (force_d ch facts)) as [u|] eqn:E.
  - rewrite E. destruct (pc_ud_ok _ _ H1) as [X|X]; rewrite E in X; [discriminate | exact X].
  - cbn [set_ud pc_ud]. rewrite (get_d_ok _ _ H1). reflexivity.
Qed.
Lemma pc_u0_force_d : ltac2:(tb__ "0|0|
S95S47S2A1S57S44S159A1S97S9fR2R1A2A1S97R2A1A3Ffacts;Fpc;").
Proof. intros pc facts. unfold force_d. destruct (pc_d pc); reflexivity. Qed.
Lemma pc_u0_force_ud : ltac2:(tb__ "0|0|
S95S47S2A1S57S44S159A1S97S99R2R1A2A1S97R2A1A3Ffacts;Fpc;").
Proof.
  intros pc facts. unfold force_ud. cbv zeta. destruct (pc_ud (force_d pc facts)); [apply pc_u0_force_d|].
  cbn [set_ud pc_u0]. apply pc_u0_force_d.
Qed.
Definition prov_c (ch : pcache) (facts : list sprop) : prov * pcache := ltac2:(tb__ "0|0|
S1c3Vch;Vfacts;A2S95S16cR1A1S95S99R1Vfacts;A2S95S4bSa6S95Sd5Vfacts;S9cR1A1Sa0R1Vfacts;A2S97R1A1S9dR1A1A5R1A4Tch3;Tch2;Tch1;").
Lemma prov_c_ok : ltac2:(tb__ "0|1|
S95S47S2A1S96R2R1A2S58S57Sa6S51Sa6S95S163R3R2A2M0A3SafR2A1A3S96S4eSa6S95G0A3R2A2A2F_;Ffacts;Fch;").
Proof.
  intros ch facts H. pose proof (DigFastA.force_d_f_ok ch facts H) as H1.
  destruct (force_u0_ok _ _ H1) as [H2 E2]. pose proof (force_ud_ok _ _ H2) as H3. pose proof (force_ud_some _ _ H2) as E3.
  unfold prov_c. cbn [fst snd]. split; [|exact H3].
  unfold mk_prov. rewrite (pc_0_ok _ _ H3), (get_d_ok _ _ H3), E3.
  rewrite pc_u0_force_ud, E2. reflexivity.
Qed.

Fixpoint facts_eqb (a b : list sprop) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => if sprop_eqb x y then facts_eqb a' b' else false
  | _, _ => false
  end.
Lemma facts_eqb_sound : ltac2:(tb__ "0|1|
S47S2A1M0G0S57S43S16bR2R1A2S48A3S57G0R3R2A3F_;Fb;Fa;").
Proof.
  induction a as [|x a IH]; intros [|y b] H; cbn in H; try discriminate; [reflexivity|].
  destruct (sprop_eqb x y) eqn:E; [|discriminate]. apply sprop_eqb_sound in E. subst y. rewrite (IH b H). reflexivity.
Qed.

Definition is_zero_lit_h (v : sv) : bool := ltac2:(tb__ "0|3|
S0S43Lv;Vv;S5eS115S85R1A1Z0A2Lz;S5fS49Li;S121S0S0S49Lb;La;M0Lop;M1G1S125G0Lop;M2G2S43S60S0S49La;Lw;Lsgn;S5fS0S5eS49Lk;Li;Ll;X0x8").
Lemma is_zero_lit_h_eq : ltac2:(tb__ "0|0|
S0S57S43S166R1A1SbaR1A1A3Fv;").
Proof. intros v. unfold is_zero_lit_h, is_zero_lit. destruct v; try reflexivity. rewrite zmod64_eq. reflexivity. Qed.

Fixpoint store_cells_z_c (pc : pcache) (facts : list sprop) (cells : list cell) (off : sv) (k : Z) : (list cell * bool) * pcache :=
  match cells with
  | [] => (([], false), pc)
  | c :: rest =>
      let '((rest', taint), pc1) := store_cells_z_c pc facts rest off k in
      let z := is_zero_lit_h (c_val c) in
      let '(r, pc2) := cell_rel_c pc1 facts off k c in
      (match r with
       | CLit d =>
           if lit_overlaps d (c_width c) k then
             let lo_keep := if d <? 0 then [mkCell (c_off c) (- d) (c_val c)] else [] in
             let hi_keep := if k <? d + c_width c
                            then [mkCell (mk_addk off k) (d + c_width c - k)
                                         (mk_alu ALU_SRL (c_val c) (SLit (8 * (k - d))))]
                            else [] in
             (lo_keep ++ hi_keep ++ (if z then c :: rest' else rest'), taint)
           else (c :: rest', taint)
       | CDisj => (c :: rest', taint)
       | CUnk => if z then (c :: rest', taint) else (rest', true)
       end, pc2)
  end.
Lemma store_cells_z_c_ok : ltac2:(tb__ "0|1|
S47S2A1S0S5eS47S7A1M0S95S96R1R5A2S9bS45G0S43A2R6S177R2R6R3R5R4A5Sc7R6R3R5R4A4A4F_;Fpc;Fcells;Fk;Foff;Ffacts;").
Proof.
  intros facts off k. induction cells as [|c rest IH]; intros pc H; cbn [store_cells_z_c store_cells_z].
  - apply cres_ret; exact H.
  - destruct (IH pc H) as (pc1 & -> & H1).
    destruct (store_cells_z facts rest off k) as [rest' taint].
    destruct (cell_rel_c_ok pc1 facts off k c H1) as (pc2 & -> & H2).
    rewrite is_zero_lit_h_eq. apply cres_ret; exact H2.
Qed.
Definition obj_store_z_c (pc : pcache) (facts : list sprop) (o : sobj) (off : sv) (k : Z) (v : sv) : sobj * pcache := ltac2:(tb__ "0|3|
S45S45S47S7A1M0S43A2M1S95A2S45S3S95A2M2Lx;S177Vpc;Vfacts;S17Vo;A1Voff;Vk;A5G1S95G1G2Lp;R2G0S43S4bS3S95S2aS1dVo;A1S25Vo;A1S24Vo;A1S4fS7S1cVoff;Vk;Vv;A3R2A3S43SfLtaint;R1S2eSeVo;A1X43x2A5R3A4Ltaint;Lcells';X45x1Lpc1;Lp;X45x1").
Lemma obj_store_z_c_ok : ltac2:(tb__ "0|0|
S95S47S2A1S3S0S5eS0S96R6R5A2S9bS3R6S164R7R6R5R4R3R2A6Sb3R6R5R4R3R2A5A4F_;Fv;Fk;Foff;Fo;Ffacts;Fpc;").
Proof.
  intros pc facts o off k v H. unfold obj_store_z_c, obj_store_z.
  destruct (store_cells_z_c_ok facts off k (ob_cells o) pc H) as (pc1 & -> & H1).
  destruct (store_cells_z facts (ob_cells o) off k) as [cells' taint]. apply cres_ret; exact H1.
Qed.
Definition zst_step_c (ch : pcache) (S : sstate) (sz : msize) (rs1 rs2 : reg) (imm : bv 12) : option step_out * pcache := ltac2:(tb__ "0|19|
S44S0A1S45S44S61A1M0S95A2M1Lx;S1eVS;A1S0S4bG0S95S4cS61A1M2Vch;A4M3Ls;S0G1Lx;S63VS;Vrs2;A2S5eS43G1L_;M4S50S115S85R1A1Z0A2A1G3S45S44S45S45S4dS3A2M5S0A2M6A1M7S95A2G1Lx;S9eVch;S11VS;A1M8S4VS;A1M9S6aS63VS;Vrs1;A2S66Vimm;A1A2S73Vsz;A1MaU0A6G7S95G7G1Lfo;R2G6G6G1Lp;R1G5S0G5G1Lp0;R2S4dS3S47S7A1MbG1Lx;S17R1A1McSfG1Lx;SeR1A1MdG4S4aS4aS15GdA1S50S16GdA1A1A2S160S7S7S166S19R1A1A1Lc;MeGcA3A2S45S3S95A2G1Lx;MfS164R6G9R1R3GaS5R8A1A6S3S95S4bG0S95S46S61S64S62S6dVS;S75S3G8R4R2A4A2S110S6VS;A1Z4A2M10A2A1A2R1A4Lch2;Lo';X45x1S4bG0S95G2R6A4X43x2M11S4bG0S95S46S61S64S62VS;G10A2A1A2R6A4G11S5fG4S4aS4aS15SeR2A1M12A1S50S16G12A1A1A2S160S7GeS17R2A1A3A2GfS164R7G9R2R4GaS5R9A1A6S3S95S4bG0S95S46S61S64S62S6dVS;S75S3G8R5R2A4A2G10A2A1A2R1A4Lch2;Lo';X45x1S4bG0S95G2R7A4X43x2Ll;M13G13S5eS0S47S45S5eS5eA2A1S47S28A1G4S4aS4aS15SeR5A1M14A1S50S16G14A1A1A2S160S7GeS17R5A1A3A2GfS164RaG9R5R7GaS5RcA1A6S3S95S4bG0S95S46S61S64S62S6dVS;S75S3G8R8R2A4A2G10A2A1A2R1A4Lch2;Lo';X45x1S4bG0S95G2RaA4X43x2Ltmpl;Lflds;Lcnt;Lesz;Xfx6S7GbG4S4aS4aS15SeR3A1M15A1S50S16G15A1A1A2S160S7GeS17R3A1A3A2GfS164R8G9R3R5GaS5RaA1A6S3S95S4bG0S95S46S61S64S62S6dVS;S75S3G8R6R2A4A2G10A2A1A2R1A4Lch2;Lo';X45x1S4bG0S95G2R8A4X43x2Ll;Lc;X47x2Lo;Ln;X45x1Loff;Lp0;X45x1Lp;S4bG0S95G2R1A4X44x2Lch1;Lfo;X45x1X43x2Lz;S5fG3Li;S121S0S0G3Lb;La;M16Lop;M17G17S125G16Lop;M18G18S43S60S0G3La;Lw;Lsgn;S5fS0S5eG3Lk;Li;Ll;X0x8X44x2").

Section RulesPV.
  Definition r1_step_pv (pv : prov) (S : sstate) (rd rs1 : reg) : option step_out := ltac2:(tb__ "0|d|
S6VS;A1S5eS4VS;A1S47S2A1S63VS;Vrs1;A2S0S43S44S61A1M0L_;M1S71R1A1S4cS61A1S45S0S5eA2G0Lx;Sd8R1A1S0S5eG1S43S43L_;S4aS4aS117Z0M2R1A2S11aR1S112Z2M3Z28A2A2A2S117Z3S69R4R2A2A2A2Sa7Vpv;R2R1S5S118S112G3Z40A2Z1A2A1A4S49X43x2S5fS43S0L_;S115S119R2Z8A2M4G2A2SdR1A1M5SaS123G5S5G4A1A3X43x2Lg;S5fS0Fg;S44S5fA1G0Lx;M6ScfVpv;R5R3A3S5fS46S61S64S62S65VS;Vrd;R2R1A1M7A3S110R7Z4M8A2M9A2A1A2Lg;S9VS;A1MaS5fS46S61S64S62S65S15fScaR1R4A2S4eS0S1S6bVS;A1A3MbA2Vrd;G7A3G9A2A1A2Tg;X44x2Tmk;G6Sb6Vpv;R4R3A3S5fS46S61S64S62S65VS;Vrd;G5A3S110R6G8A2McA2A1A2Lg;GaS5fS46S61S64S62S65S15fSc9R1R4A2GbA2Vrd;G5A3GcA2A1A2Tg;X44x2X43x2Lc;Le0;X45x1X43x2Te;Tfacts;Tpc;").

  Definition r2_step_pv (pv : prov) (S : sstate) (rd rs1 : reg) : option step_out := ltac2:(tb__ "0|0|
S6VS;A1S5eS63VS;Vrs1;A2S0S44S5fA1S44S61A1Lx;Sb6Vpv;S4VS;A1R1A3S5fS46S61S64S62S65VS;Vrd;SaS12eR2SabR1A1A3A3S110R3Z4A2A2A1A2Lg;S4cS61A1X44x2Te;Tpc;").

  Definition andm8_step_pv (pv : prov) (A : axst) (rd rs1 : reg) (imm : bv 12) : option step_out := ltac2:(tb__ "0|4|
Sa3VA;A1S1S63R1Vrs1;A2S0S43S44S61A1L_;M0S54S71R1A1S115S93Q5Vrd;A2Z0A2A2S4cS61A1M1G0Sa7Vpv;R1Z7M2S5S118S112Z2Z40A2M3Z1A2A1A4S84S4R2A1S12aR1S5S113S66Vimm;A1G3A2A1A4S0S46S61S64S15fS55S2S4fS2S10R1R2A2S4fS2S10R2SaS123R1S5G2A1A3A2S52S2A1A3A3SdcVpv;SaaVA;A1R2R1A4A3S62S65R3Vrd;R1A3S110S6R3A1Z4A2A2A2A1A2Tv;G1X43x2X43x2Te;TS;").

  Definition r3_step_pv (pv : prov) (A : axst) (sgn : bool) (rd rs1 : reg) (imm : bv 12) : option step_out := ltac2:(tb__ "0|b|
Sa3VA;A1S1S6aS63R1Vrs1;A2S66Vimm;A1A2S0S44S0A1S44S61A1M0Lx;S6eSa9VA;A1R1A2S0S44Sa5A1G0Lx;Sb2Vpv;R1A2Sa5Sa5G0Lg0;R1S0S44S45S0S0A2M1A1G0Lx;M2Sb7Vpv;SaaVA;A1M3R1Z0M4A4M5G1G1G0Lp;M6R1S0S0S46S61Sc2R8Vrd;Sa7Vpv;R4Z8M7SaS123R2R1A3M8A4R4R2R1A6A2Ll;Lb;X45x1Lp;S4cS61A1M9X44x2Lq8;S5fS0G2G5G1G6R1S0S0S46S61Sc2R9Vrd;Sa7Vpv;SabR5A1MaG7G8A4GaR2R1A6A2Ll;Lb;X45x1Lp;G9X44x2Le;Lg;S5fS0S5eG2Sb7Vpv;G3R2S114G7R1A2A4G1G6R1S0S0S43G0L_;Sa7Vpv;SabR6A1S110S114G7R4A2G7A2G8A4S46S61S64S62S65RaVrd;S5G4A1A3S110S6RaA1Z4A2A2A1A2G9X43x2Ll;Lb;X45x1Lp;G9X44x2Lk;Le;Lg;Xa5x3Lg0;G9X44x2Loff;G9X44x2Tae;TS;").

  Definition r3x_step_pv (pv : prov) (A : axst) (sz : msize) (rd rs1 : reg) (imm : bv 12) : option step_out := ltac2:(tb__ "0|3|
Sa3VA;A1S1S6aS63R1Vrs1;A2S66Vimm;A1A2S0S44S0A1S44S61A1M0Lx;S6eSa9VA;A1R1A2S0S44Sa5A1G0Lx;Sb2Vpv;R1A2Sa5Sc0R1A1S0S44S45S0S0A2M1A1G0Lx;Sd0Vpv;SaaVA;A1R2A3G1G1G0Lp;R1S0S0S43G0L_;Sa7Vpv;R4S114Z8S73Vsz;A1A2SaS123R2R1A3A4S46S61S64S62S65R8Vrd;S5Z0A1A3S110S6R8A1Z4A2A2A1A2S4cS61A1M2X43x2Ll;Lb;X45x1Lp;G2X44x2Tq8;Ld;G2X44x2Loff;G2X44x2Tae;TS;").

  Definition r3w_step_pv (pv : prov) (A : axst) (sz : msize) (rd rs1 : reg) (imm : bv 12) : option step_out := ltac2:(tb__ "0|7|
Sa3VA;A1S1S124S44S61A1M0Lsz;Vsz;S4cS61A1M1G1G1S44S0A1G0Lx;Sd7VA;S6aS63R1Vrs1;A2S66Vimm;A1A2A2S0S43G0L_;M2S50SbS9R2A1R1A2A1G1S44Sa5A1G0Lx;Sb2Vpv;R1A2Sa5S44S45S0S0A2M3A1G0Lx;M4Sd0Vpv;SaaVA;A1R1A3G3G3G0Lp;R1S0S0G2S43S43L_;Se5VA;A1S103Vpv;R2R1R4A4S49X43x2S46S61S64S62S65R6Vrd;S5Z0A1A3S110S6R6A1Z4M5A2M6A2A1A2S46S61S64S62S65S4eS0S1S6bR6A1A3Vrd;SdS9R6A1A1A3G6A2A1A2X43x2Ll;Lb;X45x1Lp;G4S10bVA;R2A2G3S46S61S64S62S65S4eS0S1S6bR4A1A3Vrd;SdS9R4A1A1A3S110S6R4A1G5A2A2A1A2Lp;G1X44x2X44x2Ld;G1X44x2X43x2Lt;G1X44x2X124x4TS;").
End RulesPV.

Lemma r1_step_pv_eq : ltac2:(tb__ "0|1|
S1S92Q5A1M0G0S57S44S61A1S16eSafS4R3A1A1R3R2R1A4Sc1R3R2R1A3A3Frs1;Frd;FS;").
Proof. reflexivity. Qed.
Lemma r2_step_pv_eq : ltac2:(tb__ "0|1|
S1S92Q5A1M0G0S57S44S61A1S170SafS4R3A1A1R3R2R1A4Sd6R3R2R1A3A3Frs1;Frd;FS;").
Proof. reflexivity. Qed.
Lemma andm8_step_pv_eq : ltac2:(tb__ "0|1|
Sa4S92Q5A1M0G0S92QcA1S57S44S61A1S16aSafS4Sa3R4A1A1A1R4R3R2R1A5SbdR4R3R2R1A4A3Fimm;Frs1;Frd;FA;").
Proof. reflexivity. Qed.
Lemma r3_step_pv_eq : ltac2:(tb__ "0|1|
Sa4S43S92Q5A1M0G0S92QcA1S57S44S61A1S172SafS4Sa3R5A1A1A1R5R4R3R2R1A6Sc3R5R4R3R2R1A5A3Fimm;Frs1;Frd;Fsgn;FA;").
Proof. reflexivity. Qed.
Lemma r3x_step_pv_eq : ltac2:(tb__ "0|1|
Sa4S124S92Q5A1M0G0S92QcA1S57S44S61A1S176SafS4Sa3R5A1A1A1R5R4R3R2R1A6Sc5R5R4R3R2R1A5A3Fimm;Frs1;Frd;Fsz;FA;").
Proof. reflexivity. Qed.
Lemma r3w_step_pv_eq : ltac2:(tb__ "0|1|
Sa4S124S92Q5A1M0G0S92QcA1S57S44S61A1S174SafS4Sa3R5A1A1A1R5R4R3R2R1A6Sc4R5R4R3R2R1A5A3Fimm;Frs1;Frd;Fsz;FA;").
Proof. reflexivity. Qed.

Definition rres {T} (facts : list sprop) (r : T * pcache) (orig : T) : Prop := fst r = orig /\ pc_ok (snd r) facts.

Lemma existsb_ext_zl : ltac2:(tb__ "0|1|
S47S7A1S57S43S14bS7S7S166S19R1A1M0A1Lc;R1A3S14bS7S7SbaG0A1Lc;R1A3A3Fl;").
Proof. induction l as [|c l IH]; cbn [existsb]; [reflexivity|]. rewrite is_zero_lit_h_eq, IH. reflexivity. Qed.
Lemma zst_step_c_ok : ltac2:(tb__ "0|1|
S95S1S124S92Q5A1M0G0S92QcA1S96R6S4R5A1A2S162S44S61A1S4R6A1S178R7R6R5R4R3R2A6Se0R6R5R4R3R2A5A4F_;Fimm;Frs2;Frs1;Fsz;FS;Fch;").
Proof.
  intros ch S sz rs1 rs2 imm H. unfold zst_step_c, zst_step.
  destruct (ss_resv S); [split; [reflexivity | exact H]|].
  destruct (get_reg S rs2); try (split; [reflexivity | exact H]).
  rewrite zmod64_eq. destruct (negb (z mod 2 ^ 64 =? 0)); [split; [reflexivity | exact H]|].
  destruct (find_obj_c_ok ch (ss_objs S) (ss_facts S) (mk_addk (get_reg S rs1) (immI imm)) (msz sz) 0 H) as (ch1 & E1 & H1).
  rewrite E1.
  destruct (find_obj (ss_objs S) (ss_facts S) (mk_addk (get_reg S rs1) (immI imm)) (msz sz) 0) as [[[n o] off]|] eqn:EF;
    [|split; [reflexivity | exact H1]].
  destruct (ob_cells o) as [|c0 cs] eqn:EC.
  - destruct (ob_dflt o) eqn:ED; try (split; [reflexivity | exact H1]).
    all: rewrite existsb_lazy_eq; cbn [existsb map]; rewrite ?Bool.andb_false_r; try (split; [reflexivity | exact H1]).
  - rewrite existsb_lazy_eq.
    rewrite existsb_ext_zl.
    destruct (ob_dflt o) eqn:ED;
    (destruct (dflt_writable _ && negb (is_arr _) && existsb (fun c : cell => is_zero_lit (c_val c)) (c0 :: cs));
       [|split; [reflexivity | exact H1]];
     destruct (obj_store_z_c_ok ch1 (ss_facts S) o off (msz sz) (SLit z) H1) as (ch2 & E2 & H2);
     rewrite E2;
     rewrite (list_upd_set _ _ (fun o1 => obj_store_z (ss_facts S) o1 off (msz sz) (SLit z)) _ (find_obj_nth _ _ _ _ _ _ _ EF));
     split; [reflexivity | exact H2]).
Qed.

Definition r2_step_c (ch : pcache) (S : sstate) (rd rs1 : reg) : option step_out * pcache := ltac2:(tb__ "0|1|
S45Sa6S95A2S45S44S61A1M0S95A2Lx;S163Vch;S4VS;A1A2Sa6S95S4bG0S95S170R2VS;Vrd;Vrs1;A4R1A4Lch';Lpv;X45x1").
Lemma r2_step_c_ok : ltac2:(tb__ "0|1|
S95S1S92Q5A1M0G0S96R4S4R3A1A2S162S44S61A1S4R4A1S16fR5R4R3R2A4Sd6R4R3R2A3A4F_;Frs1;Frd;FS;Fch;").
Proof.
  intros ch S rd rs1 H. unfold r2_step_c. destruct (prov_c_ok ch _ H) as [E H']. destruct (prov_c ch (ss_facts S)) as [pv ch'].
  cbn [fst snd] in *. subst pv. split; [apply r2_step_pv_eq | exact H'].
Qed.

Definition r1_step_c (ch : pcache) (S : sstate) (rd rs1 : reg) : option step_out * pcache := ltac2:(tb__ "0|2|
S43S45S44S61A1M0S95A2M1L_;S71S63VS;Vrs1;A2A1S4bG0S95S4cS61A1Vch;A4S45Sa6S95A2G1Lx;S163Vch;S4VS;A1A2Sa6S95S4bG0S95S16eR2VS;Vrd;Vrs1;A4R1A4Lch';Lpv;X45x1X43x2").
Lemma r1_step_c_ok : ltac2:(tb__ "0|1|
S95S1S92Q5A1M0G0S96R4S4R3A1A2S162S44S61A1S4R4A1S16dR5R4R3R2A4Sc1R4R3R2A3A4F_;Frs1;Frd;FS;Fch;").
Proof.
  intros ch S rd rs1 H. unfold r1_step_c. destruct (is_lit (get_reg S rs1)) eqn:EL.
  - split; [|exact H]. cbn [fst]. unfold r1_step. cbv zeta. rewrite EL. reflexivity.
  - destruct (prov_c_ok ch _ H) as [E H']. destruct (prov_c ch (ss_facts S)) as [pv ch']. cbn [fst snd] in *. subst pv.
    split; [apply r1_step_pv_eq | exact H'].
Qed.

Definition andm8_step_c (ch : pcache) (A : axst) (rd rs1 : reg) (imm : bv 12) : option step_out * pcache := ltac2:(tb__ "0|3|
S43S45S44S61A1M0S95A2M1L_;S54S71S63Sa3VA;A1M2Vrs1;A2A1S115S93Q5Vrd;A2Z0A2A2S4bG0S95S4cS61A1Vch;A4S45Sa6S95A2G1Lx;S163Vch;S4G2A1A2Sa6S95S4bG0S95S16aR2VA;Vrd;Vrs1;Vimm;A5R1A4Lch';Lpv;X45x1X43x2").
Lemma andm8_step_c_ok : ltac2:(tb__ "0|1|
S95Sa4S92Q5A1M0G0S92QcA1S96R5S4Sa3R4A1A1A2S162S44S61A1S4Sa3R5A1A1S169R6R5R4R3R2A5SbdR5R4R3R2A4A4F_;Fimm;Frs1;Frd;FA;Fch;").
Proof.
  intros ch A rd rs1 imm H. unfold andm8_step_c. destruct (is_lit (get_reg (ax_S A) rs1) || (bv_unsigned rd =? 0)) eqn:EL.
  - split; [|exact H]. cbn [fst]. unfold andm8_step. cbv zeta. rewrite EL. reflexivity.
  - destruct (prov_c_ok ch _ H) as [E H']. destruct (prov_c ch (ss_facts (ax_S A))) as [pv ch']. cbn [fst snd] in *. subst pv.
    split; [apply andm8_step_pv_eq | exact H'].
Qed.

Definition granule_pre (off : sv) : bool := ltac2:(tb__ "0|2|
S44SaeA1S43Lx;Sc6Voff;A1SaeSaeS43Lg0;R1S5fS5eS4aS117Z0R1A2M0S11aR1S112Z2M1Z28A2A2A2Lk;Lg;S5eS4aG0S11aR1S112G1Z3dA2A2A2Lq;Xaex2Lg0;S49X44x2").
Lemma granule_pre_false : ltac2:(tb__ "0|0|
Sa6S0S57S43S165R1A1S49A3S57S44Sa5A1Sb2R3R2A2S4cSa5A1A3F_;Foff;Fpv;").
Proof. intros pv off H. unfold granule_pre in H. unfold granule_of. destruct (split_gk off) as [[g k|q]|]; [| |reflexivity]; rewrite H; reflexivity. Qed.

Definition r3_step_c (ch : pcache) (A : axst) (sgn : bool) (rd rs1 : reg) (imm : bv 12) : option step_out * pcache := ltac2:(tb__ "0|4|
S44S0A1S45S44S61A1M0S95A2M1Lx;S6eSa9VA;A1S6aS63Sa3VA;A1M2Vrs1;A2S66Vimm;A1A2A2S0S43G1L_;S165R1A1S45Sa6S95A2G1Lx;S163Vch;S4G2A1A2Sa6S95S4bG0S95S172R2VA;Vsgn;Vrd;Vrs1;Vimm;A6R1A4Lch';Lpv;X45x1S4bG0S95S4cS61A1Vch;A4M3X43x2Loff;G3X44x2").
Lemma r3_step_c_ok : ltac2:(tb__ "0|1|
S95Sa4S43S92Q5A1M0G0S92QcA1S96R6S4Sa3R5A1A1A2S162S44S61A1S4Sa3R6A1A1S171R7R6R5R4R3R2A6Sc3R6R5R4R3R2A5A4F_;Fimm;Frs1;Frd;Fsgn;FA;Fch;").
Proof.
  intros ch A sgn rd rs1 imm H. unfold r3_step_c. destruct (rel_offset (ax_base A) (mk_addk (get_reg (ax_S A) rs1) (immI imm))) as [off|] eqn:EL.
  - destruct (granule_pre off) eqn:GP.
    + destruct (prov_c_ok ch _ H) as [E H']. destruct (prov_c ch (ss_facts (ax_S A))) as [pv ch']. cbn [fst snd] in *. subst pv.
      split; [apply r3_step_pv_eq | exact H'].
    + split; [|exact H]. cbn [fst]. rewrite <- r3_step_pv_eq. unfold r3_step_pv. cbv zeta. rewrite EL, (granule_pre_false _ _ GP). reflexivity.
  - split; [|exact H]. cbn [fst]. unfold r3_step. cbv zeta. rewrite EL. reflexivity.
Qed.

Definition r3x_step_c (ch : pcache) (A : axst) (sz : msize) (rd rs1 : reg) (imm : bv 12) : option step_out * pcache := ltac2:(tb__ "0|4|
S44S0A1S45S44S61A1M0S95A2M1Lx;S6eSa9VA;A1S6aS63Sa3VA;A1M2Vrs1;A2S66Vimm;A1A2A2S0S43G1L_;S165R1A1S45Sa6S95A2G1Lx;S163Vch;S4G2A1A2Sa6S95S4bG0S95S176R2VA;Vsz;Vrd;Vrs1;Vimm;A6R1A4Lch';Lpv;X45x1S4bG0S95S4cS61A1Vch;A4M3X43x2Loff;G3X44x2").
Lemma r3x_step_c_ok : ltac2:(tb__ "0|1|
S95Sa4S124S92Q5A1M0G0S92QcA1S96R6S4Sa3R5A1A1A2S162S44S61A1S4Sa3R6A1A1S175R7R6R5R4R3R2A6Sc5R6R5R4R3R2A5A4F_;Fimm;Frs1;Frd;Fsz;FA;Fch;").
Proof.
  intros ch A sz rd rs1 imm H. unfold r3x_step_c. destruct (rel_offset (ax_base A) (mk_addk (get_reg (ax_S A) rs1) (immI imm))) as [off|] eqn:EL.
  - destruct (granule_pre off) eqn:GP.
    + destruct (prov_c_ok ch _ H) as [E H']. destruct (prov_c ch (ss_facts (ax_S A))) as [pv ch']. cbn [fst snd] in *. subst pv.
      split; [apply r3x_step_pv_eq | exact H'].
    + split; [|exact H]. cbn [fst]. rewrite <- r3x_step_pv_eq. unfold r3x_step_pv. cbv zeta. rewrite EL, (granule_pre_false _ _ GP). reflexivity.
  - split; [|exact H]. cbn [fst]. unfold r3x_step. cbv zeta. rewrite EL. reflexivity.
Qed.

Definition r3w_step_c (ch : pcache) (A : axst) (sz : msize) (rd rs1 : reg) (imm : bv 12) : option step_out * pcache := ltac2:(tb__ "0|4|
S124S45S44S61A1M0S95A2M1Lsz;Vsz;S4bG0S95S4cS61A1Vch;A4M2G2G2S44S0A1G1Lx;Sd7VA;S6aS63Sa3VA;A1M3Vrs1;A2S66Vimm;A1A2A2S0S43G1L_;S165R1A1S45Sa6S95A2G1Lx;S163Vch;S4G3A1A2Sa6S95S4bG0S95S174R2VA;Vsz;Vrd;Vrs1;Vimm;A6R1A4Lch';Lpv;X45x1G2X43x2Lt;G2X44x2X124x4").
Lemma r3w_step_c_ok : ltac2:(tb__ "0|1|
S95Sa4S124S92Q5A1M0G0S92QcA1S96R6S4Sa3R5A1A1A2S162S44S61A1S4Sa3R6A1A1S173R7R6R5R4R3R2A6Sc4R6R5R4R3R2A5A4F_;Fimm;Frs1;Frd;Fsz;FA;Fch;").
Proof.
  intros ch A sz rd rs1 imm H. unfold r3w_step_c.
  destruct sz; try (split; [reflexivity | exact H]).
  destruct (r3w_target A (mk_addk (get_reg (ax_S A) rs1) (immI imm))) as [t|] eqn:EL.
  - destruct (granule_pre t) eqn:GP.
    + destruct (prov_c_ok ch _ H) as [E H']. destruct (prov_c ch (ss_facts (ax_S A))) as [pv ch']. cbn [fst snd] in *. subst pv.
      split; [apply r3w_step_pv_eq | exact H'].
    + split; [|exact H]. cbn [fst]. rewrite <- r3w_step_pv_eq. unfold r3w_step_pv. cbv zeta. rewrite EL, (granule_pre_false _ _ GP).
      destruct (negb (sv_below (ss_next (ax_S A)) t)); reflexivity.
  - split; [|exact H]. cbn [fst]. unfold r3w_step. cbv zeta. rewrite EL. reflexivity.
Qed.

Definition stepA_ok (ch' : pcache) (o : step_outA) : Prop := ltac2:(tb__ "0|1|
SadOLo;Vo;Sa4S96Vch';S4Sa3R1A1A1A2LA';Sa4Sa4S5aLA2;LA1;M0G0S68S5aLr;Xadx4").

Definition rekey (ch : pcache) (facts : list sprop) (o : step_out) : pcache := ltac2:(tb__ "0|1|
S61S95Lo;Vo;S1S43S95L_;S16bS4R1A1M0Vfacts;A2Vch;S98G0A1X43x2LS';S1S1Vch;LS2;LS1;S68Vch;Lr;X61x3").
Lemma rekey_ok : ltac2:(tb__ "0|0|
S95S47S2A1S61S96R3R2A2S9aS167R4R3R2A3R2A2F_;Fo;Ffacts;Fch;").
Proof.
  intros ch facts [S'|S1 S2|r] H; cbn [rekey step_ok]; try exact I.
  destruct (facts_eqb (ss_facts S') facts) eqn:E; [|apply pc_init_ok]. apply facts_eqb_sound in E. rewrite E. exact H.
Qed.
Lemma lift_out_ok : ltac2:(tb__ "0|0|
Sa4S61S95S9aR1R2A2S168R2SacR4R3A2A2F_;Fch;Fo;FA;").
Proof. intros A [S'|S1 S2|r] ch H; cbn in *; auto. Qed.
Lemma lift_out_j_ok : ltac2:(tb__ "0|0|
Sa4S61S95S9aR1R2A2S168R2SbfR4R3A2A2F_;Fch;Fo;FA;").
Proof. intros A [S'|S1 S2|r] ch H; cbn in *; auto. Qed.

Section WithImage.
  Variable segs : list Segment.

  Definition x_related_l (pv : prov) (facts : list sprop) (X : list (sv * sv)) (e : sv) : bool := ltac2:(tb__ "0|1|
S160S45S0S0A2M0G0Sa7Vpv;S51S0S0R1A3Z0Ve;A4Lr;VX;A3").
  Lemma x_related_l_eq : ltac2:(tb__ "0|0|
Sa6S47S2A1S47S45S0S0A2A1S0S57S43S181R4R3R2R1A4S10fR4R3R2R1A4A3Fe;FX;Ffacts;Fpv;").
  Proof. intros. unfold x_related_l, x_related. apply existsb_lazy_eq. Qed.
  Definition dflt_c (ch : pcache) (A : axst) : step_outA * pcache := ltac2:(tb__ "0|0|
S45S61S95A2S45SadS95A2Lx;Sa2Vsegs;Vch;Sa3VA;A1A3S61S95S4bSadS95SacVA;R2A2R1A4Lch';Lo;X45x1").
  Definition ruleA (ch : pcache) (A : axst) (o : step_out) : step_outA * pcache := ltac2:(tb__ "0|0|
S4bSadS95SacVA;Vo;A2S167Vch;S4Sa3VA;A1A1Vo;A3A4").
  Definition or_else_c (r : option step_out * pcache) (A : axst) : step_outA * pcache := ltac2:(tb__ "0|2|
S44S61A1M0S45SadS95A2Lx;S51G0S95Vr;A3S61S17cS4eG0S95Vr;A3M1VA;R1A3Lo;S17bG1VA;A2X44x2").

  Definition sres (r : step_outA * pcache) (orig : step_outA) : Prop := ltac2:(tb__ "0|0|
S5bS95S95S58S57S45SadS95A2Vr;S4bSadS95Vorig;R1A4A3S168R1Vorig;A2A2Lch';A2").

  Lemma dflt_c_ok : ltac2:(tb__ "0|0|
S95Sa4S96R2S4Sa3R1A1A1A2S17dS17bR3R2A2SacR2S6cVsegs;Sa3R2A1A2A2A2F_;FA;Fch;").
  Proof.
    intros ch A H. destruct (sym_step_c_ok segs ch (ax_S A) H) as (ch' & E & Hok). unfold dflt_c. rewrite E.
    exists ch'. split; [reflexivity | apply lift_out_ok; exact Hok].
  Qed.
  Lemma ruleA_ok : ltac2:(tb__ "0|0|
S95Sa4S61S96R3S4Sa3R2A1A1A2S17dS17cR4R3R2A3SacR3R2A2A2F_;Fo;FA;Fch;").
  Proof. intros ch A o H. eexists. split; [reflexivity | apply lift_out_ok, rekey_ok; exact H]. Qed.
  Lemma or_else_c_ok_opt : ltac2:(tb__ "0|1|
S45S44S61A1M0S95A2Sa4G0S162G0S4Sa3R2A1A1R3R1A4S17dS17aR4R3A2G0SadLorig;R2S61SacR4R1A2Lo;SacR3S6cVsegs;Sa3R3A1A2A2X44x2A2F_;Forig;FA;Fr;").
  Proof.
    intros [o ch] A orig [E H]. cbn [fst snd] in *. subst o. unfold or_else_c. cbn [fst snd].
    destruct orig as [o|]; [apply ruleA_ok | apply dflt_c_ok]; exact H.
  Qed.
  Lemma or_else_c_ok : ltac2:(tb__ "0|1|
S45S44S61A1M0S95A2Sa4G0S162G0S4Sa3R2A1A1R3R1A4S17dS17aR4R3A2SacR3SeaR2S6cVsegs;Sa3R3A1A2A2A2A2F_;Forig;FA;Fr;").
  Proof. intros r A orig H. pose proof (or_else_c_ok_opt r A orig H) as T. destruct orig; exact T. Qed.

  Definition sym_stepA_c (ch : pcache) (A : axst) : step_outA * pcache := ltac2:(tb__ "0|1b|
Sa3VA;A1S1S43S45SadS95A2M0L_;M1S18R1A1S17bVch;VA;A2M2S44S122A1G0Lx;S67Vsegs;S6R1A1A2S122S122G0Li;R1S92Q5A1M3S92Q14A1G2Limm;Lrd;M4G4G3S92Q15A1G2Limm;Lrd;G3G3S92QcA1M5G2Limm;M6Lrs1;Lrd;M7S131G3G3S92QdA1G2Limm;Lrs2;Lrs1;Lc;S124S43G3G3G5S124G0Lsz;R5S171Vch;VA;R4R3R2R1A6S45S44S61A1M8S95A2M9G8G0Lx;MaS51G8S95R1A3MbS61S4bSadS95SbfVA;R1A2S167S4eG8S95R2A3McS4R9A1R1A3A4Lo;S17bS4eG8S95R1A3MdVA;A2X44x2Tr;S175Vch;VA;R5R3R2R1A6G9GaGbS61S17cGcVA;R1A3Lo;S17aS173GdVA;R6R4R3R2A6VA;A2X44x2Tr;MeGeGeX124x4Limm;Lrs1;Lrd;Lsgn;Lsz;S124G3G3G5S17aS178Vch;R6R4R3R2R1A6VA;A2Limm;Lrs2;Lrs1;Lsz;S121G3G3G5S121G0Lop;MfR4G2G2G2G2G2G2G2G2G2G1S115S66R1A1M10Z7A2S17aS16fVch;R6R3R2A4VA;A2G1S115G10N8A2GaScdVA;R3R2A3S61S17cVch;VA;R1A3Lo;S17aS169Vch;VA;R3R2R1A5VA;A2X44x2G2X43x2X43x2X121xaLimm;Lrs1;Lrd;Lop;S121G3G3S92Q6M11A1GfR4G2G2G2G2G2G2G1S115S93G11R1A2Z3A2S45Sa6S95A2G0Lx;S163Vch;S4R6A1A2Sa6S95G1S181R2S4R8A1SaaVA;A1S63R8R4A2A4S17aS16dR1R8R5R4A4VA;A2S17bR1VA;A2X43x2Lch1;Lpv;X45x1G2X43x2G2G2G2X121xaLsh;Lrs1;Lrd;Lop;S121G3G3G3G2Lrs2;Lrs1;Lrd;M12Lop;M13G7S121G3G3G3G2Lshamt;Lrs1;Lrd;Lop;G13S92Q4A1M14G14G14G3G3G2Lrs1;Lrd;M15Lsucc;Lpred;Lfm;G7G2G2S125G3G3G3S17aS4bG8S95SceR6R4R3R2R1A5Vch;A4VA;A2Lrs2;Lrs1;Lrd;Lop;S125G12Lop;S127S43S43G15Lrl;Laq;Lw;S127S43S43G12Lrl;Laq;Lw;S128S127S43S43G3G3G3S17cVch;VA;SccVsegs;R9R7R6R3R2R1A7A3Lrs2;Lrs1;Lrd;Lrl;Laq;Lwd;Lop;S12bG3G3G5G2Lcsr;M16Lrs1;Lrd;Lop;S12bG3G3G16Luimm;Lrd;Lop;S126G7Lfmt;S126G3G3G6Lrs2;Lrs1;Lfmt;S134S126G3G3G3G3S92Q3A1G2Lrm;M17Lrs3;Lrs2;Lrs1;Lrd;Lfmt;Lop;S132S126G3G3G3G17Lrs2;Lrs1;Lrd;Lfmt;Lop;S126G3G3G17Lrs1;Lrd;M18Lfmt;S137S126G12Lfmt;M19Lop;S135G19Lop;S133G19Lop;S12cS12cG18Lsrc;Ldst;S136S126G15Lfmt;M1aLdir;G1aX122x23Li;G2X44x2X43x2TS;").

  Lemma sym_stepA_c_ok : ltac2:(tb__ "0|0|
S95Sa4S96R2S4Sa3R1A1A1A2S17dS183R3R2A2SdaVsegs;R2A2A2F_;FA;Fch;").
  Proof.
    intros ch A H. unfold sym_stepA_c, sym_stepA. cbv zeta.
    destruct (ss_lenient (ax_S A)); [apply dflt_c_ok; exact H|].
    destruct (instr_at segs (ss_pc (ax_S A))) as [i|]; [|apply dflt_c_ok; exact H].
    destruct i; try (apply dflt_c_ok; exact H).
    -
      destruct sz.
      1: { pose proof (r3_step_c_ok ch A signed rd rs1 imm H) as [E H']. destruct (r3_step_c ch A signed rd rs1 imm) as [o ch1]. cbn [fst snd] in *. subst o.
           destruct (r3_step A signed rd rs1 imm) as [o|]; [|apply dflt_c_ok; exact H'].
           eexists. split; [reflexivity | apply lift_out_j_ok, rekey_ok; exact H']. }
      all: match goal with HH : pc_ok ?ch _ |- context [r3x_step_c ?ch ?A ?z ?rd ?rs1 ?imm] =>
             pose proof (r3x_step_c_ok ch A z rd rs1 imm HH) as [E H']; destruct (r3x_step_c ch A z rd rs1 imm) as [o ch1]; cbn [fst snd] in *; subst o;
             destruct (r3x_step A z rd rs1 imm) as [o|]; [apply ruleA_ok; exact H' | apply or_else_c_ok_opt, r3w_step_c_ok; exact H'] end.
    -   apply or_else_c_ok, zst_step_c_ok; exact H.
    -   match goal with o : aluop |- _ => destruct o end; try (apply dflt_c_ok; exact H).
      destruct (immI imm =? 7); [apply or_else_c_ok, r2_step_c_ok; exact H|].
      destruct (immI imm =? -8); [|apply dflt_c_ok; exact H].
      destruct (andm8_sh_step A rd rs1) as [o|]; [apply ruleA_ok; exact H|].
      apply or_else_c_ok, andm8_step_c_ok; exact H.
    -   match goal with o : aluop |- _ => destruct o end; try (apply dflt_c_ok; exact H).
      destruct (bv_unsigned shamt =? 3); [|apply dflt_c_ok; exact H].
      destruct (prov_c_ok ch _ H) as [E H']. destruct (prov_c ch (ss_facts (ax_S A))) as [pv ch1]. cbn [fst snd] in *. subst pv.
      rewrite x_related_l_eq. destruct (x_related _ _ _ _); [apply or_else_c_ok, r1_step_c_ok; exact H' | apply dflt_c_ok; exact H'].
    -   apply or_else_c_ok. split; [reflexivity | exact H].
    -   apply ruleA_ok; exact H.
  Qed.

  Fixpoint run_past_branch_c (n : nat) (ch : pcache) (A : axst) : option axst :=
    match n with
    | O => None
    | S n' =>
        let '(o, ch') := sym_stepA_c ch A in
        match o with
        | StNextA A' => if is_branch_at segs (ss_pc (ax_S A)) then Some A' else run_past_branch_c n' ch' A'
        | _ => None
        end
    end.
  Lemma run_past_branch_c_eq : ltac2:(tb__ "0|0|
S4dS95Sa4S96R2S4Sa3R1A1A1A2S57S44Sa4A1S17eR4R3R2A3S10cVsegs;R4R2A3A3F_;FA;Fch;Fn;").
  Proof.
    induction n as [|n IH]; intros ch A H; cbn [run_past_branch_c run_past_branch]; [reflexivity|].
    destruct (sym_stepA_c_ok ch A H) as (ch' & -> & H'). destruct (sym_stepA segs A) as [A'|? ?|? ?|?]; try reflexivity.
    destruct (is_branch_at segs (ss_pc (ax_S A))); [reflexivity | apply IH; exact H'].
  Qed.

  Fixpoint run_to_pc_c (n : nat) (pc : Z) (ch : pcache) (A : axst) : option axst :=
    if ss_pc (ax_S A) =? pc then Some A else
    match n with
    | O => None
    | S n' =>
        let '(o, ch') := sym_stepA_c ch A in
        match o with
        | StNextA A' => run_to_pc_c n' pc ch' A'
        | _ => None
        end
    end.
  Lemma run_to_pc_c_eq : ltac2:(tb__ "0|0|
S4dS5eS95Sa4S96R2S4Sa3R1A1A1A2S57S44Sa4A1S17fR5R4R3R2A4S10dVsegs;R5R4R2A4A3F_;FA;Fch;Fpc;Fn;").
  Proof.
    induction n as [|n IH]; intros pc ch A H; cbn [run_to_pc_c run_to_pc]; [reflexivity|].
    destruct (ss_pc (ax_S A) =? pc); [reflexivity|].
    destruct (sym_stepA_c_ok ch A H) as (ch' & -> & H'). destruct (sym_stepA segs A) as [A'|? ?|? ?|?]; try reflexivity.
    apply IH; exact H'.
  Qed.

  Definition try_join_c (A A1 A2 : axst) : option axst := ltac2:(tb__ "0|3|
S44Sa4A1M0G0Lx;M1S17eSe1S98S4Sa3VA1;A1A1A1VA1;A3Sa4G1S17fSe1S6Sa3R1A1A1S98S4Sa3VA2;A1A1A1VA2;A4Sa4Se8S9Sa3VA;A1A1VA;R2R1A4LB2;S4cSa4A1M2X44x2LB1;G2X44x2").
  Lemma try_join_c_eq : ltac2:(tb__ "0|0|
Sa4Sa4Sa4S57S44Sa4A1S184R3R2R1A3Sf4Vsegs;R3R2R1A4A3FA2;FA1;FA;").
  Proof.
    intros A A1 A2. unfold try_join_c, try_join. rewrite run_past_branch_c_eq by apply pc_init_ok.
    destruct (run_past_branch segs JOIN_FUEL A1) as [B1|]; [|reflexivity]. rewrite run_to_pc_c_eq by apply pc_init_ok. reflexivity.
  Qed.

  Lemma join2_facts : ltac2:(tb__ "0|0|
S5fSa4Sa4Sa4Sa4S57S44Sa4A1Se8R5R4R3R2A4S46Sa4R1A2A3S57S47S2A1S4Sa3R2A1A1S4Sa3R5A1A1A3F_;FM;FB2;FB1;FA;Fg;").
  Proof. intros g A B1 B2 M H. unfold join2 in H. destruct (_ && _) in H; [|discriminate]. injection H as <-. reflexivity. Qed.
  Lemma try_join_facts : ltac2:(tb__ "0|0|
Sa4Sa4Sa4Sa4S57S44Sa4A1Sf4Vsegs;R4R3R2A4S46Sa4R1A2A3S57S47S2A1S4Sa3R2A1A1S4Sa3R5A1A1A3F_;FM;FA2;FA1;FA;").
  Proof.
    intros A A1 A2 M H. unfold try_join in H. destruct (run_past_branch segs JOIN_FUEL A1) as [B1|]; [|discriminate].
    destruct (run_to_pc segs JOIN_FUEL (ss_pc (ax_S B1)) A2) as [B2|]; [|discriminate]. exact (join2_facts _ _ _ _ _ H).
  Qed.

  Fixpoint sym_runA_c (fuel : nat) (cuts : list Z) (ch : pcache) (A : axst) (first : bool) : option (list leafA) :=
    match fuel with
    | O => if first then None else Some [mkLeafA A RsFuel]
    | S fuel' =>
        if negb first && memZ (ss_pc (ax_S A)) cuts then Some [mkLeafA A RsCut]
        else
          let fork A1 A2 :=
            match sym_runA_c fuel' cuts (pc_init (ss_facts (ax_S A1))) A1 false,
                  sym_runA_c fuel' cuts (pc_init (ss_facts (ax_S A2))) A2 false with
            | Some l1, Some l2 => Some (l1 ++ l2)
            | _, _ => None
            end in
          let '(o, ch') := sym_stepA_c ch A in
          match o with
          | StNextA A' => sym_runA_c fuel' cuts ch' A' false
          | StForkA A1 A2 => fork A1 A2
          | StJoinA A1 A2 =>
              match try_join_c A A1 A2 with
              | Some M => sym_runA_c fuel' cuts ch M false
              | None => fork A1 A2
              end
          | StStopA r => if first then None else Some [mkLeafA A r]
          end
    end.

  Lemma sym_runA_c_eq : ltac2:(tb__ "0|0|
S4dS47S5eA1S95Sa4S43S96R3S4Sa3R2A1A1A2S57S44S47Sd4A1A1S180R6R5R4R3R2A5Sd9Vsegs;R6R5R3R2A5A3F_;Ffirst;FA;Fch;Fcuts;Ffuel;").
  Proof.
    induction fuel as [|fuel IH]; intros cuts ch A first H; cbn [sym_runA_c sym_runA_ref]; [reflexivity|].
    destruct (negb first && memZ (ss_pc (ax_S A)) cuts); [reflexivity|]. cbv zeta.
    destruct (sym_stepA_c_ok ch A H) as (ch' & -> & H').
    destruct (sym_stepA segs A) as [A'|A1 A2|A1 A2|r]; cbn [stepA_ok] in H'.
    - apply IH; exact H'.
    - rewrite (IH cuts _ A1 false (pc_init_ok _)), (IH cuts _ A2 false (pc_init_ok _)). reflexivity.
    - rewrite try_join_c_eq. destruct (try_join segs A A1 A2) as [M|] eqn:EJ.
      + apply IH. rewrite (try_join_facts _ _ _ _ EJ). exact H.
      + rewrite (IH cuts _ A1 false (pc_init_ok _)), (IH cuts _ A2 false (pc_init_ok _)). reflexivity.
    - reflexivity.
  Qed.

  Definition sym_runA_fast (fuel : nat) (cuts : list Z) (A : axst) (first : bool) : option (list leafA) := ltac2:(tb__ "0|0|
S180Vfuel;Vcuts;S98S4Sa3VA;A1A1A1VA;Vfirst;A5").
  Theorem sym_runA_fast_eq : ltac2:(tb__ "0|0|
S4dS47S5eA1Sa4S43S57S44S47Sd4A1A1S182R4R3R2R1A4Sd9Vsegs;R4R3R2R1A5A3Ffirst;FA;Fcuts;Ffuel;").
  Proof. intros. apply sym_runA_c_eq, pc_init_ok. Qed.
End WithImage.
End StepAFast.

Definition sym_runA (segs : list Segment) (fuel : nat) (cuts : list Z) (A : axst) (first : bool) : option (list leafA) := ltac2:(tb__ "0|0|
S179Vsegs;Vfuel;Vcuts;VA;Vfirst;A5").
Theorem sym_runA_ref_eq : ltac2:(tb__ "0|0|
S47S1c1A1S4dS47S5eA1Sa4S43S57S44S47Sd4A1A1S10eR5R4R3R2R1A5Sd9R5R4R3R2R1A5A3Ffirst;FA;Fcuts;Ffuel;Fsegs;").
Proof. intros. apply StepAFast.sym_runA_fast_eq. Qed.
