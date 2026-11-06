(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "bool"; "list"; "false"; "nat"; "true"; "andb"; "option"; "prod"; "Some"; "length"; "orb"; "pair"; "nil"; "cons"; "fst"; "snd"; "None"; "negb"; "app"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "or"; "False"; "iff"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "sprop"; "cell"; "valuation"; "sstate"; "odefault"; "tfact"; "holds"; "eval"; "ob_base"; "c_off"; "ss_objs"; "ob_dflt"; "ob_lo"; "ss_facts"; "c_val"; "c_width"; "ob_cells"; "ob_hi"; "obj_range"; "smatch"; "obj_holds"; "obj_wf"; "agree_below"; "dflt_writable"; "obj_lo_of"; "soff"; "sv_eqb"; "obj_hi_of"; "rom_ok"; "sfcsr"; "SLit"; "elem_holds"; "freg_sv"; "ranges_disjoint"; "reg_sv"; "ss_fcsr"; "ss_pc"; "ss_resv"; "tf_holds"; "DArr"; "mem_match"; "sprop_eqb"; "DImage"; "DList"; "DRom"; "DUnknown"; "DZero"; "fld_ok"; "pairwise_disjoint"; "rl"; "swf"; "is_arr"; "mkObj"; "ss_next"; "@Stdlib.Lists.List"; "In"; "forallb"; "existsb"; "nth_error"; "NoDup"; "filter"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "sv_equiv"; "lf_state"; "uleq_d"; "uleq"; "ctx0"; "mk_addk"; "mk_dig"; "set_objs"; "align_of"; "fdig"; "in_bounds"; "in_bounds_d"; "itv0"; "lin_decomp"; "mk_alu"; "prove_sprop"; "same_atoms"; "sleq_d"; "snorm"; "tf_inst"; "tf_mentions"; "align_sv"; "mk_ext"; "@Stdlib.ZArith.BinInt.Z"; "add"; "eqb"; "leb"; "le"; "modulo"; "pow"; "mul"; "ltb"; "lt"; "opp"; "sub"; "of_nat"; "to_N"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "triple"; "assn"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "nth"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "rho_sub"; "obj_subst"; "sv_subst"; "wsub_id_below"; "rho_absorb"; "sprop_subst"; "tf_subst"; "wsub_get"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "mk_pf"; "entails"; "odefault_eqb"; "nodupN"; "fact_entailed_d"; "uleq_pf"; "lit_shift_eqb"; "all_regs_eqb"; "tmpl_eqb_with"; "witnesses"; "fact_by_prover_d"; "flds_eqb"; "obj_entailed"; "objs_entailed"; "anchor_cell"; "cells_entailed"; "cells_entailed_pf"; "elem_checked"; "elem_xs"; "find_fld_cell"; "fld_okb"; "pf_d0"; "pf_dg"; "pf_f"; "witnesses_pf"; "align_entailed"; "arr_entailed"; "arr_entailed_pf"; "cell_eqb"; "cell_equiv"; "cell_shift_eqb"; "elem_checked_pf"; "elem_xs_pf"; "entails_cheap"; "entails_pfx"; "find_entailed"; "in_bounds_pf"; "memN"; "objs_entailed_pf"; "prove_sprop_pf"; "resv_entailed"; "sfcsr_entailed"; "sprop_equiv"; "sprop_trivial"; "entails_ref"; "fact_by_prover"; "fact_entailed"; "find_entailed_pf"; "mkPF"; "obj_entailed_pf"; "obj_entailed_same"; "obj_entailed_same_pf"; "obj_entailed_shift"; "obj_entailed_shift_pf"; "pfacts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SP"; "SPJ"; "jpred"; "LQ"; "LQJ"; "stableJ"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state";
"@LinuxProcessSemantics.Riscv.Instr"; "branch_cond"; "aluop"; "mulop"; "ALU_SUB"; "@Corelib.Init.Peano"; "lt"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail.WithSegs"; "select"; "cell_abs"; "complement"; "entails_fr"; "dummy_obj"; "entails_fr_ref"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL"; "dg_ok"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "ltb"; "@Corelib.Init.Nat"; "add"; "sub"; "@LinuxProcessSemantics.Riscv.Sem"; "branch_taken"; "@Stdlib.NArith.BinNat.N"; "mul"; "@Stdlib.PArith.BinPos.Pos"; "eqb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Lia Bool PArith.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundI SymSoundV SymSoundL SymLin SymSoundM SymSoundW SymSoundR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Export SymFrame.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition sprop_trivial (p : sprop) : bool := ltac2:(tb__ "0|13|
S1fS0Lp;Vp;Sd4S1dS1dS1dS0La0;M0R2S13S1dS0Lb0;M1R2S13Se7R5S95Q40M2R2A2S95G2R1A2A3M3Lb;S14S2Li;M4Sd5S1dS1dS2Lb;M5La1;M6Lop;M7G7Sd6G6Lop;M8G8S0S15S1dS2La1;Lw;Lsgn;M9S14S1dS13S2Lk;Li;Ll;MaX1dx8La;G4Sd5S1dG5La;MbLop;McGcSd6GbLop;MdGdS0S15S1dS2La;Lw;Lsgn;MeGaX1dx8Lb0;La0;Lc;S1fS1fS0Lp0;R1Sd4S1dS1dG0R2S13G1R2S13S11G3A1Lb;G4G7G7G8G8G9GaX1dx8La;G4GcGcGdGdGeGaX1dx8Lb0;La0;Lc;S1fS2Lp1;GbGbGbS2S14S13S2La;Li;MfX1fx7Lp0;S1dS1dG0R2S13G1R2S13S7aS77R2S78Z2Z40A2M10A2M11S77R1G10A2M12A2Lb;G4G7G7G8G8G9GaX1dx8La;G4GcGcGdGdGeGaX1dx8Lb0;La0;S1dS1dG0R2S13G1R2S13S75G11G12A2Lb;G4G7G7G8G8G9GaX1dx8La;G4GcGcGdGdGeGaX1dx8Lb0;La0;S1dS1dG0R2S13G1R2S13S74G11G12A2Lb;G4G7G7G8G8G9GaX1dx8La;G4GcGcGdGdGeGaX1dx8Lb0;La0;S4GfX1fx7").

Definition align_entailed (facts : list sprop) (e : sv) (a : Z) : bool := ltac2:(tb__ "0|b|
S5S5S75Z0M0Va;A2S75Va;Z40M1A2A2SaS1dS0Le;Ve;S13S74S77S77R1S78Z2M2G1A2A2S78G2Va;A2A2G0A2M3Lz;S14S75Va;S64Vfacts;R1A2A2Lj;Sd5S1dS1dSd5S0Lop;R3S1dS0La0;R2S13S2Lz;S14S1dS0Lb;R2S13S5S75Va;S64Vfacts;R2A2A2G3A2Lc;S14S2Li;Sd5S1dS1dS2Lb0;La1;M4Lop0;M5G5Sd6G4Lop0;M6G6S0S15S1dS2La1;Lw;Lsgn;M7S14S1dS13S2Lk;Li;Ll;M8X1dx8Lj;G5G5G6G6G7G8X1dx8S2S2S2S2S2S2S2S2S2Xd5xaLb;La0;Lop;Sd5S1dS1dS2Lb;La0;M9Lop;Sd6G9Lop;MaGaS0S15S1dS2La0;Lw;Lsgn;G8X1dx8S75Va;S71Vfacts;Ve;A2A2A2A2").

Fixpoint sprop_equiv (p q : sprop) : bool :=
  match p, q with
  | SPBranch c1 a1 b1, SPBranch c2 a2 b2 =>
      if branch_cond_eq_dec c1 c2 then sv_equiv a1 a2 && sv_equiv b1 b2 else false
  | SPNot p1, SPNot q1 => sprop_equiv p1 q1
  | SPUlt a1 b1, SPUlt a2 b2 => sv_equiv a1 a2 && sv_equiv b1 b2
  | SPUle a1 b1, SPUle a2 b2 => sv_equiv a1 a2 && sv_equiv b1 b2
  | SPEq a1 b1, SPEq a2 b2 => sv_equiv a1 a2 && sv_equiv b1 b2
  | SPTrue, SPTrue => true
  | SPAlign i1 a1, SPAlign i2 a2 => Pos.eqb i1 i2 && Z.eqb a1 a2
  | _, _ => false
  end.

Definition fact_by_prover_d (dg : fdig) (p : sprop) : bool := ltac2:(tb__ "0|d|
S1fS0Lp;Vp;Sd4S1dS1dSd4S0Lc;M0R3S0S0L_;M1S5eVdg;R2Z0M2R1A4M3S5eVdg;R1G2R2A4M4S2X0x2M5G1S5eVdg;R2Z1M6R1A4M7S4S5eVdg;R1G6R2A4X0x2M8S6dVdg;R2G6R1A4M9S6dVdg;R1G2R2A4MaG7G4Xd4x6Lb;La;Lc;S1fS1fS0Lp0;R1Sd4S1dS1dG0R3G8G5GaG9G4G7Xd4x6Lb;La;Lc;S1fS2Lp1;S1dS1dS2Lb;La;MbGbS1dS1dG8Lb;La;S2S14S13S2La;Li;McX1fx7Lp0;S1dS1dG7Lb;La;S1dS1dG3Lb;La;S1dS1dG5Lb;La;S2GcX1fx7").

Definition fact_by_prover (factsL : list sprop) (p : sprop) : bool := ltac2:(tb__ "0|0|
S0S0L_;Sa0S60VfactsL;A1Vp;A2S4Sa0S62VfactsL;A1Vp;A2X0x2").

Definition fact_entailed_d (dg : fdig) (factsL : list sprop) (s : wsub) (p : sprop) : bool := ltac2:(tb__ "0|3|
S1fS0Lp;Vp;Sd4S1dS1dS6S1fA1S0Lx;S8eVs;Vp;A2S1fS0S0L_;M0SaS57S1fS48R1A1VfactsL;A3Sc1R1A1A2S4G0S57S1fSc0R1A1VfactsL;A3S4Sa0Vdg;R1A2X0x2X0x2Lp';S2X6x2M1Lb;La;M2Lc;S1fG1Lp0;G2G2G2G1S14S13SafVfactsL;S90Vs;R2A2R1A3La;Li;X1fx7").

Definition fact_entailed (factsL : list sprop) (s : wsub) (p : sprop) : bool := ltac2:(tb__ "0|0|
S0S0L_;S9aS60VfactsL;A1VfactsL;Vs;Vp;A4S4S9aS62VfactsL;A1VfactsL;Vs;Vp;A4X0x2").

Definition cell_eqb (c c' : cell) : bool := ltac2:(tb__ "0|0|
S5S5S39S28Vc;A1S28Vc';A1A2S74S2eVc;A1S2eVc';A1A2A2S39S2dVc;A1S2dVc';A1A2A2").

Fixpoint flds_eqb (a b : list (Z * Z)) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => (fst x =? fst y) && (snd x =? snd y) && flds_eqb a' b'
  | _, _ => false
  end.

Fixpoint tmpl_eqb_with (eqe : sv -> sv -> bool) (a b : list tfact) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => tf_eqb_with eqe x y && tmpl_eqb_with eqe a' b'
  | _, _ => false
  end.

Definition odefault_eqb (d d' : odefault) : bool := ltac2:(tb__ "0|7|
S23S0Ld;Vd;S23S0Ld';M0Vd';S4S2S2S14S2Ll;M1G1S13S1dS1S7S13S13A2A1M2S1S24A1M3S2Ltmpl;Lflds;Lcnt;Lesz;M4X23x6G0Vd';S2S4S2G1G1G4X23x6G0Vd';S2S2S4G1G1G4X23x6S14G0Vd';S2S2S2S14Se9R2R1A2Ll';M5S14S2Ll0;M6G4X23x6Ll;S14G0Vd';S2S2S2G6G5G4X23x6Ll;S13S1dG2G3G0Vd';S2S2S2G1G1S13S1dG2G3S5S5S5S74R8R4A2S39R7R3A2A2Sa1R6R2A2A2S9eS39R5R1A3A2Lt2;Lf2;Lc2;Le2;X23x6Lt1;Lf1;Lc1;Le1;X23x6").

Definition fld_okb (esz : Z) (f : Z * Z) : bool := ltac2:(tb__ "0|2|
S5S5S75Z0SeS13S13Vf;A3M0A2S75S73G0SfS13S13Vf;A3M1A2Vesz;A2A2SaSaSaS74G1Z1A2S74G1Z2A2A2S74G1Z4A2A2S74G1Z8A2A2A2").

Fixpoint find_fld_cell (factsL : list sprop) (cells : list cell) (lo : sv) (esz : Z) (idx : sv) (f : Z * Z)
  : option cell :=
  match cells with
  | [] => None
  | c :: rest =>
      let here :=
        if c_width c =? snd f then
          match lin_decomp factsL (mk_alu ALU_SUB (c_off c) lo) esz with
          | Some (idx', foff) => (foff =? fst f) && sv_equiv idx' idx
          | None => false
          end
        else false in
      if here then Some c else find_fld_cell factsL rest lo esz idx f
  end.

Fixpoint elem_xs (factsL : list sprop) (cells : list cell) (lo : sv) (esz : Z) (idx : sv)
         (flds : list (Z * Z)) (need : nat -> bool) (j : nat) : option (list sv) :=
  match flds with
  | [] => Some []
  | f :: rest =>
      let here := if need j
                  then option_map (fun c => mk_ext false (8 * Z.to_N (snd f))%N (c_val c)) (find_fld_cell factsL cells lo esz idx f)
                  else Some (SLit 0) in
      match here, elem_xs factsL cells lo esz idx rest need (S j) with
      | Some x, Some xs => Some (x :: xs)
      | _, _ => None
      end
  end.

Fixpoint anchor_cell (factsL : list sprop) (cells : list cell) (lo : sv) (esz : Z) (idx : sv) (flds : list (Z * Z))
  : option (cell * Z) :=
  match flds with
  | [] => None
  | f :: rest => match find_fld_cell factsL cells lo esz idx f with
                 | Some c => Some (c, fst f)
                 | None => anchor_cell factsL cells lo esz idx rest
                 end
  end.

Definition elem_checked (factsL : list sprop) (oL : sobj) (esz : Z) (idx : sv) (flds : list (Z * Z)) (tmplT : list tfact) : bool := ltac2:(tb__ "0|4|
S3S57S24S70R1A1VtmplT;A3Lj;S3S0Fj;S6S7S20S13A2M0A1S0Lx;Sa4VfactsL;S2fVoL;A1M1S2bVoL;A1M2Vesz;Vidx;Vflds;A6G0G0S0Lp;R1S20S13S5S66VfactsL;G2S30VoL;A1S61S28R2A1S7cR1A1A2Vesz;A5S6S1S1dA1M3A1S0Lx;Sa8VfactsL;G1G2Vesz;Vidx;Vflds;R4U0A8G3S56S24S24S56S1fS6bVfactsL;A1S6fR2R1A2A3Lt;VtmplT;A3Lxs;S2X6x2A2Lfoff;Lc;X7x1Lp;S2X6x2Tneed;").

Definition arr_entailed (factsL : list sprop) (oL : sobj) (eszT : Z) (cntT : sv) (fldsT : list (Z * Z)) (tmplT : list tfact) : bool := ltac2:(tb__ "0|6|
S5S36S2aVoL;A1M0A1SaS23S0Lx;G0S2S2S2S14S2Ll;M1G1S13S1dS1S7S13S13A2M2A1S1S24A1S5S5S5S74R4VeszT;A2Sa1R2VfldsT;A2A2S9eS5cR1VtmplT;A3A2SaS5fVfactsL;VcntT;Z0M3R3A4S5S5S5fVfactsL;VcntT;G3S61R3Z1M4A2M5A4S5fVfactsL;R3G4G5A4A2Sa7VfactsL;VoL;VeszT;R3VfldsT;VtmplT;A6A2A2A2LtmplL;LfldsL;LcntL;LeszL;X23x6S5S5S7aG3VeszT;A2S56G2SaaVeszT;A1VfldsT;A3A2S5fVfactsL;VcntT;G3S3dG3A1A4A2A2A2").

Definition cells_entailed (factsL : list sprop) (ceq : cell -> cell -> bool) (oL oT : sobj) : bool := ltac2:(tb__ "0|4|
S5S56S20S20S57S20S20Vceq;R1R2A2LcL;S2fVoL;A1M0A3Lc;S2fVoT;A1M1A3S23S0Lx;S2aVoT;A1S36S2aVoL;A1M2A1S5S98G2S4dA2S56S20S20S57S20S20Vceq;R2R1A2Lc;G1A3LcL;G0A3M3A2S5S98G2S49A2G3A2S14S5S98G2S4aR1A1A2G3A2Ll;S14S5S98G2S4bR1A1A2G3A2Ll;S13S1dS1S7S13S13A2A1S1S24A1Sb0VfactsL;VoL;R4R3R2R1A6LtmplT;LfldsT;LcntT;LeszT;X23x6A2").

Definition cell_equiv (c c' : cell) : bool := ltac2:(tb__ "0|1|
S0S0L_;M0S5cS28Vc;A1S28Vc';A1A2G0S74S2eVc;A1S2eVc';A1A2S5cS2dVc;A1S2dVc';A1A2S2X0x2S2X0x2").

Definition obj_entailed_same (factsL : list sprop) (oL oT : sobj) : bool := ltac2:(tb__ "0|1|
S0S0L_;M0S5cS27VoL;A1S27VoT;A1A2G0S5cS2bVoL;A1S2bVoT;A1A2G0S5cS30VoL;A1S30VoT;A1A2Sa5VfactsL;Sb3VoL;VoT;A4S2X0x2S2X0x2S2X0x2").

Definition lit_shift_eqb (c : Z) (eL eT : sv) : bool := ltac2:(tb__ "0|6|
S1dS0LeL;VeL;S13S1dS0LeT;VeT;S13S74S6eR1A1S7dS6eR2A1Vc;A2A2Lzt;S14S2Li;M0Sd5S1dS1dS2Lb;La;M1Lop;M2G2Sd6G1Lop;M3G3S0S15S1dS2La;Lw;Lsgn;M4S14S1dS13S2Lk;Li;Ll;M5X1dx8Lzl;G0G2G2G3G3G4G5X1dx8").

Definition cell_shift_eqb (c : Z) (cL cT : cell) : bool := ltac2:(tb__ "0|1|
S0S0L_;M0S9cVc;S28VcL;A1S28VcT;A1A3G0S74S2eVcL;A1S2eVcT;A1A2S39S2dVcL;A1S2dVcT;A1A2S2X0x2S2X0x2").

Definition obj_entailed_shift (factsL : list sprop) (oL oT : sobj) : bool := ltac2:(tb__ "0|2|
S6S13A1S0Lx;S6cS27VoT;A1S27VoL;A1M0A2S13S0S0L_;M1S9cR1S2bVoL;A1S2bVoT;A1A3G1S9cR1S30VoL;A1S30VoT;A1A3S7S13S13A2S0Lx;S68VfactsL;G0A2S13S13G1S5S5S75Z0S73R2R3A2A2S7aS73R1R3A2S78Z2Z40A2A2A2S75R2R1A2A2Sa5VfactsL;Sb4R3A1VoL;VoT;A4S2X0x2Lh;Ll;X7x1S2X0x2S2X0x2Lc;S2X6x2").

Definition obj_entailed (factsL : list sprop) (oL oT : sobj) : bool := ltac2:(tb__ "0|0|
S0S0L_;Sc8VfactsL;VoL;VoT;A3S4ScaVfactsL;VoL;VoT;A3X0x2").

Fixpoint find_entailed (factsL : list sprop) (objsL : list sobj) (oT : sobj) (n : nat) : option nat :=
  match objsL with
  | [] => None
  | o :: t => if obj_entailed factsL o oT then Some n else find_entailed factsL t oT (S n)
  end.

Fixpoint witnesses (factsL : list sprop) (objsL : list sobj) (objsT : list sobj) : option (list nat) :=
  match objsT with
  | [] => Some []
  | oT :: t => match find_entailed factsL objsL oT 0, witnesses factsL objsL t with
               | Some n, Some ns => Some (n :: ns)
               | _, _ => None
               end
  end.

Fixpoint memN (n : nat) (l : list nat) : bool :=
  match l with [] => false | x :: t => Nat.eqb x n || memN n t end.

Fixpoint nodupN (l : list nat) : bool :=
  match l with [] => true | x :: t => negb (memN x t) && nodupN t end.

Definition objs_entailed (factsL : list sprop) (objsL objsT : list sobj) : bool := ltac2:(tb__ "0|2|
S0S0L_;Se3S9S1eVobjsT;A2S9S1eVobjsL;A2A2M0S6S1S3A1M1A1S0Lx;S9fVfactsL;VobjsL;VobjsT;A3G1S5S99R1A1G0A2Lns;S2X6x2S2X0x2").

Record pfacts := mkPF { pf_f : list sprop; pf_d0 : fdig; pf_dg : fdig }.
Definition mk_pf (f : list sprop) : pfacts := ltac2:(tb__ "0|0|
Sc6Vf;S60Vf;A1S62Vf;A1A3").

Definition uleq_pf (pf : pfacts) (a : sv) (k : Z) (b : sv) : bool := ltac2:(tb__ "0|0|
S0S0L_;S5eSabVpf;A1Va;Vk;Vb;A4S4S5eSacVpf;A1Va;Vk;Vb;A4X0x2").
Definition in_bounds_pf (pf : pfacts) (lo hi off : sv) (k : Z) : bool := ltac2:(tb__ "0|0|
S0S0L_;S67SabVpf;A1Vlo;Vhi;Voff;Vk;A5S4S67SacVpf;A1Vlo;Vhi;Voff;Vk;A5X0x2").
Definition prove_sprop_pf (pf : pfacts) (p : sprop) : bool := ltac2:(tb__ "0|1|
SaS57S1fS48Vp;A1SadVpf;A1A3S1fS0Lp;Vp;Sd4S1dS1dS2Lb;La;M0Lc;S1fS2Lp0;S1dS1dS9bVpf;R2Z1R1A4Lb;La;S1dS1dS9bVpf;R2Z0R1A4Lb;La;G0S2S14S13S2La;Li;X1fx7A2").
Lemma uleq_pf_eq : ltac2:(tb__ "0|0|
S1S1fA1S1dS13S1dS16S0S9bS96R4A1R3R2R1A4S5fR4R3R2R1A4A3Fb;Fk;Fa;Ff;").
Proof. reflexivity. Qed.
Lemma in_bounds_pf_eq : ltac2:(tb__ "0|0|
S1S1fA1S1dS1dS1dS13S16S0SbaS96R5A1R4R3R2R1A5S66R5R4R3R2R1A5A3Fk;Foff;Fhi;Flo;Ff;").
Proof. reflexivity. Qed.
Lemma prove_sprop_pf_eq : ltac2:(tb__ "0|0|
S1S1fA1S1fS16S0SbdS96R2A1R1A2S6bR2R1A2A3Fp;Ff;").
Proof. reflexivity. Qed.

Fixpoint elem_xs_pf (pf : pfacts) (cells : list cell) (lo : sv) (esz : Z) (idx : sv)
         (flds : list (Z * Z)) (need : nat -> bool) (j : nat) : option (list sv) :=
  match flds with
  | [] => Some []
  | f :: rest =>
      let here := if need j
                  then option_map (fun c => mk_ext false (8 * Z.to_N (snd f))%N (c_val c)) (find_fld_cell (pf_f pf) cells lo esz idx f)
                  else Some (SLit 0) in
      match here, elem_xs_pf pf cells lo esz idx rest need (S j) with
      | Some x, Some xs => Some (x :: xs)
      | _, _ => None
      end
  end.
Lemma elem_xs_pf_eq : ltac2:(tb__ "0|0|
S1S1fA1S1S20A1S1dS13S1dS1S7S13S13A2A1S3S0F_;S3S16S6S1S1dA1A1Sb6S96R8A1R7R6R5R4R3R2R1A8Sa8R8R7R6R5R4R3R2R1A8A3Fj;Fneed;Fflds;Fidx;Fesz;Flo;Fcells;Ff;").
Proof. intros f cells lo esz idx flds. induction flds as [|x t IH]; intros need j; cbn [elem_xs_pf elem_xs]; [reflexivity|]. rewrite IH. reflexivity. Qed.

Definition elem_checked_pf (pf : pfacts) (oL : sobj) (esz : Z) (idx : sv) (flds : list (Z * Z)) (tmplT : list tfact) : bool := ltac2:(tb__ "0|4|
S3S57S24S70R1A1VtmplT;A3Lj;S3S0Fj;S6S7S20S13A2M0A1S0Lx;Sa4SadVpf;A1S2fVoL;A1M1S2bVoL;A1M2Vesz;Vidx;Vflds;A6G0G0S0Lp;R1S20S13S5SbaVpf;G2S30VoL;A1S61S28R2A1S7cR1A1A2Vesz;A5S6S1S1dA1M3A1S0Lx;Sb6Vpf;G1G2Vesz;Vidx;Vflds;R4U0A8G3S56S24S24S56S1fSbdVpf;A1S6fR2R1A2A3Lt;VtmplT;A3Lxs;S2X6x2A2Lfoff;Lc;X7x1Lp;S2X6x2Tneed;").
Lemma elem_checked_pf_eq : ltac2:(tb__ "0|0|
S1S1fA1S1eS13S1dS1S7S13S13A2A1S1S24A1S16S0Sb5S96R6A1R5R4R3R2R1A6Sa7R6R5R4R3R2R1A6A3FtmplT;Fflds;Fidx;Fesz;FoL;Ff;").
Proof. intros. unfold elem_checked_pf, elem_checked. cbn [pf_f mk_pf]. rewrite elem_xs_pf_eq. reflexivity. Qed.

Definition arr_entailed_pf (pf : pfacts) (oL : sobj) (eszT : Z) (cntT : sv) (fldsT : list (Z * Z)) (tmplT : list tfact) : bool := ltac2:(tb__ "0|6|
S5S36S2aVoL;A1M0A1SaS23S0Lx;G0S2S2S2S14S2Ll;M1G1S13S1dS1S7S13S13A2M2A1S1S24A1S5S5S5S74R4VeszT;A2Sa1R2VfldsT;A2A2S9eS5cR1VtmplT;A3A2SaS9bVpf;VcntT;Z0M3R3A4S5S5S9bVpf;VcntT;G3S61R3Z1M4A2M5A4S9bVpf;R3G4G5A4A2Sb5Vpf;VoL;VeszT;R3VfldsT;VtmplT;A6A2A2A2LtmplL;LfldsL;LcntL;LeszL;X23x6S5S5S7aG3VeszT;A2S56G2SaaVeszT;A1VfldsT;A3A2S9bVpf;VcntT;G3S3dG3A1A4A2A2A2").
Lemma arr_entailed_pf_eq : ltac2:(tb__ "0|0|
S1S1fA1S1eS13S1dS1S7S13S13A2A1S1S24A1S16S0Sb1S96R6A1R5R4R3R2R1A6Sb0R6R5R4R3R2R1A6A3FtmplT;FfldsT;FcntT;FeszT;FoL;Ff;").
Proof. intros. unfold arr_entailed_pf, arr_entailed. destruct (ob_dflt oL); try reflexivity. rewrite elem_checked_pf_eq. reflexivity. Qed.

Definition cells_entailed_pf (pf : pfacts) (ceq : cell -> cell -> bool) (oL oT : sobj) : bool := ltac2:(tb__ "0|4|
S5S56S20S20S57S20S20Vceq;R1R2A2LcL;S2fVoL;A1M0A3Lc;S2fVoT;A1M1A3S23S0Lx;S2aVoT;A1S36S2aVoL;A1M2A1S5S98G2S4dA2S56S20S20S57S20S20Vceq;R2R1A2Lc;G1A3LcL;G0A3M3A2S5S98G2S49A2G3A2S14S5S98G2S4aR1A1A2G3A2Ll;S14S5S98G2S4bR1A1A2G3A2Ll;S13S1dS1S7S13S13A2A1S1S24A1Sb1Vpf;VoL;R4R3R2R1A6LtmplT;LfldsT;LcntT;LeszT;X23x6A2").
Lemma cells_entailed_pf_eq : ltac2:(tb__ "0|0|
S1S1fA1S20S20S0F_;F_;S1eS1eS16S0Sa6S96R4A1R3R2R1A4Sa5R4R3R2R1A4A3FoT;FoL;Fceq;Ff;").
Proof. intros. unfold cells_entailed_pf, cells_entailed. destruct (ob_dflt oT); try reflexivity. rewrite arr_entailed_pf_eq. reflexivity. Qed.

Definition obj_entailed_same_pf (pf : pfacts) (oL oT : sobj) : bool := ltac2:(tb__ "0|1|
S0S0L_;M0S5cS27VoL;A1S27VoT;A1A2G0S5cS2bVoL;A1S2bVoT;A1A2G0S5cS30VoL;A1S30VoT;A1A2Sa6Vpf;Sb3VoL;VoT;A4S2X0x2S2X0x2S2X0x2").
Definition obj_entailed_shift_pf (pf : pfacts) (oL oT : sobj) : bool := ltac2:(tb__ "0|2|
S6S13A1S0Lx;S6cS27VoT;A1S27VoL;A1M0A2S13S0S0L_;M1S9cR1S2bVoL;A1S2bVoT;A1A3G1S9cR1S30VoL;A1S30VoT;A1A3S7S13S13A2S0Lx;S68SadVpf;A1G0A2S13S13G1S5S5S75Z0S73R2R3A2A2S7aS73R1R3A2S78Z2Z40A2A2A2S75R2R1A2A2Sa6Vpf;Sb4R3A1VoL;VoT;A4S2X0x2Lh;Ll;X7x1S2X0x2S2X0x2Lc;S2X6x2").
Definition obj_entailed_pf (pf : pfacts) (oL oT : sobj) : bool := ltac2:(tb__ "0|0|
S0S0L_;Sc9Vpf;VoL;VoT;A3S4ScbVpf;VoL;VoT;A3X0x2").
Lemma obj_entailed_pf_eq : ltac2:(tb__ "0|0|
S1S1fA1S1eS1eS16S0Sc7S96R3A1R2R1A3Sa2R3R2R1A3A3FoT;FoL;Ff;").
Proof.
  intros. unfold obj_entailed_pf, obj_entailed, obj_entailed_same_pf, obj_entailed_same, obj_entailed_shift_pf, obj_entailed_shift.
  cbn [pf_f mk_pf]. rewrite cells_entailed_pf_eq. destruct (same_atoms (ob_base oT) (ob_base oL)); [|reflexivity].
  rewrite cells_entailed_pf_eq. reflexivity.
Qed.

Fixpoint find_entailed_pf (pf : pfacts) (objsL : list sobj) (oT : sobj) (n : nat) : option nat :=
  match objsL with
  | [] => None
  | o :: t => if obj_entailed_pf pf o oT then Some n else find_entailed_pf pf t oT (S n)
  end.
Lemma find_entailed_pf_eq : ltac2:(tb__ "0|0|
S1S1fA1S1S1eA1S1eS3S16S6S3A1Sc5S96R4A1R3R2R1A4Sb9R4R3R2R1A4A3Fn;FoT;FobjsL;Ff;").
Proof. intros f objsL oT. induction objsL as [|o t IH]; intros n; cbn [find_entailed_pf find_entailed]; [reflexivity|]. rewrite obj_entailed_pf_eq, IH. reflexivity. Qed.

Fixpoint witnesses_pf (pf : pfacts) (objsL : list sobj) (objsT : list sobj) : option (list nat) :=
  match objsT with
  | [] => Some []
  | oT :: t => match find_entailed_pf pf objsL oT 0, witnesses_pf pf objsL t with
               | Some n, Some ns => Some (n :: ns)
               | _, _ => None
               end
  end.
Lemma witnesses_pf_eq : ltac2:(tb__ "0|1|
S1S1fA1S1S1eA1M0G0S16S6S1S3A1A1SaeS96R3A1R2R1A3S9fR3R2R1A3A3FobjsT;FobjsL;Ff;").
Proof. intros f objsL objsT. induction objsT as [|o t IH]; cbn [witnesses_pf witnesses]; [reflexivity|]. rewrite find_entailed_pf_eq, IH. reflexivity. Qed.

Definition objs_entailed_pf (pf : pfacts) (objsL objsT : list sobj) : bool := ltac2:(tb__ "0|2|
S0S0L_;Se3S9S1eVobjsT;A2S9S1eVobjsL;A2A2M0S6S1S3A1M1A1S0Lx;SaeVpf;VobjsL;VobjsT;A3G1S5S99R1A1G0A2Lns;S2X6x2S2X0x2").
Lemma objs_entailed_pf_eq : ltac2:(tb__ "0|1|
S1S1fA1S1S1eA1M0G0S16S0SbcS96R3A1R2R1A3Sa3R3R2R1A3A3FobjsT;FobjsL;Ff;").
Proof. intros. unfold objs_entailed_pf, objs_entailed. rewrite witnesses_pf_eq. reflexivity. Qed.

Fixpoint all_regs_eqb (k : nat) (f : Z -> bool) : bool :=
  match k with
  | O => true
  | S k' => f (Z.of_nat k') && all_regs_eqb k' f
  end.

Definition sfcsr_entailed (fL fT : sfcsr) (s : wsub) : bool := ltac2:(tb__ "0|1|
S3cS0LfL;VfL;S3cS0LfT;M0VfT;S4S1dS2Lv;X3cx2S1dG0VfT;S2S1dS5cR2S8bVs;R1A2A2Lv';X3cx2Lv;X3cx2").

Definition resv_entailed (rL rT : option sv) (s : wsub) : bool := ltac2:(tb__ "0|2|
S6S1dA1M0S0LrL;VrL;S1dG0S0LrT;M1VrT;S1dS5cR2S8bVs;R1A2A2Lv';S2X6x2Lv;G1VrT;S1dS2Ls0;S4X6x2X6x2").

Definition entails_ref (L T : sstate) (s : wsub) : bool := ltac2:(tb__ "0|3|
S5S5S5S5S5S5S5S51VT;A1S74S43VL;A1S43VT;A1A2A2S9dU20M0S13SaS74R1Z0A2S5cS41VL;R1A2S8bVs;S41VT;R1A2A2A2A2Lr;A2A2S9dG0S13S5cS3fVL;R1A2S8bVs;S3fVT;R1A2A2A2Lr;A2A2SbfS42VL;A1S42VT;A1Vs;A3A2SbeS44VL;A1S44VT;A1Vs;A3A2Sa3S2cVL;A1M1S29VL;A1S85S1eS1eS8aVs;A1S29VT;A1A4A3A2S0S0L_;S56S1fS9aS60G1A1G1Vs;A3S2cVT;A1M2A3S4S56S1fS9aS62G1A1G1Vs;A3G2A3X0x2A2").

Definition entails_pfx (pf : pfacts) (L T : sstate) (s : wsub) : bool := ltac2:(tb__ "0|3|
S0S0L_;M0SbcVpf;S29VL;A1S85S1eS1eS8aVs;A1S29VT;A1A4A3G0S56S1fS9aSabVpf;A1S2cVL;A1M1Vs;A3S2cVT;A1M2A3S4S56S1fS9aSacVpf;A1G1Vs;A3G2A3X0x2S2X0x2").

Definition entails_cheap (L T : sstate) (s : wsub) : bool := ltac2:(tb__ "0|2|
S0S0L_;M0S51VT;A1G0S74S43VL;A1S43VT;A1A2G0S9dU20M1S13SaS74R1Z0A2S5cS41VL;R1A2S8bVs;S41VT;R1A2A2A2A2Lr;A2G0S9dG1S13S5cS3fVL;R1A2S8bVs;S3fVT;R1A2A2A2Lr;A2G0SbfS42VL;A1S42VT;A1Vs;A3SbeS44VL;A1S44VT;A1Vs;A3S2X0x2S2X0x2S2X0x2S2X0x2S2X0x2").

Definition entails (L T : sstate) (s : wsub) : bool := ltac2:(tb__ "0|0|
S0S0L_;Sb7VL;VT;Vs;A3Sb8S96S2cVL;A1A1VL;VT;Vs;A4S2X0x2").

Lemma lazy_andb_andb : ltac2:(tb__ "0|0|
S0S0S16S0S0S0La;R2R1S2X0x2S5R2R1A2A3Fb;Fa;").
Proof. intros [|] b; reflexivity. Qed.

Lemma entails_eq : ltac2:(tb__ "0|0|
S22S22S88S16S0S97R3R2R1A3Sc2R3R2R1A3A3Fs;FT;FL;").
Proof.
  intros. unfold entails, entails_cheap, entails_pfx, entails_ref. rewrite objs_entailed_pf_eq.
  rewrite !lazy_andb_andb. rewrite !Bool.andb_assoc. reflexivity.
Qed.

Lemma all_regs_eqb_spec : ltac2:(tb__ "0|0|
S3S13S0F_;S13S16S0S9dR3R2A2S4A3S17S76Z0R2A2S7bR2S7eR4A1A2A2S16S0R4R3A1S4A3F_;F_;Fr;Ff;Fk;").
Proof.
  induction k as [|k IH]; intros f r H Hr; [lia|].
  cbn in H. apply andb_prop in H as [H1 H2].
  destruct (Z.eq_dec r (Z.of_nat k)) as [->|Hne]; [exact H1|].
  apply IH; [exact H2|]. lia.
Qed.

Lemma sprop_trivial_sound : ltac2:(tb__ "0|0|
S21S1fS16S0Sc1R1A1S4A3S25R3R2A2F_;Fp;Frho;").
Proof.
  intros rho p H. destruct p; cbn in H; try discriminate.
  - destruct a; try discriminate. destruct b; try discriminate. cbn. exact H.
  - destruct p; try discriminate. destruct a; try discriminate. destruct b; try discriminate.
    cbn. intros Ht. rewrite Ht in H. discriminate.
  - destruct a; try discriminate. destruct b; try discriminate. cbn.
    rewrite !Z_to_bv_unsigned. unfold bv_wrap. rewrite two64. apply Z.ltb_lt in H. exact H.
  - destruct a; try discriminate. destruct b; try discriminate. cbn.
    rewrite !Z_to_bv_unsigned. unfold bv_wrap. rewrite two64. apply Z.leb_le in H. exact H.
  - destruct a; try discriminate. destruct b; try discriminate. cbn.
    apply Z.eqb_eq in H. apply Z_to_bv64_eq_iff. exact H.
  - exact I.
Qed.

Lemma mod_pow2_mono : ltac2:(tb__ "0|2|
S13S13S13S17S76Z0R2A2S76R2R1A2A2S16S13S77S77R4S78Z2M0R2A2A2S78G0R3A2M1A2S77R4G1A2A3F_;Fb;Fa;Fx;").
Proof.
  intros x a b H.
  rewrite <- Znumtheory.Zmod_div_mod; try (apply Z.pow_pos_nonneg; lia).
  - reflexivity.
  - exists (2 ^ (b - a)). rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.

Lemma align_weaken : ltac2:(tb__ "0|2|
S13S13S13S17S76Z0M0R2A2S76R2R1A2A2S16S13S77R4S78Z2M1R2A2A2G0A3S16S13S77R5S78G1R4A2A2G0A3F_;F_;Fb;Fa;Fx;").
Proof.
  intros x a b H Hb. rewrite <- (mod_pow2_mono x a b H). rewrite Hb. apply Z.mod_0_l. apply Z.pow_nonzero; lia.
Qed.

Lemma align_entailed_sound : ltac2:(tb__ "0|1|
S21S1S1fA1S1dS13S84S1fS25R4A1R3A3S16S0SafR4R3R2A3S4A3S17S76Z0M0R3A2S16S13S77S93Q40S26R6R4A2A2S78Z2R3A2A2G0A3A2F_;F_;Fa;Fe;Ffacts;Frho;").
Proof.
  intros rho facts e a Hf H. unfold align_entailed in H.
  apply andb_prop in H as [H12 H3]. apply andb_prop in H12 as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2.
  split; [exact H1|].
  destruct (Z.leb_spec a (align_sv facts e)) as [Hle|Hgt].
  { pose proof (align_sv_sound rho facts e Hf) as [Hr Hd].
    apply Z.mod_divide; [apply Z.pow_nonzero; lia|]. eapply divide_pow2_le; [|exact Hd]. lia. }
  rewrite Bool.orb_false_r in H3.
  destruct e; try discriminate.
  - cbn. rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite two64. apply Z.eqb_eq in H3. exact H3.
  - cbn. apply Z.leb_le in H3.
    pose proof (align_of_sound rho facts i Hf) as [Ha0 Hal].
    eapply align_weaken; [|exact Hal]. lia.
  - destruct op; try discriminate. destruct e1; try discriminate. destruct e2; try discriminate.
    apply andb_prop in H3 as [H3 H4]. apply Z.leb_le in H3. apply Z.eqb_eq in H4.
    pose proof (align_of_sound rho facts i Hf) as [Ha0 Hal].
    cbn [eval]. unfold alu64, alu. rewrite bv_add_unsigned, Z_to_bv_unsigned. unfold bv_wrap. rewrite two64.
    rewrite (congr_add (bv_unsigned (rw rho i)) z a); [| lia | eapply align_weaken; [|exact Hal]; lia].
    rewrite <- (mod_pow2_mono z a 64) by lia. exact H4.
Qed.

Lemma existsb_sprop_eqb : ltac2:(tb__ "0|0|
S1fS1S1fA1S16S0S57S1fS48R2A1R1A3S4A3S55S1fR3R2A3F_;Ffacts;Fp;").
Proof.
  intros p facts H. apply existsb_exists in H as (q & Hin & Heq).
  rewrite (sprop_eqb_sound _ _ Heq). exact Hin.
Qed.

Lemma sprop_equiv_sound : ltac2:(tb__ "0|0|
S21S1fS1fS16S0Sc0R2R1A2S4A3S1bS25R4R3A2S25R4R2A2A2F_;Fq;Fp;Frho;").
Proof.
  intros rho p. induction p; intros q H; destruct q; cbn in H; try discriminate; cbn [holds];
    try (apply andb_prop in H as [H1 H2];
         rewrite (sv_equiv_sound rho _ _ H1), (sv_equiv_sound rho _ _ H2); split; intros X; exact X).
  - destruct (branch_cond_eq_dec c c0) as [<-|]; [|discriminate].
    apply andb_prop in H as [H1 H2].
    rewrite (sv_equiv_sound rho _ _ H1), (sv_equiv_sound rho _ _ H2). split; intros X; exact X.
  - specialize (IHp q H). destruct IHp as [A B]. split; intros X Y; apply X; auto.
  - split; intros X; exact X.
  - apply andb_prop in H as [H1 H2]. apply Pos.eqb_eq in H1. apply Z.eqb_eq in H2. subst. split; intros X; exact X.
Qed.

Lemma fact_by_prover_d_sound : ltac2:(tb__ "0|0|
S21S65S1fSe2R3R2A2S16S0Sa0R3R2A2S4A3S25R5R3A2F_;F_;Fp;Fdg;Frho;").
Proof.
  intros rho dg p Hall H.
  assert (U1 : forall a k b, uleq_d dg a k b = true -> bv_unsigned (eval rho a) + k <= bv_unsigned (eval rho b)).
  { intros a k b Hu. exact (uleq_d_sound rho dg a k b Hall Hu). }
  assert (NE : forall a b, (uleq_d dg a 1 b ||| uleq_d dg b 1 a) = true -> eval rho a <> eval rho b).
  { intros a b Hu X. apply lazy_orb_prop in Hu as [Hu|Hu]; apply U1 in Hu; rewrite X in Hu; lia. }
  assert (EQ : forall a b, (uleq_d dg a 0 b &&& uleq_d dg b 0 a) = true -> eval rho a = eval rho b).
  { intros a b Hu. apply lazy_andb_prop in Hu as [H1 H2]. apply U1 in H1. apply U1 in H2. apply bv_eq. lia. }
  assert (S1 : forall a k b, sleq_d dg a k b = true -> bv_signed (eval rho a) + k <= bv_signed (eval rho b)).
  { intros a k b Hs. exact (sleq_d_sound rho dg a k b Hall Hs). }
  unfold fact_by_prover_d in H.
  destruct p as [c a b|p|a b|a b|a b| |i al]; try discriminate.
  - destruct c; try discriminate; cbn [holds branch_taken]; unfold bv_ltu, bv_lts, bv_eqb.
    + apply Z.eqb_eq. rewrite (EQ a b H). reflexivity.
    + apply Bool.negb_true_iff. apply Z.eqb_neq. intros X. apply (NE a b H). apply bv_eq. exact X.
    + apply Z.ltb_lt. pose proof (S1 _ _ _ H). lia.
    + apply Bool.negb_true_iff. apply Z.ltb_ge. pose proof (S1 _ _ _ H). lia.
    + apply Z.ltb_lt. pose proof (U1 _ _ _ H). lia.
    + apply Bool.negb_true_iff. apply Z.ltb_ge. pose proof (U1 _ _ _ H). lia.
  - destruct p as [c a b|p|a b|a b|a b| |i al]; try discriminate.
    + destruct c; try discriminate; cbn [holds branch_taken]; unfold bv_ltu, bv_lts, bv_eqb.
      * intros X. apply Z.eqb_eq in X. apply (NE a b H). apply bv_eq. exact X.
      * rewrite (EQ a b H), Z.eqb_refl. cbn. intros X; discriminate.
      * intros X. apply Z.ltb_lt in X. pose proof (S1 _ _ _ H). lia.
      * intros X. apply Bool.negb_true_iff in X. apply Z.ltb_ge in X. pose proof (S1 _ _ _ H). lia.
      * intros X. apply Z.ltb_lt in X. pose proof (U1 _ _ _ H). lia.
      * intros X. apply Bool.negb_true_iff in X. apply Z.ltb_ge in X. pose proof (U1 _ _ _ H). lia.
    + cbn [holds]. exact (NE a b H).
  - cbn [holds]. pose proof (U1 _ _ _ H). lia.
  - cbn [holds]. pose proof (U1 _ _ _ H). lia.
  - cbn [holds]. exact (EQ a b H).
Qed.

Lemma fact_by_prover_sound : ltac2:(tb__ "0|0|
S21S1S1fA1S1fS84S1fS25R3A1R2A3S16S0Sc3R3R2A2S4A3S25R5R3A2F_;F_;Fp;FfactsL;Frho;").
Proof.
  intros rho factsL p Hall H. unfold fact_by_prover in H. apply lazy_orb_prop in H as [H|H].
  - eapply fact_by_prover_d_sound; [apply ctx0_dg_ok; exact Hall | exact H].
  - eapply fact_by_prover_d_sound; [apply mk_dig_ok; exact Hall | exact H].
Qed.

Lemma fact_entailed_d_sound : ltac2:(tb__ "0|0|
S21S65S1S1fA1S88S1fS84S1fS25R5A1R3A3Se2R6R5A2S16S0S9aR6R5R4R3A4S4A3S25S89R8R5A2R4A2F_;F_;F_;Fp;Fs;FfactsL;Fdg;Frho;").
Proof.
  intros rho dg factsL s p Hall Hd H.
  assert (G : forall q, match sprop_subst s q with
                        | Some p' => (existsb (sprop_eqb p') factsL || sprop_trivial p')
                                     ||| (existsb (sprop_equiv p') factsL ||| fact_by_prover_d dg p')
                        | None => false end = true -> holds (rho_sub rho s) q).
  { intros q Hq. destruct (sprop_subst s q) as [p'|] eqn:Hs; [|discriminate].
    apply (sprop_subst_sound rho s q p' Hs).
    apply lazy_orb_prop in Hq. destruct Hq as [Hq|Hq]; [apply orb_prop in Hq; destruct Hq as [Hin|Htr] | apply lazy_orb_prop in Hq; destruct Hq as [Heqv|Hpr]].
    - apply existsb_sprop_eqb in Hin. exact (proj1 (Forall_forall _ _) Hall _ Hin).
    - apply sprop_trivial_sound. exact Htr.
    - apply existsb_exists in Heqv as (f & Hin & Heq).
      apply (proj2 (sprop_equiv_sound rho p' f Heq)). exact (proj1 (Forall_forall _ _) Hall _ Hin).
    - exact (fact_by_prover_d_sound rho dg p' Hd Hpr). }
  destruct p; try (apply G; exact H).
  cbn in H. cbn. exact (align_entailed_sound rho factsL _ _ Hall H).
Qed.

Lemma fact_entailed_sound : ltac2:(tb__ "0|0|
S21S1S1fA1S88S1fS84S1fS25R4A1R3A3S16S0Sc4R4R3R2A3S4A3S25S89R6R4A2R3A2F_;F_;Fp;Fs;FfactsL;Frho;").
Proof.
  intros rho factsL s p Hall H. unfold fact_entailed in H. apply lazy_orb_prop in H as [H|H].
  - eapply fact_entailed_d_sound; [exact Hall | apply ctx0_dg_ok; exact Hall | exact H].
  - eapply fact_entailed_d_sound; [exact Hall | apply mk_dig_ok; exact Hall | exact H].
Qed.

Lemma cell_eqb_sound : ltac2:(tb__ "0|0|
S20S20S16S0Sb2R2R1A2S4A3S16S20R3R2A3F_;Fc';Fc;").
Proof.
  intros [o w v] [o' w' v'] H. unfold cell_eqb in H. cbn in H.
  apply andb_prop in H as [H Hv]. apply andb_prop in H as [Ho Hw].
  apply sv_eqb_sound in Ho. apply Z.eqb_eq in Hw. apply sv_eqb_sound in Hv. congruence.
Qed.

Lemma existsb_cell_eqb : ltac2:(tb__ "0|0|
S20S1S20A1S16S0S57S20Sb2R2A1R1A3S4A3S55S20R3R2A3F_;Fcells;Fc;").
Proof.
  intros c cells H. apply existsb_exists in H as (c' & Hin & Heq).
  rewrite (cell_eqb_sound _ _ Heq). exact Hin.
Qed.

Lemma flds_eqb_sound : ltac2:(tb__ "0|1|
S1S7S13S13A2A1M0G0S16S0Sa1R2R1A2S4A3S16G0R3R2A3F_;Fb;Fa;").
Proof.
  induction a as [|x a IH]; intros [|y b] H; cbn in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. rewrite (IH b H3). destruct x, y; cbn in *; subst; reflexivity.
Qed.

Lemma tmpl_eqb_sound : ltac2:(tb__ "0|1|
S1S24A1M0G0S16S0S9eS39R2R1A3S4A3S16G0R3R2A3F_;Fb;Fa;").
Proof.
  induction a as [|x a IH]; intros [|y b] H; cbn in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H1 H2]. rewrite (tf_eqb_sound x y H1), (IH b H2). reflexivity.
Qed.

Lemma odefault_eqb_sound : ltac2:(tb__ "0|0|
S23S23S16S0S98R2R1A2S4A3S16S23R3R2A3F_;Fd';Fd;").
Proof.
  intros d d' H. destruct d, d'; cbn in H; try discriminate; try reflexivity;
  try (apply Pos.eqb_eq in H; congruence).
  apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.eqb_eq in H1. apply sv_eqb_sound in H2. apply flds_eqb_sound in H3. apply tmpl_eqb_sound in H4. congruence.
Qed.

Lemma fld_okb_sound : ltac2:(tb__ "0|0|
S13S7S13S13A2S16S0SaaR2R1A2S4A3S4eR3R2A2F_;Ff;Fesz;").
Proof.
  intros esz f H. unfold fld_okb in H. unfold fld_ok.
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2.
  repeat (apply Bool.orb_prop in H3; destruct H3 as [H3|H3]); apply Z.eqb_eq in H3; repeat split; lia.
Qed.

Lemma tmpl_equiv_transfer : ltac2:(tb__ "0|1|
S21S1S24A1M0G0S1S94Q40A1A1S16S0S9eS5cR3R2A3S4A3S84S24S45R5R2A2R4A3S84S24S45R6R3A2R4A3F_;F_;Fvals;Fb;Fa;Frho;").
Proof.
  intros rho a. induction a as [|x a IH]; intros [|y b] vals H Ha; cbn in H; try discriminate; [constructor|].
  apply andb_prop in H as [H1 H2]. inversion Ha; subst. constructor; [|apply IH; assumption].
  destruct (tf_eqb_with_sound sv_equiv x y H1) as [E ->].
  apply (sv_equiv_sound rho) in E.
  apply (proj2 (tf_holds_with_expr rho rho vals x (tf_expr y) ltac:(symmetry; exact E))). assumption.
Qed.

Section WithSegs.
Variable segs : list Segment.

Definition cell_abs (rho : valuation) (B : Z) (c : cell) : Z * Z * word := ltac2:(tb__ "0|0|
SbS7S13S13A2S94Q40A1SbS13S13S73VB;S38Vrho;S28Vc;A1A2A2S2eVc;A1A4S26Vrho;S2dVc;A1A2A4").

Lemma cell_abs_inj : ltac2:(tb__ "0|1|
S21S21S13S13S20S20S16S7S7S13S13A2S94Q40A1M0A2SdbR6R4R2A3SdbR5R3R1A3A3S17S16S13S73R5S38R7S28R3A1A2A2S73R4S38R6S28R2A1A2A2A3S17S16S13S2eR3A1S2eR2A1A3S16G0S26R7S2dR3A1A2S26R6S2dR2A1A2A3A2A2F_;Fc2;Fc1;FB2;FB1;Frho2;Frho1;").
Proof using . intros rho1 rho2 B1 B2 c1 c2 E. unfold cell_abs in E. inversion E. repeat split; reflexivity. Qed.

Lemma obj_holds_transfer : ltac2:(tb__ "0|10|
S21S21Sd3S1eS1eS14S3bVsegs;R4A2S16S0S34R2R4A2S4A3S16S13S73S93Q40M0S26R8S27R5A1A2A2M1S37R8R5A2A2S73S93G0S26R7S27R4A1A2A2S37R7R4A2A2A3S16S13S73S93G0S26R9S27R6A1A2A2S3aR9R6A2A2S73G1S3aR8R5A2A2A3S16S14S1S94Q8A1A1F_;S50RaA1S50R9A1A3S20S55S20R1S2fR8A1A3S18S20S20S17S55S20R1S2fRbA1A3M2S16S7S7S13S13A2M3S94G0A1M4A2M5SdbReS93G0S26ReS27RbA1A2A2R1A3M6SdbRdS93G0S26RdS27RaA1A2A2R3A3A3A2Lc1;A2F_;Fc2;S19S17S16S23S2aR8A1M7S4cA3S16S0S36S2aR9A1M8A1S4A3A2S19S17S16S23G7G8A3S17S16S0S52G8A1S2A3S20S55S20R1S2fRaA1A3S18S20S20S17G2S16G5SdbRfS93G0S26RfS27RcA1A2A2R3A3G6A3A2Lc2;A2F_;Fc1;A2A2S18S13S13S18S1dS1dS18S1G3A1M9G9S18S1S24A1MaGaS17S16S23S2aRcA1S46R4R3R2R1A4A3S17S16S0S36S2aRdA1A1S4A3S19S18S1dS1dS18GaGaS17S16S23S2aRfA1S46R6R2R4R1A4A3S17S19S76S93G0S26R11R5A2A2MbS93G0S26R12R2A2A2McA2S17S76GbS73GcZ1A2MdA2S17S76S73S37R12RfA2MeS79R6GdA2A2S3aR12RfA2A2S3eR11R10S73S73S93G0S26R12S27RfA1A2A2GeA2S79R6GcA2A2R4R3A5A2A2A2S1G4A1S84S24S45R13R1A2R2A3S84S24S45R13R2A2R5A3F_;Fvals;A2A2LtmplL;A2LcntL;A2S17S16S13S93G0S26RfR3A2A2Z0MfA3S17S7bGfR4A2S84G3S4eR4A1R2A3A2A2A2A2A2LtmplT;A2LfldsT;A2LcntT;A2LeszT;A2A2A2S33Vsegs;RdRbRaA4S33Vsegs;RdRcRaA4F_;F_;F_;F_;F_;F_;F_;F_;Fn;Fo2;Fo1;Fms;Frho2;Frho1;").
Proof using .
  intros rho1 rho2 ms o1 o2 n Hrom Hwf Elo Ehi Erl HcT Hdf Ho.
  pose proof Ho as (Hb & Hw & Hc & Hd & Hdl).
  set (B1 := bv_unsigned (eval rho1 (ob_base o1))) in *.
  set (B2 := bv_unsigned (eval rho2 (ob_base o2))) in *.
  unfold obj_holds. fold B2. unfold obj_lo_of, obj_hi_of in *.
  set (lo1 := soff rho1 (ob_lo o1)) in *. set (hi1 := soff rho1 (ob_hi o1)) in *.
  set (lo2 := soff rho2 (ob_lo o2)) in *. set (hi2 := soff rho2 (ob_hi o2)) in *.
  pose proof (urange (eval rho2 (ob_base o2))) as HB2. fold B2 in HB2.
  split; [lia|]. split.
  { intros off Hoff Hdw2. replace (B2 + off) with (B1 + (off + (B2 - B1))) by lia. apply Hw; [lia|].
    destruct Hdf as [[_ W1] | [[Hdeq _] | (eszT & cntT & fldsT & tmplT & _ & W1 & _)]]; [exact W1 | rewrite <- Hdeq; exact Hdw2 | exact W1]. }
  split.
  { apply Forall_forall. intros c2 Hin2. destruct (HcT c2 Hin2) as (c1 & Hin1 & E).
    pose proof (proj1 (Forall_forall _ _) Hc c1 Hin1) as (C1 & C2 & C3).
    destruct (cell_abs_inj _ _ _ _ _ _ E) as (Eo & Ew & Ev).
    unfold cell_holds. rewrite <- Ew, <- Ev. split; [lia|]. split; [lia|].
    unfold oaddr in *. fold B2. fold B1 in C3. rewrite <- Eo. exact C3. }
  split.
  { intros off Hoff Hncov.
    assert (Hoff1 : lo1 <= off + (B2 - B1) < hi1) by lia.
    replace (B2 + off) with (B1 + (off + (B2 - B1))) by lia.
    destruct Hdf as [[HdU _] | [(Hdeq & _ & Hsame) | (eszT & cntT & fldsT & tmplT & HdA & _ & _)]].
    - rewrite HdU. cbn. subst B1. eapply (obj_byte_readable segs rho1 ms o1 _ n Hrom Hwf Ho). unfold obj_lo_of, obj_hi_of. lia.
    - rewrite Hdeq.
      assert (Hncov1 : ~ covered rho1 (ob_cells o1) (off + (B2 - B1))).
      { intros Hcov. apply Hncov. unfold covered in *. apply Exists_exists in Hcov as (c1 & Hin1 & Hc1).
        destruct (Hsame c1 Hin1) as (c2 & Hin2 & E). apply Exists_exists. exists c2. split; [exact Hin2|].
        destruct (cell_abs_inj _ _ _ _ _ _ E) as (Eo & Ew & Ev). unfold in_cell in *. rewrite <- Ew. lia. }
      specialize (Hd (off + (B2 - B1)) Hoff1 Hncov1).
      destruct (ob_dflt o1); cbn in Hd |- *; try exact Hd;
      rewrite <- Erl; replace (off - lo2) with (off + (B2 - B1) - lo1) by lia; exact Hd.
    - rewrite HdA. cbn. subst B1. eapply (obj_byte_readable segs rho1 ms o1 _ n Hrom Hwf Ho). unfold obj_lo_of, obj_hi_of. lia. }
  destruct Hdf as [[HdU _] | [(Hdeq & Hna & _) | (eszT & cntT & fldsT & tmplT & HdA & _ & HA)]]; [rewrite HdU; exact I| |].
  - rewrite Hdeq. destruct (ob_dflt o1); cbn in Hdl |- *; try exact I; try (rewrite <- Erl; lia). discriminate Hna.
  - rewrite HdA. cbn [dflt_inv].
    destruct HA as [(cntL & tmplL & HdL & Hle & Htm) | (Hz & Hesz & Hflds)].
    + rewrite HdL in Hdl. cbn [dflt_inv] in Hdl. destruct Hdl as (Q1 & Q2 & Q3 & Q4).
      split; [exact Q1|]. split; [exact Q2|].
      assert (OLD : forall k, 0 <= k < bv_unsigned (eval rho1 cntL) -> elem_holds rho2 ms (B2 + lo2 + eszT * k) fldsT tmplT).
      { intros k Hk. destruct (Q4 k Hk) as (vals & L & F & T).
        exists vals. split; [exact L|]. split; [|apply Htm; exact T].
        intros i f Hi. replace (B2 + lo2 + eszT * k + fst f) with (B1 + lo1 + eszT * k + fst f) by lia. exact (F i f Hi). }
      destruct Hle as [Hle | (Hle & Hfit & Hnew)].
      * assert (HM : eszT * bv_unsigned (eval rho2 cntT) <= eszT * bv_unsigned (eval rho1 cntL)) by (apply Z.mul_le_mono_nonneg_l; lia).
        split; [lia|]. intros k Hk. apply OLD. lia.
      * unfold obj_lo_of, obj_hi_of in Hfit, Hnew. fold lo1 hi1 B1 in Hfit, Hnew. fold lo1 in Hnew.
        assert (HM : eszT * bv_unsigned (eval rho2 cntT) <= eszT * (bv_unsigned (eval rho1 cntL) + 1)) by (apply Z.mul_le_mono_nonneg_l; lia).
        split; [lia|]. intros k Hk.
        destruct (Z.lt_ge_cases k (bv_unsigned (eval rho1 cntL))) as [Hk'|Hk'].
        -- apply OLD. lia.
        -- assert (k = bv_unsigned (eval rho1 cntL)) as -> by lia.
           replace (B2 + lo2) with (B1 + lo1) by lia. exact Hnew.
    + split; [exact Hesz|]. split; [exact Hflds|]. rewrite Hz. split; [lia|]. intros k Hk. lia.
Qed.

Lemma lit_shift_eqb_sound : ltac2:(tb__ "0|0|
S21S21S13S1dS1dS16S0S9cR3R2R1A3S4A3S16S13S38R5R2A2S7dS38R6R3A2R4A2A3F_;FeT;FeL;Fc;Frho2;Frho1;").
Proof using .
  intros rho1 rho2 c eL eT H. unfold lit_shift_eqb in H.
  destruct eL; try discriminate. destruct eT; try discriminate.
  apply Z.eqb_eq in H. rewrite !soff_lit. exact H.
Qed.

Lemma find_fld_cell_spec : ltac2:(tb__ "0|1|
S1S1fA1S1S20A1S1dS13S1dS7S13S13A2S20S16S6S20A1Sa9R7R6R5R4R3R2A6S8S20R1A2A3S17S55S20R2R7A3S17S16S13S2eR2A1SfS13S13R3A3A3S18S1dS1dS17S16S6S7S1dS13A2M0A1S69R9S6aSd7S28R3A1R7A3R6A3S8G0SbS1dS13R1SeS13S13R4A3A4A2A3S16S0S5cR1R5A2S4A3A2Lidx';A2A2A2F_;Fc;Ff;Fidx;Fesz;Flo;Fcells;FfactsL;").
Proof using .
  intros factsL cells lo esz idx f. induction cells as [|c0 rest IH]; intros c H; cbn in H; [discriminate|].
  destruct (c_width c0 =? snd f) eqn:Ew.
  - destruct (lin_decomp factsL (mk_alu ALU_SUB (c_off c0) lo) esz) as [[idx' foff]|] eqn:Hd.
    + destruct ((foff =? fst f) && sv_equiv idx' idx)%bool eqn:E.
      * injection H as <-. apply andb_prop in E as [E1 E2]. apply Z.eqb_eq in E1. apply Z.eqb_eq in Ew. subst foff.
        split; [left; reflexivity|]. split; [exact Ew|]. exists idx'. auto.
      * destruct (IH c H) as (A & B & C). split; [right; exact A|]. auto.
    + destruct (IH c H) as (A & B & C). split; [right; exact A|]. auto.
  - destruct (IH c H) as (A & B & C). split; [right; exact A|]. auto.
Qed.

Lemma arr_cell_offset : ltac2:(tb__ "0|1|
S21S1S1fA1Sd3S1eS14S20S13S1dS13S13S84S1fS25RaA1R9A3S33Vsegs;RbR9R8A4S16S0S34R8R9A2S4A3S55S20R8S2fRaA1A3S16S6S7S1dS13A2M0A1S69RdS6aSd7S28R9A1S2bRbA1A3R8A3S8G0SbS1dS13R7R6A4A2A3S16S13S93Q40S26RfR8A2A2R6A3S76S73S37R10RdA2S79RaR7A2A2S3aR10RdA2A2S16S13S38R11S28RcA1A2S73S73S37R11ReA2S79RbR8A2A2R9A2A3F_;F_;F_;F_;F_;F_;F_;FK;Ffoff;Fidx';Fesz;Fc;Fn;Fo;Fms;Ffacts;Frho;").
Proof using .
  intros rho facts ms o n c esz idx' foff K Hf Ho Hwf Hin Hdec HK Hfit.
  destruct (lin_decomp_sound rho facts _ esz idx' foff Hf Hdec) as (Hesz & Hc & HU).
  pose proof (proj1 Ho) as HB. pose proof (proj1 (Forall_forall _ _) (proj1 (proj2 (proj2 Ho))) c Hin) as (C1 & C2 & _).
  destruct (obj_wf_cell _ _ _ Hwf Hin) as (W1 & _).
  unfold obj_lo_of, obj_hi_of in *.
  assert (E : (soff rho (c_off c) - soff rho (ob_lo o)) mod 2 ^ 64 = (esz * U rho idx' + foff) mod 2 ^ 64).
  { rewrite <- HU. unfold U at 1. rewrite mk_alu_sound, sub_val.
    change (bv_unsigned (eval rho (c_off c))) with (U rho (c_off c)). change (bv_unsigned (eval rho (ob_lo o))) with (U rho (ob_lo o)).
    rewrite <- (soff_mod rho (c_off c)), <- (soff_mod rho (ob_lo o)). rewrite <- Zminus_mod. reflexivity. }
  unfold U in E. rewrite HK in E.
  assert (HKnn : 0 <= esz * K) by (apply Z.mul_nonneg_nonneg; [lia | rewrite <- HK; apply (proj1 (urange _))]).
  rewrite (Z.mod_small (soff rho (c_off c) - soff rho (ob_lo o))) in E by lia.
  rewrite Z.mod_small in E by lia. lia.
Qed.

Lemma elem_xs_spec : ltac2:(tb__ "0|2|
S1S1fA1S1S20A1S1dS13S1dS1S7S13S13A2M0A1S3S0F_;S3S1S1dA1M1S16S6G1A1Sa8R9R8R7R6R5R4R3R2A8S8G1R1A2A3S17S16S3S9S1dR2A2S9G0R5A2A3S3G0S16S6G0A1S58G0R7R2A3S8G0R1A2A3S16S0R7Se5R6R3A2A1S4A3S18S20S20S17S16S6S20A1Sa9RfReRdRcRbR4A6S8S20R1A2A3S16S1dS86S1dR5R7S3dZ0A1A4S72S2Se8Q8S7fSfS13S13R4A3A1A2S2dR1A1A3A3A2Lc;A2F_;F_;Ff;Fjj;A2F_;Fxs;Fj0;Fneed;Ffl;Fidx;Fesz;Flo;Fcells;FfactsL;").
Proof using .
  intros factsL cells lo esz idx. induction fl as [|f rest IH]; intros need j0 xs H; cbn [elem_xs] in H.
  - injection H as <-. split; [reflexivity|]. intros jj f' Hjj. destruct jj; discriminate.
  - destruct (if need j0 then option_map (fun c => mk_ext false (8 * Z.to_N (snd f))%N (c_val c)) (find_fld_cell factsL cells lo esz idx f)
              else Some (SLit 0)) as [x|] eqn:Ex; [|discriminate].
    destruct (elem_xs factsL cells lo esz idx rest need (Datatypes.S j0)) as [xs'|] eqn:Er; [|discriminate].
    injection H as <-. destruct (IH need (Datatypes.S j0) xs' Er) as [L A].
    split; [cbn; rewrite L; reflexivity|].
    intros jj f' Hjj Hneed. destruct jj as [|jj]; cbn [nth]; cbn in Hjj.
    + injection Hjj as <-. rewrite Nat.add_0_r in Hneed. rewrite Hneed in Ex.
      destruct (find_fld_cell factsL cells lo esz idx f) as [c|]; cbn in Ex; [|discriminate].
      injection Ex as <-. exists c. auto.
    + replace (j0 + Datatypes.S jj)%nat with (Datatypes.S j0 + jj)%nat in Hneed by lia. apply A; assumption.
Qed.

Lemma anchor_cell_spec : ltac2:(tb__ "0|2|
S1S1fA1S1S20A1S1dS13S1dS1S7S13S13A2M0A1S20S13S16S6S7S20S13A2M1A1Sa4R8R7R6R5R4R3A6S8G1SbS20S13R2R1A4A2A3S18G0G0S17S55G0R1R5A3S17S16S13SeS13S13R1A3R3A3S16S6S20A1Sa9RaR9R8R7R6R1A6S8S20R4A2A3A2A2Lf;A2F_;Ffoff;Fc;Ffl;Fidx;Fesz;Flo;Fcells;FfactsL;").
Proof using .
  intros factsL cells lo esz idx. induction fl as [|f rest IH]; intros c foff H; cbn in H; [discriminate|].
  destruct (find_fld_cell factsL cells lo esz idx f) as [c0|] eqn:E.
  - injection H as <- <-. exists f. split; [left; reflexivity|]. auto.
  - destruct (IH c foff H) as (f' & Hin & A & B). exists f'. split; [right; exact Hin|]. auto.
Qed.

Lemma elem_checked_sound : ltac2:(tb__ "0|4|
S21Sd3S1eS14S1S1fA1S13S1dS1S7S13S13A2A1S1S24A1M0G0S3bVsegs;R9A2S84S1fS25RbA1R7A3S16S0S34R9RaA2S4A3S33Vsegs;RdRcRbA4S16S23S2aRcA1S46R9R8R7R6A4A3S16S0Sa7RbRdRaR9R8R6A6S4A3S17S76S73S37R10ReA2M1S79RbS73S93Q40M2S26R10RaA2A2M3Z1A2A2A2S3aR10ReA2A2S3eR10RfS73S73S93G2S26R10S27ReA1A2A2G1A2S79RbG3A2A2R9R7A5A2F_;F_;F_;F_;F_;F_;FtmplX;Ftmpl;Fflds;Fcnt;Fesz;FfactsL;Fn;Fo;Fms;Frho;").
Proof using .
  intros rho ms o n factsL esz cnt flds tmpl tmplX Hrom Hf Hwf Ho Hd Hchk.
  pose proof Ho as (HB & HW & HC & HD & HDL). rewrite Hd in HDL. cbn [dflt_inv] in HDL.
  destruct HDL as (Hesz & Hflds & Hfit0 & _). destruct HB as (HB1 & HB2 & HB3 & HB4).
  set (K := bv_unsigned (eval rho cnt)) in *.
  set (b := bv_unsigned (eval rho (ob_base o))) in *.
  unfold elem_checked in Hchk.
  destruct (anchor_cell factsL (ob_cells o) (ob_lo o) esz cnt flds) as [[ca fa]|] eqn:Han; [|discriminate].
  apply andb_prop in Hchk as [Hib Hchk].
  destruct (anchor_cell_spec _ _ _ _ _ _ _ _ Han) as (fa' & Hfa' & <- & Hfca).
  destruct (find_fld_cell_spec _ _ _ _ _ _ _ Hfca) as (HinA & HwA & idxA & HdecA & HeqA).
  pose proof (sv_equiv_sound rho _ _ HeqA) as EidxA.
  pose proof (arr_cell_offset rho factsL ms o n ca esz idxA (fst fa') K Hf Ho Hwf HinA HdecA ltac:(rewrite EidxA; reflexivity) Hfit0) as HoffA.
  pose proof (proj1 (Forall_forall _ _) Hflds fa' Hfa') as FokA. unfold fld_ok in FokA.

  pose proof (in_bounds_sound rho factsL (ob_lo o) (ob_hi o) (mk_addk (c_off ca) (- fst fa')) esz Hf ltac:(lia) Hib) as [F1 F2].
  assert (HKnn : 0 <= esz * K) by (apply Z.mul_nonneg_nonneg; [lia | unfold K; apply (proj1 (urange _))]).
  assert (E0 : soff rho (mk_addk (c_off ca) (- fst fa')) = obj_lo_of rho o + esz * K).
  { rewrite soff_mk_addk; [lia|]. rewrite HoffA. pose proof (soff_range rho (ob_lo o)). pose proof (soff_range rho (ob_hi o)).
    unfold obj_lo_of, obj_hi_of in *. lia. }
  rewrite E0 in F2. unfold obj_lo_of, obj_hi_of in *.
  assert (HFIT : soff rho (ob_lo o) + esz * (K + 1) <= soff rho (ob_hi o)) by lia.
  split; [exact HFIT|].

  set (need := fun j => existsb (tf_mentions j) tmplX) in Hchk.
  destruct (elem_xs factsL (ob_cells o) (ob_lo o) esz cnt flds need 0) as [xs|] eqn:Hxs; [|discriminate].
  destruct (elem_xs_spec _ _ _ _ _ _ _ _ _ Hxs) as [Lxs Xs].

  assert (VALS : forall fl j0, (forall jj f, nth_error fl jj = Some f -> nth_error flds (j0 + jj)%nat = Some f) ->
            exists vals : list word, length vals = length fl
              /\ (forall jj f, nth_error fl jj = Some f ->
                    rd_bytes ms (Z_to_bv 64 (b + soff rho (ob_lo o) + esz * K + fst f)) (Z.to_nat (snd f)) = Some (enc_bytes (Z.to_nat (snd f)) (fldv vals jj))
                    /\ bv_unsigned (fldv vals jj) < 2 ^ (8 * snd f))
              /\ (forall jj f, nth_error fl jj = Some f -> need (j0 + jj)%nat = true ->
                    eval rho (nth (j0 + jj)%nat xs (SLit 0)) = fldv vals jj)).
  { induction fl as [|f rest IH]; intros j0 Hsub.
    - exists []. split; [reflexivity|]. split; intros jj f' Hjj; destruct jj; discriminate.
    - destruct (IH (Datatypes.S j0) ltac:(intros jj f' Hjj; replace (Datatypes.S j0 + jj)%nat with (j0 + Datatypes.S jj)%nat by lia; apply Hsub; exact Hjj))
        as (vals & L & R & XV).
      pose proof (Hsub 0%nat f eq_refl) as Hf0. rewrite Nat.add_0_r in Hf0.
      pose proof (proj1 (Forall_forall _ _) Hflds f (nth_error_In _ _ Hf0)) as Fok. unfold fld_ok in Fok. destruct Fok as (G0 & G1 & G2).

      destruct (obj_bytes_readable segs rho ms o (soff rho (ob_lo o) + esz * K + fst f) (Z.to_nat (snd f)) n Hrom Hwf Ho
                  ltac:(unfold obj_lo_of; lia) ltac:(unfold obj_hi_of; rewrite Z2Nat.id by lia; lia)) as (bs & Hrd & Hlen).
      fold b in Hrd.

      assert (CH : exists v : word, rd_bytes ms (Z_to_bv 64 (b + soff rho (ob_lo o) + esz * K + fst f)) (Z.to_nat (snd f)) = Some (enc_bytes (Z.to_nat (snd f)) v)
                     /\ bv_unsigned v < 2 ^ (8 * snd f)
                     /\ (need j0 = true -> eval rho (nth j0 xs (SLit 0)) = v)).
      { destruct (need j0) eqn:Hn.
        - destruct (Xs j0 f Hf0 Hn) as (c & Hfc & Hnth).
          destruct (find_fld_cell_spec _ _ _ _ _ _ _ Hfc) as (Hin & Hw & idx' & Hdec & Heq).
          pose proof (sv_equiv_sound rho _ _ Heq) as Eidx.
          pose proof (arr_cell_offset rho factsL ms o n c esz idx' (fst f) K Hf Ho Hwf Hin Hdec ltac:(rewrite Eidx; reflexivity) Hfit0) as Hoffc.
          unfold obj_lo_of in Hoffc.
          destruct (obj_wf_cell _ _ _ Hwf Hin) as (W1 & W2 & W3 & W4).
          pose proof (obj_read_cell segs rho ms o c (soff rho (c_off c)) (snd f) Ho Hin W2 ltac:(lia) ltac:(rewrite Hw; lia) ltac:(lia)) as Rc.
          rewrite Z.sub_diag, Z.mul_0_r, Z.shiftr_0_r, Z_to_bv_bv_unsigned in Rc. unfold oaddr in Rc. rewrite Hoffc in Rc. fold b in Rc.
          exists (ext_low false (8 * N.of_nat (Z.to_nat (snd f)))%N (eval rho (c_val c))).
          split; [|split].
          + rewrite enc_bytes_low by lia.
            replace (b + soff rho (ob_lo o) + esz * K + fst f) with (b + (soff rho (ob_lo o) + esz * K + fst f)) by lia. exact Rc.
          + rewrite ext_low_false_unsigned by lia. rewrite Z2Nat.id by lia. apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia.
          + intros _. rewrite Hnth, mk_ext_sound.
            replace (8 * Z.to_N (snd f))%N with (8 * N.of_nat (Z.to_nat (snd f)))%N by lia. reflexivity.
        - exists (le_bytes_to_word bs). split; [|split].
          + rewrite (enc_bytes_le_word _ _ Hlen ltac:(lia)).
            replace (b + soff rho (ob_lo o) + esz * K + fst f) with (b + (soff rho (ob_lo o) + esz * K + fst f)) by lia. exact Hrd.
          + unfold le_bytes_to_word. rewrite Z_to_bv_unsigned.
            pose proof (bytes_le_to_Z_bound bs) as Bb. rewrite Hlen, Z2Nat.id in Bb by lia.
            unfold bv_wrap. rewrite two64. rewrite Z.mod_small; [lia|]. split; [lia|].
            eapply Z.lt_le_trans; [exact (proj2 Bb)|]. apply Z.pow_le_mono_r; lia.
          + intros; discriminate. }
      destruct CH as (v & Hv1 & Hv2 & Hv3).
      exists (v :: vals). split; [cbn; rewrite L; reflexivity|]. split.
      + intros jj f' Hjj. destruct jj as [|jj]; cbn in Hjj.
        * injection Hjj as <-. unfold fldv. cbn [nth]. auto.
        * unfold fldv. cbn [nth]. exact (R jj f' Hjj).
      + intros jj f' Hjj Hn. destruct jj as [|jj]; cbn in Hjj.
        * injection Hjj as <-. rewrite Nat.add_0_r in Hn |- *. unfold fldv. cbn [nth]. apply Hv3. exact Hn.
        * unfold fldv. cbn [nth]. replace (j0 + Datatypes.S jj)%nat with (Datatypes.S j0 + jj)%nat in Hn |- * by lia. exact (XV jj f' Hjj Hn). }
  destruct (VALS flds 0%nat ltac:(intros jj f H; exact H)) as (vals & Lv & Rv & Xv).
  exists vals. split; [exact Lv|]. split.
  { intros i f Hi. fold b. exact (Rv i f Hi). }
  apply Forall_forall. intros t Hin.
  pose proof (proj1 (forallb_forall _ _) Hchk t Hin) as Hpt.
  apply (tf_inst_complete rho xs).
  - intros j Hmj.
    destruct (Nat.lt_ge_cases j (length flds)) as [Hjl|Hjl].
    + destruct (nth_error flds j) as [f|] eqn:Hj; [|exfalso; exact (proj2 (nth_error_Some flds j) Hjl Hj)].
      apply (Xv j f Hj). unfold need. apply existsb_exists. exists t. auto.
    + rewrite nth_overflow by (rewrite Lxs; lia). unfold fldv. rewrite nth_overflow by lia. reflexivity.
  - apply Forall_forall. intros p Hp. eapply prove_sprop_sound; [exact Hf|]. exact (proj1 (forallb_forall _ _) Hpt p Hp).
Qed.

Lemma elem_holds_unsubst : ltac2:(tb__ "0|0|
S21S88Sd3S13S1S7S13S13A2A1S1S24A1S3eR6R4R3R2S85S24S24S8fR5A1R1A4A5S3eS89R7R6A2R5R4R3R2A5F_;Ftmpl;Fflds;Fa0;Fms;Fs;Frho;").
Proof using .
  intros rho s ms a0 flds tmpl (vals & L & F & T). exists vals. split; [exact L|]. split; [exact F|].
  apply Forall_forall. intros t Hin.
  apply (proj1 (tf_holds_with_expr rho (rho_sub rho s) vals t _ (eval_subst rho s (tf_expr t)))).
  apply (proj1 (Forall_forall _ _) T (tf_subst s t)). apply in_map. exact Hin.
Qed.

Lemma obj_entailed_sound : ltac2:(tb__ "0|1|
S21S88Sd3S1eS1eS14S1S1fA1S3bVsegs;R5A2S84S1fS25R8A1R2A3S16S0S34R4R6A2S4A3S33Vsegs;RaR8R7A4S16S0Sa2R5R8S8aRaR7A2A3S4A3S17S33Vsegs;S89RcRbA2M0RaR8A4S16S7S13S13A2S31G0R8A2S31RcR9A2A3A2F_;F_;F_;F_;F_;FfactsL;Fn;FoT;FoL;Fms;Fs;Frho;").
Proof using .
  intros rho s ms oL oT n factsL Hrom Hfacts Hwf Ho He.
  unfold obj_entailed in He. apply lazy_orb_prop in He.

  assert (MAIN : forall (c : Z) (ceq : cell -> cell -> bool),
    bv_unsigned (eval rho (ob_base (obj_subst s oT))) = bv_unsigned (eval rho (ob_base oL)) + c ->
    soff rho (ob_lo (obj_subst s oT)) = soff rho (ob_lo oL) - c ->
    soff rho (ob_hi (obj_subst s oT)) = soff rho (ob_hi oL) - c ->
    (forall cL cT, ceq cL cT = true ->
       soff rho (c_off cT) = soff rho (c_off cL) - c /\ c_width cT = c_width cL /\ eval rho (c_val cT) = eval rho (c_val cL)) ->
    cells_entailed factsL ceq oL (obj_subst s oT) = true ->
    obj_holds segs (rho_sub rho s) ms oT /\ obj_range (rho_sub rho s) oT = obj_range rho oL).
  { intros c ceq EB Elo Ehi Hceq Hce.
    unfold obj_subst in EB, Elo, Ehi, Hce. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt] in EB, Elo, Ehi, Hce.
    rewrite eval_subst in EB. rewrite soff_subst in Elo, Ehi.
    unfold cells_entailed in Hce. cbn [ob_cells ob_dflt] in Hce. apply andb_prop in Hce as [Hincl Hdf].
    assert (CA : forall cL c2, ceq cL (cell_subst s c2) = true ->
              cell_abs rho (bv_unsigned (eval rho (ob_base oL))) cL
              = cell_abs (rho_sub rho s) (bv_unsigned (eval (rho_sub rho s) (ob_base oT))) c2).
    { intros cL c2 Hq. destruct (Hceq _ _ Hq) as (Qo & Qw & Qv). cbn [cell_subst c_off c_width c_val] in Qo, Qw, Qv.
      rewrite soff_subst in Qo. rewrite eval_subst in Qv. unfold cell_abs. rewrite EB, Qo, <- Qw, <- Qv. f_equal. f_equal. lia. }
    assert (HcT : forall c2, In c2 (ob_cells oT) -> exists c1, In c1 (ob_cells oL)
              /\ cell_abs rho (bv_unsigned (eval rho (ob_base oL))) c1
                 = cell_abs (rho_sub rho s) (bv_unsigned (eval (rho_sub rho s) (ob_base oT))) c2).
    { intros c2 Hin2.
      pose proof (proj1 (forallb_forall _ _) Hincl (cell_subst s c2) ltac:(apply in_map; exact Hin2)) as X.
      apply existsb_exists in X as (c1 & Hin1 & Hq). exists c1. split; [exact Hin1|]. apply CA. exact Hq. }
    split.
    - apply (obj_holds_transfer rho (rho_sub rho s) ms oL oT n Hrom Hwf).
      + unfold obj_lo_of. rewrite EB, Elo. lia.
      + unfold obj_hi_of. rewrite EB, Ehi. lia.
      + reflexivity.
      + exact HcT.
      + destruct (ob_dflt oT) eqn:EdT; [left; split; [reflexivity | exact Hdf] | right; left | right; left | right; left | right; left | right; right];
          try (cbn [dflt_subst] in Hdf; apply andb_prop in Hdf as [Hdeq Hback]; apply odefault_eqb_sound in Hdeq;
           split; [symmetry; exact Hdeq|];
           split; [rewrite Hdeq; reflexivity|];
           intros c1 Hin1;
           pose proof (proj1 (forallb_forall _ _) Hback c1 Hin1) as X;
           apply existsb_exists in X as (c2' & Hin2' & Hq);
           apply in_map_iff in Hin2' as (c2 & <- & Hin2);
           exists c2; split; [exact Hin2|]; apply CA; exact Hq).

        cbn [dflt_subst] in Hdf. unfold arr_entailed in Hdf. apply andb_prop in Hdf as [Hdw Harr].
        exists esz, cnt, flds, tmpl. split; [reflexivity|]. split; [exact Hdw|].
        apply Bool.orb_prop in Harr as [Harr|Harr].
        * left. destruct (ob_dflt oL) as [| | | | |eszL cntL fldsL tmplL] eqn:EdL; try discriminate.
          apply andb_prop in Harr as [Harr Hcase]. apply andb_prop in Harr as [Harr Htm]. apply andb_prop in Harr as [Hee Hfl].
          apply Z.eqb_eq in Hee. apply flds_eqb_sound in Hfl. subst eszL fldsL.
          exists cntL, tmplL. split; [reflexivity|]. split.
          -- apply Bool.orb_prop in Hcase as [Hul|Hext].
             ++ left. pose proof (uleq_sound rho factsL (sv_subst s cnt) 0 cntL Hfacts Hul) as U0. unfold U in U0. rewrite eval_subst in U0. lia.
             ++ right. apply andb_prop in Hext as [Hext Hchk]. apply andb_prop in Hext as [Hu1 Hu2].
                pose proof (uleq_sound rho factsL (sv_subst s cnt) 0 (mk_addk cntL 1) Hfacts Hu1) as U1.
                pose proof (uleq_sound rho factsL cntL 1 (mk_addk cntL 1) Hfacts Hu2) as U2.
                unfold U in U1, U2. rewrite eval_subst in U1.
                rewrite mk_addk_sound, bv_add_unsigned, Z_to_bv_unsigned in U1, U2. unfold bv_wrap in U1, U2. rewrite two64 in U1, U2.
                pose proof (urange (eval rho cntL)) as HcL.
                assert (NW : (bv_unsigned (eval rho cntL) + 1 mod 2 ^ 64) mod 2 ^ 64 = bv_unsigned (eval rho cntL) + 1).
                { change (1 mod 2 ^ 64) with 1.
                  destruct (Z.lt_ge_cases (bv_unsigned (eval rho cntL) + 1) (2 ^ 64)); [apply Z.mod_small; lia|].
                  exfalso. change (1 mod 2 ^ 64) with 1 in U2.
                  replace (bv_unsigned (eval rho cntL) + 1) with (2 ^ 64) in U2 by lia. rewrite Z.mod_same in U2 by lia. lia. }
                rewrite NW in U1.
                destruct (elem_checked_sound rho ms oL n factsL esz cntL flds tmplL (map (tf_subst s) tmpl) Hrom Hfacts Hwf Ho EdL Hchk) as [FIT EL].
                split; [lia|]. split; [exact FIT|]. apply elem_holds_unsubst. exact EL.
          -- intros vals Hv. pose proof (tmpl_equiv_transfer rho _ _ vals Htm Hv) as X.
             apply Forall_forall. intros t Hin.
             apply (proj1 (tf_holds_with_expr rho (rho_sub rho s) vals t _ (eval_subst rho s (tf_expr t)))).
             apply (proj1 (Forall_forall _ _) X (tf_subst s t)). apply in_map. exact Hin.
        * right. apply andb_prop in Harr as [Harr Hul]. apply andb_prop in Harr as [Hee Hfl].
          apply Z.ltb_lt in Hee. pose proof (uleq_sound rho factsL (sv_subst s cnt) 0 (SLit 0) Hfacts Hul) as U0.
          unfold U in U0. rewrite eval_subst in U0. cbn [eval] in U0. rewrite Z_to_bv_unsigned in U0. change (bv_wrap 64 0) with 0 in U0.
          pose proof (urange (eval (rho_sub rho s) cnt)).
          split; [lia|]. split; [exact Hee|]. apply Forall_forall. intros f Hf. apply fld_okb_sound. exact (proj1 (forallb_forall _ _) Hfl f Hf).
      + exact Ho.
    - unfold obj_range, obj_lo_of, obj_hi_of. rewrite EB, Elo, Ehi. f_equal; lia. }
  destruct He as [He | He].
  -
    unfold obj_entailed_same in He.
    apply lazy_andb_prop in He as [Hba He]. apply lazy_andb_prop in He as [Hlo He]. apply lazy_andb_prop in He as [Hhi Hce].
    apply (sv_equiv_sound rho) in Hba. apply (sv_equiv_sound rho) in Hlo. apply (sv_equiv_sound rho) in Hhi.
    apply (MAIN 0 cell_equiv); [rewrite <- Hba; lia | unfold soff; rewrite <- Hlo; lia | unfold soff; rewrite <- Hhi; lia | | exact Hce].
    intros cL cT Hq. unfold cell_equiv in Hq.
    apply lazy_andb_prop in Hq as [Hqo Hq]. apply lazy_andb_prop in Hq as [Hqw Hqv].
    apply (sv_equiv_sound rho) in Hqo. apply Z.eqb_eq in Hqw. apply (sv_equiv_sound rho) in Hqv.
    unfold soff. rewrite Hqo, Hqw, Hqv. repeat split; lia.
  -
    unfold obj_entailed_shift in He.
    destruct (same_atoms (ob_base (obj_subst s oT)) (ob_base oL)) as [c|] eqn:Hsa; [|discriminate].
    apply lazy_andb_prop in He as [Hlo He]. apply lazy_andb_prop in He as [Hhi He].
    destruct (itv0 factsL (ob_base oL)) as [l h] eqn:Hitv.
    apply lazy_andb_prop in He as [He Hce].
    apply andb_prop in He as [He Hlh]. apply andb_prop in He as [Hl Hh].
    apply Z.leb_le in Hl. apply Z.ltb_lt in Hh. apply Z.leb_le in Hlh.
    apply (MAIN c (cell_shift_eqb c)).
    + exact (same_atoms_exact0 rho factsL _ _ c l h Hfacts Hsa Hitv Hl Hh).
    + exact (lit_shift_eqb_sound rho rho c _ _ Hlo).
    + exact (lit_shift_eqb_sound rho rho c _ _ Hhi).
    + intros cL cT Hq. unfold cell_shift_eqb in Hq.
      apply lazy_andb_prop in Hq as [Hoff Hq]. apply lazy_andb_prop in Hq as [Hw Hv].
      apply Z.eqb_eq in Hw. apply sv_eqb_sound in Hv.
      split; [exact (lit_shift_eqb_sound rho rho c _ _ Hoff) | split; [symmetry; exact Hw | rewrite Hv; reflexivity]].
    + exact Hce.
Qed.

Lemma find_entailed_spec : ltac2:(tb__ "0|0|
S1S1fA1S1S1eA1S1eS3S3S16S6S3A1Sb9R5R4R3R2A4S8S3R1A2A3S18S1eS1eS17Sd9R4R3A2S17S16S6S1eA1S58S1eR6Se6R3R4A2A3S8S1eR1A2A3S16S0Sa2R7R1R5A3S4A3A2A2LoL;A2F_;Fn;Fn0;FoT;FobjsL;FfactsL;").
Proof using .
  induction objsL as [|o t IH]; intros oT n0 n H; cbn in H; [discriminate|].
  destruct (obj_entailed factsL o oT) eqn:He.
  - injection H as <-. exists o. rewrite Nat.sub_diag. cbn. auto.
  - destruct (IH oT (S n0) n H) as (oL & Hle & Hnth & HeL).
    exists oL. split; [lia|]. split; [|exact HeL].
    replace (n - n0)%nat with (S (n - S n0))%nat by lia. cbn. exact Hnth.
Qed.

Lemma witnesses_length : ltac2:(tb__ "0|2|
S1S1fA1S1S1eA1M0G0S1S3A1M1S16S6G1A1S9fR4R3R2A3S8G1R1A2A3S16S3S9S3R2A2S9S1eR3A2A3F_;Fns;FobjsT;FobjsL;FfactsL;").
Proof using .
  induction objsT as [|oT t IH]; intros ns H; cbn in H.
  - injection H as <-. reflexivity.
  - destruct (find_entailed factsL objsL oT 0) as [n|]; [|discriminate].
    destruct (witnesses factsL objsL t) as [ns'|] eqn:Hw; [|discriminate].
    injection H as <-. cbn. f_equal. apply IH. reflexivity.
Qed.

Lemma witnesses_spec : ltac2:(tb__ "0|3|
S1S1fA1S1S1eA1M0G0S1S3A1M1S3S1eS16S6G1A1S9fR6R5R4A3S8G1R3A2A3S16S6S1eA1M2S58S1eR5R3A3S8S1eR2A2A3S18S3S3S18S1eS1eS17S16S6S3A1S58S3R7R6A3S8S3R2A2A3S17S16G2S58S1eR9R2A3S8S1eR1A2A3S16S0Sa2RaR1R5A3S4A3A2A2LoL;A2Ln;A2F_;F_;FoT;Fi;Fns;FobjsT;FobjsL;FfactsL;").
Proof using .
  induction objsT as [|o t IH]; intros ns i oT H Hi; cbn in H.
  - destruct i; discriminate.
  - destruct (find_entailed factsL objsL o 0) as [n|] eqn:Hf; [|discriminate].
    destruct (witnesses factsL objsL t) as [ns'|] eqn:Hw; [|discriminate].
    injection H as <-.
    destruct i as [|i'].
    + cbn in Hi. injection Hi as <-.
      destruct (find_entailed_spec factsL objsL o 0 n Hf) as (oL & _ & Hnth & He).
      rewrite Nat.sub_0_r in Hnth. exists n, oL. cbn. auto.
    + cbn in Hi. destruct (IH ns' i' oT eq_refl Hi) as (n' & oL & H1 & H2 & H3).
      exists n', oL. cbn. auto.
Qed.

Lemma memN_In : ltac2:(tb__ "0|0|
S3S1S3A1S1bS16S0SbbR2R1A2S4A3S55S3R2R1A3A2Fl;Fn;").
Proof using .
  intros n l. induction l as [|x t IH]; cbn.
  - split; [discriminate | tauto].
  - rewrite Bool.orb_true_iff, Nat.eqb_eq, IH. split; intros [H|H]; auto.
Qed.

Lemma nodupN_NoDup : ltac2:(tb__ "0|0|
S1S3A1S16S0S99R1A1S4A3S59S3R2A2F_;Fl;").
Proof using .
  induction l as [|x t IH]; cbn; intros H; [constructor|].
  apply andb_prop in H as [H1 H2]. constructor; [|apply IH; exact H2].
  intros Hin. assert (Hm : memN x t = true) by (apply memN_In; exact Hin). rewrite Hm in H1. discriminate.
Qed.

Lemma ranges_disjoint_sym : ltac2:(tb__ "0|1|
S7S13S13A2M0G0S40R2R1A2S40R2R3A2F_;Fr2;Fr1;").
Proof using . intros r1 r2 H. unfold ranges_disjoint in *. tauto. Qed.

Lemma pairwise_disjoint_nth : ltac2:(tb__ "0|2|
S21S1S1eA1S1bS4fR2R1A2S3S3S1eS1eSd8R4R3A2S16S6S1eA1M0S58S1eR6R5A3S8S1eR3A2M1A3S16G0S58S1eR7R5A3G1A3S40S31R9R5A2S31R9R4A2A2F_;F_;F_;Foj;Foi;Fj;Fi;A2Fobjs;Frho;").
Proof using .
  intros rho objs. induction objs as [|o t IH]; cbn.
  - split; [|tauto]. intros _ i j oi oj _ Hi. destruct i; discriminate.
  - split.
    + intros [Hhd Htl] i j oi oj Hij Hi Hj.
      destruct i as [|i'].
      * cbn in Hi. injection Hi as <-. destruct j as [|j']; [lia|]. cbn in Hj.
        apply (proj1 (Forall_forall _ _) Hhd). eapply nth_error_In; eauto.
      * destruct j as [|j']; [lia|]. cbn in Hi, Hj.
        apply (proj1 IH Htl i' j' oi oj); auto. lia.
    + intros H. split.
      * apply Forall_forall. intros o' Hin. apply In_nth_error in Hin as [j Hj].
        apply (H 0%nat (S j) o o'); auto. lia.
      * apply (proj2 IH). intros i j oi oj Hij Hi Hj. apply (H (S i) (S j) oi oj); auto. lia.
Qed.

Lemma NoDup_nth_error_inj : ltac2:(tb__ "0|1|
S1S3A1S3S3S3S59S3R4A2S16S6S3A1M0S58S3R5R4A3S8S3R2A2A3S16G0S58S3R6R4A3S8S3R3A2A3S16S3R6R5A3F_;F_;F_;Fx;Fj;Fi;Fl;").
Proof using .
  intros l i j x Hnd Hi Hj.
  apply (proj1 (List.NoDup_nth_error l) Hnd i j).
  - apply (proj1 (nth_error_Some l i)). rewrite Hi. discriminate.
  - rewrite Hi, Hj. reflexivity.
Qed.

Lemma nodup_indices_onto : ltac2:(tb__ "0|0|
S1S3A1S3S3S59S3R3A2S16S3S9S3R4A2R3A3S3S55S3R1R6A3Sd8R2R6A2F_;Fn;Sd8R4R5A2S55S3R5R7A3F_;F_;F_;F_;Fk;Fm;Fns;").
Proof using .
  intros ns m k Hnd Hlen Hlt Hk.
  apply (List.NoDup_length_incl Hnd (l' := seq 0 m)).
  - rewrite length_seq. lia.
  - intros n Hin. apply in_seq. specialize (Hlt n Hin). lia.
  - apply in_seq. lia.
Qed.

Lemma objs_entailed_sound : ltac2:(tb__ "0|1|
S21S88Sd3S1S1eA1M0G0S14S1S1fA1S3bVsegs;R5A2S84S1fS25R8A1R2A3S16S0S56S1eS34R4A1R6A3S4A3S47Vsegs;RaR7R8A4S16S0Sa3R5R8S85S1eS1eS8aRaA1R7A4A3S4A3S47Vsegs;S89RcRbA2R8RaA4F_;F_;F_;F_;F_;FfactsL;Fn;FobjsT;FobjsL;Fms;Fs;Frho;").
Proof using .
  intros rho s ms objsL objsT n factsL Hrom Hfacts Hwf (Hall & Hpd & Hfr) He.
  unfold objs_entailed in He. apply lazy_andb_prop in He as [_ He].
  destruct (witnesses factsL objsL (map (obj_subst s) objsT)) as [ns|] eqn:Hw; [|discriminate].
  apply andb_prop in He as [Hnd Hlen]. apply nodupN_NoDup in Hnd. apply Nat.eqb_eq in Hlen.
  rewrite length_map in Hlen.
  pose proof (witnesses_length _ _ _ _ Hw) as Hnslen. rewrite length_map in Hnslen.

  assert (W : forall i oT, nth_error objsT i = Some oT ->
            exists k oL, nth_error ns i = Some k /\ nth_error objsL k = Some oL
              /\ obj_holds segs (rho_sub rho s) ms oT
              /\ obj_range (rho_sub rho s) oT = obj_range rho oL).
  { intros i oT Hi.
    destruct (witnesses_spec factsL objsL (map (obj_subst s) objsT) ns i (obj_subst s oT) Hw) as (k & oL & H1 & H2 & H3).
    { rewrite nth_error_map, Hi. reflexivity. }
    exists k, oL. split; [exact H1|]. split; [exact H2|].
    eapply obj_entailed_sound; eauto.
    - apply (proj1 (forallb_forall _ _) Hwf). eapply nth_error_In; eauto.
    - apply (proj1 (Forall_forall _ _) Hall). eapply nth_error_In; eauto. }
  split; [|split].
  - apply Forall_forall. intros oT Hin. apply In_nth_error in Hin as [i Hi].
    destruct (W i oT Hi) as (k & oL & _ & _ & Ho & _). exact Ho.
  - apply pairwise_disjoint_nth. intros i j oi oj Hij Hi Hj.
    destruct (W i oi Hi) as (ki & oLi & Hki & HLi & _ & ->).
    destruct (W j oj Hj) as (kj & oLj & Hkj & HLj & _ & ->).
    assert (Hne : ki <> kj).
    { intros Heq. subst kj. pose proof (NoDup_nth_error_inj ns i j ki Hnd Hki Hkj). lia. }
    destruct (Nat.lt_ge_cases ki kj).
    + exact (proj1 (pairwise_disjoint_nth rho objsL) Hpd ki kj oLi oLj ltac:(lia) HLi HLj).
    + apply ranges_disjoint_sym.
      exact (proj1 (pairwise_disjoint_nth rho objsL) Hpd kj ki oLj oLi ltac:(lia) HLj HLi).
  - intros a Hout. cbn. apply Hfr.
    apply Forall_forall. intros oL Hin. apply In_nth_error in Hin as [k Hk].
    assert (Hkin : In k ns).
    { apply (nodup_indices_onto ns (length objsL) k Hnd ltac:(lia)).
      - intros n0 Hn0. apply In_nth_error in Hn0 as [i Hi].
        assert (Hi' : (i < length objsT)%nat).
        { rewrite <- Hnslen. apply (proj1 (nth_error_Some ns i)). rewrite Hi. discriminate. }
        destruct (nth_error objsT i) as [oT|] eqn:HoT.
        2:{ exfalso. apply (proj2 (nth_error_Some objsT i) Hi'). exact HoT. }
        destruct (W i oT HoT) as (k' & oL' & Hk' & HL' & _).
        rewrite Hi in Hk'. injection Hk' as <-.
        apply (proj1 (nth_error_Some objsL n0)). rewrite HL'. discriminate.
      - apply (proj1 (nth_error_Some objsL k)). rewrite Hk. discriminate. }
    apply In_nth_error in Hkin as [i Hi].
    assert (Hi' : (i < length objsT)%nat).
    { rewrite <- Hnslen. apply (proj1 (nth_error_Some ns i)). rewrite Hi. discriminate. }
    destruct (nth_error objsT i) as [oT|] eqn:HoT.
    2:{ exfalso. apply (proj2 (nth_error_Some objsT i) Hi'). exact HoT. }
    destruct (W i oT HoT) as (k' & oL' & Hk' & HL' & _ & Hrange).
    rewrite Hi in Hk'. injection Hk' as <-. rewrite Hk in HL'. injection HL' as <-.
    pose proof (proj1 (Forall_forall _ _) Hout oT ltac:(eapply nth_error_In; eauto)) as Ha.
    lazy beta zeta in Ha. rewrite Hrange in Ha. lazy beta zeta. exact Ha.
Qed.

Theorem entails_sound : ltac2:(tb__ "0|0|
S22S22S88S21S7S1S91A1Se0A2S16S0S97R5R4R3A3S4A3S32Vsegs;R3R6R2A4S32Vsegs;S89R4R5A2R6R3A4F_;F_;Fw;Frho;Fs;FT;FL;").
Proof using .
  intros L T s rho [tr [ms md]] He Hsm.
  rewrite entails_eq in He. unfold entails_ref in He.
  apply andb_prop in He as [He Hfacts]. apply andb_prop in He as [He Hobjs].
  apply andb_prop in He as [He Hresv]. apply andb_prop in He as [He Hfcsr].
  apply andb_prop in He as [He Hfregs]. apply andb_prop in He as [He Hregs].
  apply andb_prop in He as [HswfT Hpc]. apply Z.eqb_eq in Hpc.
  pose proof Hsm as (Hswf & Hpc' & Hpend & Hhalt & Hrom & Hro & Hr & Hf & Hc & Hv & Hm & Hfa).
  cbn [fst snd cfg_ms cfg_model] in *.
  unfold smatch. cbn [fst snd cfg_ms cfg_model].
  split; [exact HswfT|]. split; [rewrite <- Hpc; exact Hpc'|].
  split; [exact Hpend|]. split; [exact Hhalt|]. split; [exact Hrom|]. split; [exact Hro|].
  split.
  { intros r Hr0. rewrite (Hr r Hr0).
    pose proof (all_regs_eqb_spec 32 _ (bv_unsigned r) Hregs ltac:(pose proof (regZ_range r); unfold regZ in *; lia)) as E.
    cbn beta in E. apply orb_prop in E. destruct E as [E|E]; [apply Z.eqb_eq in E; lia|].
    rewrite (sv_equiv_sound rho _ _ E). apply eval_subst. }
  split.
  { intros r. rewrite (Hf r).
    pose proof (all_regs_eqb_spec 32 _ (bv_unsigned r) Hfregs ltac:(pose proof (regZ_range r); unfold regZ in *; lia)) as E.
    cbn beta in E. rewrite (sv_equiv_sound rho _ _ E). apply eval_subst. }
  split.
  { unfold sfcsr_entailed in Hfcsr. destruct (ss_fcsr L), (ss_fcsr T); try discriminate.
    - exact Hc.
    - cbn in Hc |- *. rewrite Hc. rewrite (sv_equiv_sound rho _ _ Hfcsr), eval_subst. reflexivity. }
  split.
  { unfold resv_entailed in Hresv. unfold resv_match in *.
    destruct (ss_resv L), (ss_resv T); try discriminate; destruct (ms_resv ms); try exact Hv; try contradiction.
    rewrite Hv. rewrite (sv_equiv_sound rho _ _ Hresv), eval_subst. reflexivity. }
  split.
  { eapply objs_entailed_sound; eauto. apply swf_objs. exact Hswf. }
  apply Forall_forall. intros p Hin. apply lazy_orb_prop in Hfacts as [Hfacts|Hfacts].
  - eapply fact_entailed_d_sound; [exact Hfa | apply ctx0_dg_ok; exact Hfa |].
    apply (proj1 (forallb_forall _ _) Hfacts). exact Hin.
  - eapply fact_entailed_d_sound; [exact Hfa | apply mk_dig_ok; exact Hfa |].
    apply (proj1 (forallb_forall _ _) Hfacts). exact Hin.
Qed.

Lemma objs_entailed_ranges : ltac2:(tb__ "0|1|
S21S88Sd3S1S1eA1M0G0S14S1S1fA1S3bVsegs;R5A2S84S1fS25R8A1R2A3S16S0S56S1eS34R4A1R6A3S4A3S47Vsegs;RaR7R8A4S16S0Sa3R5R8S85S1eS1eS8aRaA1R7A4A3S4A3S1eS55S1eR1R9A3S18S1eS1eS17S55S1eR1RcA3S16S7S13S13A2S31S89RfReA2R3A2S31RfR1A2A3A2LoL;A2F_;FoT;F_;F_;F_;F_;F_;FfactsL;Fn;FobjsT;FobjsL;Fms;Fs;Frho;").
Proof using .
  intros rho s ms objsL objsT n factsL Hrom Hfacts Hwf (Hall & Hpd & Hfr) He oT HinT.
  unfold objs_entailed in He. apply lazy_andb_prop in He as [_ He].
  destruct (witnesses factsL objsL (map (obj_subst s) objsT)) as [ns|] eqn:Hw; [|discriminate].
  apply In_nth_error in HinT as [i Hi].
  destruct (witnesses_spec factsL objsL (map (obj_subst s) objsT) ns i (obj_subst s oT) Hw) as (k & oL & H1 & H2 & H3).
  { rewrite nth_error_map, Hi. reflexivity. }
  exists oL. split; [eapply nth_error_In; exact H2|].
  eapply (proj2 (obj_entailed_sound rho s ms oL oT n factsL Hrom Hfacts _ _ H3)).
  Unshelve.
  - apply (proj1 (forallb_forall _ _) Hwf). eapply nth_error_In; eauto.
  - apply (proj1 (Forall_forall _ _) Hall). eapply nth_error_In; eauto.
Qed.

Lemma entails_ranges : ltac2:(tb__ "0|1|
S22S22S88S21S1S91A1M0Sd3S92S16S0S97R7R6R5A3S4A3S32Vsegs;R5R8SbG0Se0R4Se1R3R2A2A4A4S1eS55S1eR1S29R9A1A3S18S1eS1eS17S55S1eR1S29RcA1A3S16S7S13S13A2S31S89R9RaA2R3A2S31R9R1A2A3A2LoL;A2F_;FoT;F_;F_;Fmd;Fms;Ftr;Frho;Fs;FT;FL;").
Proof using .
  intros L T s rho tr ms md He Hsm.
  rewrite entails_eq in He. unfold entails_ref in He.
  apply andb_prop in He as [He Hfacts]. apply andb_prop in He as [He Hobjs].
  pose proof Hsm as (Hswf & _ & _ & _ & Hrom & _ & _ & _ & _ & _ & Hm & Hfa).
  cbn [fst snd cfg_ms cfg_model] in *.
  eapply objs_entailed_ranges; [exact Hrom | exact Hfa | apply swf_objs; exact Hswf | exact Hm | exact Hobjs].
Qed.

Lemma SP_entails : ltac2:(tb__ "0|0|
S1S91A1S92OF_;F_;S22S22S88S21S80S16S0S97R5R4R3A3S4A3ScdVsegs;R7R6R3R2A5ScdVsegs;R8R6S89R4R5A2R3A5F_;F_;Fw;Frho;Fs;FT;FL;FK;").
Proof using .
  intros K L T s rho w He [Hsm Hk]. split; [|exact Hk]. eapply entails_sound; eauto.
Qed.

Lemma LQ_nil : ltac2:(tb__ "0|0|
S1S91A1S92OF_;F_;S14S21S80S1cSd0Vsegs;R4R3R2ScS5bA1R1A6A1Fw;Frho;Fn;FK;").
Proof using . intros K n rho w (L & rho' & Hin & _). exact Hin. Qed.

Lemma LQ_cons_inv : ltac2:(tb__ "0|0|
S1S91A1S92OF_;F_;S14S21S5bS1S5bA1S80Sd0Vsegs;R6R5R4SdS5bR3R2A3R1A6S19S18S21S21S17S35R7R6R1A3ScdVsegs;R8S5dR5A1R1R3A5A2Lrho';A2Sd0Vsegs;R7R6R5R3R2A6A2F_;Fw;Frest;FL;Frho;Fn;FK;").
Proof using .
  intros K n rho L rest w (L' & rho' & [<-|Hin] & Hag & Hsm & Hk).
  - left. exists rho'. split; [exact Hag|]. split; assumption.
  - right. exists L', rho'. auto.
Qed.

Lemma triple_leaves_nil : ltac2:(tb__ "0|0|
S80OF_;S1S91A1S92OF_;F_;S14S21S83S82Vsegs;R5Sd0Vsegs;R4R3R2ScS5bA1A5R1A4FQ;Frho;Fn;FK;Fok;").
Proof using . intros ok K n rho Q m Hg w Hw. exfalso. exact (LQ_nil K n rho w Hw). Qed.

Lemma triple_leaves_cons : ltac2:(tb__ "0|0|
S80OF_;S1S91A1S92OF_;F_;S14S21S5bS1S5bA1S83S21S35R6R5R1A3S82Vsegs;R9ScdVsegs;R8S5dR5A1R2A4R3A4F_;Frho';S82Vsegs;R8Sd0Vsegs;R7R6R5R3A5R2A4S82Vsegs;R9Sd0Vsegs;R8R7R6SdS5bR5R4A3A5R3A4F_;F_;FQ;Frest;FL;Frho;Fn;FK;Fok;").
Proof using .
  intros ok K n rho L rest Q H1 H2 m Hg w Hw.
  destruct (LQ_cons_inv K n rho L rest w Hw) as [(rho' & Hag & Hsp)|Hrest].
  - exact (H1 rho' Hag m Hg w Hsp).
  - exact (H2 m Hg w Hrest).
Qed.

Lemma etriple_leaves_nil : ltac2:(tb__ "0|0|
S1S91A1S92OF_;F_;S14S21S80OF_;S81Vsegs;Sd0Vsegs;R4R3R2ScS5bA1A5R1A3FQ;Frho;Fn;FK;").
Proof using . intros K n rho Q w Hw. exfalso. exact (LQ_nil K n rho w Hw). Qed.

Lemma etriple_leaves_cons : ltac2:(tb__ "0|0|
S1S91A1S92OF_;F_;S14S21S5bS1S5bA1S80OF_;S21S35R6R5R1A3S81Vsegs;ScdVsegs;R8S5dR5A1R2A4R3A3F_;Frho';S81Vsegs;Sd0Vsegs;R7R6R5R3A5R2A3S81Vsegs;Sd0Vsegs;R8R7R6SdS5bR5R4A3A5R3A3F_;F_;FQ;Frest;FL;Frho;Fn;FK;").
Proof using .
  intros K n rho L rest Q H1 H2 w Hw.
  destruct (LQ_cons_inv K n rho L rest w Hw) as [(rho' & Hag & Hsp)|Hrest].
  - exact (H1 rho' Hag w Hsp).
  - exact (H2 w Hrest).
Qed.

Lemma triple_leaf_absurd : ltac2:(tb__ "0|0|
S80OF_;S1S91A1S92OF_;F_;S22S21S83S84S1fS25R2A1S2cR3A1A3S1aF_;S82Vsegs;R6ScdVsegs;R5R4R3A4R2A4F_;FQ;Frho;FS;FK;Fok;").
Proof using .
  intros ok K S rho Q H m Hg w [Hsm _]. exfalso. apply H.
  destruct w as [tr [ms md]]. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Hsm))))))))))).
Qed.

Lemma etriple_leaf_absurd : ltac2:(tb__ "0|0|
S1S91A1S92OF_;F_;S22S21S80OF_;S84S1fS25R2A1S2cR3A1A3S1aF_;S81Vsegs;ScdVsegs;R5R4R3A4R2A3F_;FQ;Frho;FS;FK;").
Proof using .
  intros K S rho Q H w [Hsm _]. exfalso. apply H.
  destruct w as [tr [ms md]]. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Hsm))))))))))).
Qed.

Lemma triple_entails : ltac2:(tb__ "0|0|
S80OF_;S1S91A1S92OF_;F_;S22S22S88S21S83S16S0S97R5R4R3A3S4A3S82Vsegs;R8ScdVsegs;R7R5S89R3R4A2A4R2A4S82Vsegs;R9ScdVsegs;R8R7R4A4R3A4F_;F_;FQ;Frho;Fs;FT;FL;FK;Fok;").
Proof using .
  intros ok K L T s rho Q He HT. eapply triple_conseq; [| intros w Hw; exact Hw | exact HT].
  intros w Hw. eapply SP_entails; eauto.
Qed.

Lemma etriple_entails : ltac2:(tb__ "0|0|
S1S91A1S92OF_;F_;S22S22S88S21S80OF_;S16S0S97R5R4R3A3S4A3S81Vsegs;ScdVsegs;R7R5S89R3R4A2A4R2A3S81Vsegs;ScdVsegs;R8R7R4A4R3A3F_;F_;FQ;Frho;Fs;FT;FL;FK;").
Proof using .
  intros K L T s rho Q He HT. eapply etriple_conseq; [| intros w Hw; exact Hw | exact HT].
  intros w Hw. eapply SP_entails; eauto.
Qed.

Lemma SPJ_entails : ltac2:(tb__ "0|0|
ScfS14S22S22S88S21S80S16S0S97R5R4R3A3S4A3S16S0S8cR4R7A2S4A3Sd2R8R9A2SceVsegs;RaR8R5R4A5SceVsegs;RbR8S89R6R7A2R5A5F_;F_;F_;F_;Fw;Frho;Fs;FT;FL;Fg;FJ;").
Proof using .
  intros J g L T s rho w He Hid Hst [Hsm Hk]. split.
  - eapply entails_sound; eauto.
  - eapply Hst; [apply rho_sub_agree; exact Hid | exact Hk].
Qed.

Lemma LQJ_nil : ltac2:(tb__ "0|0|
ScfS14S21S80S1cSd1Vsegs;R4R3R2ScS5bA1R1A6A1Fw;Frho;Fn;FJ;").
Proof using . intros J n rho w (L & rho' & Hin & _). exact Hin. Qed.

Lemma LQJ_cons_inv : ltac2:(tb__ "0|0|
ScfS14S21S5bS1S5bA1S80Sd1Vsegs;R6R5R4SdS5bR3R2A3R1A6S19S18S21S21S17S35R7R6R1A3SceVsegs;R8S5dR5A1R1R3A5A2Lrho';A2Sd1Vsegs;R7R6R5R3R2A6A2F_;Fw;Frest;FL;Frho;Fn;FJ;").
Proof using .
  intros J n rho L rest w (L' & rho' & [<-|Hin] & Hag & Hsm & Hk).
  - left. exists rho'. split; [exact Hag|]. split; assumption.
  - right. exists L', rho'. auto.
Qed.

Lemma triple_leavesJ_nil : ltac2:(tb__ "0|0|
S80OF_;ScfS14S21S83S82Vsegs;R5Sd1Vsegs;R4R3R2ScS5bA1A5R1A4FQ;Frho;Fn;FJ;Fok;").
Proof using . intros ok J n rho Q m Hg w Hw. exfalso. exact (LQJ_nil J n rho w Hw). Qed.

Lemma triple_leavesJ_cons : ltac2:(tb__ "0|0|
S80OF_;ScfS14S21S5bS1S5bA1S83S21S35R6R5R1A3S82Vsegs;R9SceVsegs;R8S5dR5A1R2A4R3A4F_;Frho';S82Vsegs;R8Sd1Vsegs;R7R6R5R3A5R2A4S82Vsegs;R9Sd1Vsegs;R8R7R6SdS5bR5R4A3A5R3A4F_;F_;FQ;Frest;FL;Frho;Fn;FJ;Fok;").
Proof using .
  intros ok J n rho L rest Q H1 H2 m Hg w Hw.
  destruct (LQJ_cons_inv J n rho L rest w Hw) as [(rho' & Hag & Hsp)|Hrest].
  - exact (H1 rho' Hag m Hg w Hsp).
  - exact (H2 m Hg w Hrest).
Qed.

Lemma etriple_leavesJ_nil : ltac2:(tb__ "0|0|
ScfS14S21S80OF_;S81Vsegs;Sd1Vsegs;R4R3R2ScS5bA1A5R1A3FQ;Frho;Fn;FJ;").
Proof using . intros J n rho Q w Hw. exfalso. exact (LQJ_nil J n rho w Hw). Qed.

Lemma etriple_leavesJ_cons : ltac2:(tb__ "0|0|
ScfS14S21S5bS1S5bA1S80OF_;S21S35R6R5R1A3S81Vsegs;SceVsegs;R8S5dR5A1R2A4R3A3F_;Frho';S81Vsegs;Sd1Vsegs;R7R6R5R3A5R2A3S81Vsegs;Sd1Vsegs;R8R7R6SdS5bR5R4A3A5R3A3F_;F_;FQ;Frest;FL;Frho;Fn;FJ;").
Proof using .
  intros J n rho L rest Q H1 H2 w Hw.
  destruct (LQJ_cons_inv J n rho L rest w Hw) as [(rho' & Hag & Hsp)|Hrest].
  - exact (H1 rho' Hag w Hsp).
  - exact (H2 w Hrest).
Qed.

Lemma triple_leafJ_absurd : ltac2:(tb__ "0|0|
S80OF_;ScfS22S21S83S84S1fS25R2A1S2cR3A1A3S1aF_;S82Vsegs;R6SceVsegs;R5R4R3A4R2A4F_;FQ;Frho;FS;FJ;Fok;").
Proof using .
  intros ok J S rho Q H m Hg w [Hsm _]. exfalso. apply H.
  destruct w as [tr [ms md]]. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Hsm))))))))))).
Qed.

Lemma etriple_leafJ_absurd : ltac2:(tb__ "0|0|
ScfS22S21S80OF_;S84S1fS25R2A1S2cR3A1A3S1aF_;S81Vsegs;SceVsegs;R5R4R3A4R2A3F_;FQ;Frho;FS;FJ;").
Proof using .
  intros J S rho Q H w [Hsm _]. exfalso. apply H.
  destruct w as [tr [ms md]]. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Hsm))))))))))).
Qed.

Lemma triple_entailsJ : ltac2:(tb__ "0|0|
S80OF_;ScfS14S22S22S88S21S83S16S0S97R5R4R3A3S4A3S16S0S8cR4R7A2S4A3Sd2R8R9A2S82Vsegs;RbSceVsegs;RaR7S89R5R6A2A4R4A4S82Vsegs;RcSceVsegs;RbR9R6A4R5A4F_;F_;F_;F_;FQ;Frho;Fs;FT;FL;Fg;FJ;Fok;").
Proof using .
  intros ok J g L T s rho Q He Hid Hst HT. eapply triple_conseq; [| intros w Hw; exact Hw | exact HT].
  intros w Hw. eapply SPJ_entails; eauto.
Qed.

Lemma etriple_entailsJ : ltac2:(tb__ "0|0|
ScfS14S22S22S88S21S80OF_;S16S0S97R5R4R3A3S4A3S16S0S8cR4R7A2S4A3Sd2R8R9A2S81Vsegs;SceVsegs;RaR7S89R5R6A2A4R4A3S81Vsegs;SceVsegs;RbR9R6A4R5A3F_;F_;F_;F_;FQ;Frho;Fs;FT;FL;Fg;FJ;").
Proof using .
  intros J g L T s rho Q He Hid Hst HT. eapply etriple_conseq; [| intros w Hw; exact Hw | exact HT].
  intros w Hw. eapply SPJ_entails; eauto.
Qed.

Definition dummy_obj : sobj := ltac2:(tb__ "0|1|
S53S3dZ0A1M0G0G0ScS20A1S4cA5").

Definition select (objs : list sobj) (idxs : list nat) : list sobj := ltac2:(tb__ "0|0|
S85S3S1eS3S86S1eR1Vobjs;SdeA4Li;Vidxs;A4").

Definition complement (ns : list nat) (n : nat) : list nat := ltac2:(tb__ "0|0|
S5aS3S3S11SbbR1Vns;A2A1Li;S87U0Vn;A2A3").

Lemma select_In : ltac2:(tb__ "0|0|
S1S1eA1S1S3A1S1eS55S1eR1SdaR3R2A2A3S3S55S3R1R4A3Sd8R2S9S1eR6A2A2F_;Fi;S55S1eR3R5A3F_;F_;Fo;Fidxs;Fobjs;").
Proof using .
  intros objs idxs o Hin Hlt. unfold select in Hin. apply in_map_iff in Hin as (i & <- & Hi).
  apply nth_In. apply Hlt. exact Hi.
Qed.

Lemma select_nth_error : ltac2:(tb__ "0|0|
S1S1eA1S1S3A1S3S1eS16S6S1eA1S58S1eSdaR4R3A2R2A3S8S1eR1A2A3S18S3S3S17S16S6S3A1S58S3R5R4A3S8S3R1A2A3S16S1eR3S86S1eR1R6SdeA4A3A2Li;A2F_;Fo;Fk;Fidxs;Fobjs;").
Proof using .
  intros objs idxs k o H. unfold select in H. rewrite nth_error_map in H.
  destruct (nth_error idxs k) as [i|] eqn:E; [|discriminate]. cbn in H. injection H as <-. exists i. auto.
Qed.

Lemma smatch_select : ltac2:(tb__ "0|2|
S21S22S1S3A1S7S1S91A1Se0A2S32Vsegs;R4R3R1A4S16S0S99R3A1S4A3S3S55S3R1R5A3Sd8R2S9S1eS29R7A1M0A2M1A2F_;Fi;S3Sd8R1G1A2S55S3R2R7A3F_;Fi;S32Vsegs;R8S63R7SdaG0R6A2A2R5A4F_;F_;F_;F_;Fw;Fidxs;FS;Frho;").
Proof using .
  intros rho S idxs [tr [ms md]] Hsm Hnd Hlt Hcov.
  pose proof (smatch_swf segs _ _ _ Hsm) as Hwf.
  destruct Hsm as (_ & Hpc & Hpend & Hhalt & Hrom & Hroc & Hregs & Hfregs & Hfcsr & Hresv & Hmem & Hfacts).
  cbn [fst snd cfg_ms cfg_model] in *. destruct Hmem as (Hall & Hpd & Hfr).
  apply nodupN_NoDup in Hnd.
  unfold smatch. cbn [fst snd cfg_ms cfg_model set_objs ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next].
  split.
  { pose proof Hwf as W. unfold swf in W |- *. cbn [ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next].
    repeat (apply andb_prop in W; destruct W as [W ?]).
    repeat (apply andb_true_intro; split); try assumption.
    apply forallb_forall. intros o Hin. apply (proj1 (forallb_forall _ _) H0). eapply select_In; [exact Hin | exact Hlt]. }
  split; [exact Hpc|]. split; [exact Hpend|]. split; [exact Hhalt|]. split; [exact Hrom|]. split; [exact Hroc|].
  split; [exact Hregs|]. split; [exact Hfregs|]. split; [exact Hfcsr|]. split; [exact Hresv|].
  split; [|exact Hfacts]. split; [|split].
  - apply Forall_forall. intros o Hin. apply (proj1 (Forall_forall _ _) Hall). eapply select_In; [exact Hin | exact Hlt].
  - apply (proj2 (pairwise_disjoint_nth rho _)). intros p q op oq Hpq Hp Hq.
    destruct (select_nth_error _ _ _ _ Hp) as (ip & Hip & ->). destruct (select_nth_error _ _ _ _ Hq) as (iq & Hiq & ->).
    assert (Hne : ip <> iq).
    { intros E. subst iq. pose proof (NoDup_nth_error_inj idxs p q ip Hnd Hip Hiq). lia. }
    pose proof (Hlt ip (nth_error_In _ _ Hip)) as Lp. pose proof (Hlt iq (nth_error_In _ _ Hiq)) as Lq.
    destruct (nth_error (ss_objs S) ip) as [op|] eqn:Ep; [|exfalso; apply (proj2 (nth_error_Some (ss_objs S) ip) Lp); exact Ep].
    destruct (nth_error (ss_objs S) iq) as [oq|] eqn:Eq; [|exfalso; apply (proj2 (nth_error_Some (ss_objs S) iq) Lq); exact Eq].
    rewrite (nth_error_nth _ _ _ Ep), (nth_error_nth _ _ _ Eq).
    destruct (Nat.lt_ge_cases ip iq).
    + exact (proj1 (pairwise_disjoint_nth rho _) Hpd ip iq op oq ltac:(lia) Ep Eq).
    + apply ranges_disjoint_sym. exact (proj1 (pairwise_disjoint_nth rho _) Hpd iq ip oq op ltac:(lia) Eq Ep).
  - intros a Ha. apply Hfr. apply Forall_forall. intros o Hin. apply In_nth_error in Hin as [i Hi].
    assert (Li : (i < length (ss_objs S))%nat) by (apply (proj1 (nth_error_Some _ _)); rewrite Hi; discriminate).
    pose proof (Hcov i Li) as Hii.
    pose proof (proj1 (Forall_forall _ _) Ha (nth i (ss_objs S) dummy_obj) ltac:(unfold select; apply in_map_iff; exists i; auto)) as X.
    rewrite (nth_error_nth _ _ _ Hi) in X. exact X.
Qed.

Definition entails_fr_ref (L T : sstate) (s : wsub) : option (list sobj) := ltac2:(tb__ "0|5|
S6S1S3A1M0A1S6S1S1eA1M1A1M2Lx;S9fS2cVL;A1S29VL;A1M3S85S1eS1eS8aVs;A1S29VT;A1A4A3G0S9S1eG3A2S3S0G2L_;S5S5S99R2A1S56S3S3Se4R1R2A2Li;R2A3A2S97S63VL;SdaG3R2A2A2VT;Vs;A3A2S8G1SdaG3SdcR2R1A2A2A2S10G1A1M4X0x2Tn;Lns;G4X6x2").

Definition entails_fr (L T : sstate) (s : wsub) : option (list sobj) := ltac2:(tb__ "0|6|
S96S2cVL;A1A1SccS6S1S3A1M0A1S6S1S1eA1M1A1M2Lx;SaeR1S29VL;A1M3S85S1eS1eS8aVs;A1S29VT;A1A4A3G0S9S1eG3A2S3S0G2L_;S5S5S99R2A1S56S3S3Se4R1R2A2Li;R2A3A2S0S0L_;Sb7S63VL;SdaG3R2A2A2M4VT;Vs;A3Sb8R3G4VT;Vs;A4S2X0x2A2S8G1SdaG3SdcR2R1A2A2A2S10G1A1M5X0x2Tn;Lns;G5X6x2Tpf;").

Lemma entails_fr_eq : ltac2:(tb__ "0|0|
S22S22S88S16S6S1S1eA1A1SddR3R2R1A3SdfR3R2R1A3A3Fs;FT;FL;").
Proof using .
  intros. unfold entails_fr, entails_fr_ref. cbv zeta. rewrite witnesses_pf_eq.
  destruct (witnesses (ss_facts L) (ss_objs L) (map (obj_subst s) (ss_objs T))); [|reflexivity].
  replace (entails_cheap (set_objs L (select (ss_objs L) l)) T s &&& entails_pfx (mk_pf (ss_facts L)) (set_objs L (select (ss_objs L) l)) T s)
     with (entails (set_objs L (select (ss_objs L) l)) T s) by reflexivity.
  rewrite entails_eq. reflexivity.
Qed.

Lemma complement_spec : ltac2:(tb__ "0|0|
S1S3A1S3S3S1bS55S3R1SdcR3R2A2A3S17Sd8R1R2A2S1cS55S3R1R3A3A1A2A2Fi;Fn;Fns;").
Proof using .
  intros ns n i. unfold complement. rewrite filter_In, in_seq, Bool.negb_true_iff.
  split.
  - intros [Hi Hm]. split; [lia|]. intros Hin. apply (proj2 (memN_In i ns)) in Hin. congruence.
  - intros [Hi Hn]. split; [lia|]. destruct (memN i ns) eqn:E; [|reflexivity].
    exfalso. apply Hn. apply memN_In. exact E.
Qed.

Lemma nodupN_app_complement : ltac2:(tb__ "0|0|
S1S3A1S3S16S0S99R2A1S4A3S16S0S99S12S3R3SdcR3R2A2A3A1S4A3F_;Fn;Fns;").
Proof using .
  intros ns n Hnd.
  assert (ND : List.NoDup (ns ++ complement ns n)).
  { apply List.NoDup_app.
    - apply nodupN_NoDup. exact Hnd.
    - unfold complement. apply List.NoDup_filter. apply List.seq_NoDup.
    - intros x Hx Hc. apply complement_spec in Hc as [_ Hn]. exact (Hn Hx). }

  induction (ns ++ complement ns n) as [|x t IH]; [reflexivity|].
  inversion ND; subst. cbn. rewrite IH by assumption.
  destruct (memN x t) eqn:E; [|reflexivity]. exfalso. apply H1. apply memN_In. exact E.
Qed.

Theorem entails_fr_sound : ltac2:(tb__ "0|2|
S22S22S88S1S1eA1M0S21S1S91A1M1Sd3S92S16S6G0A1SddR8R7R6A3S8G0R5A2A3S32Vsegs;R5R9SbG1Se0R4Se1R3R2A2A4A4S17S32Vsegs;S89S8dR6R7R4A3R8A2R9SbG1Se0R5Se1R4R3A2A4A4S17S84S1eS33Vsegs;R6R4A3R7A3S17S4fR6R7A2S17S16S0S56S1eS34S54RaA1A1R7A3S4A3S1eS55S1eR1R8A3S55S1eR2S29RcA1A3F_;Fo;A2A2A2A2F_;F_;Fmd;Fms;Ftr;Frho;FR;Fs;FT;FL;").
Proof using .
  intros L T s R rho tr ms md He Hsm.
  rewrite entails_fr_eq in He. unfold entails_fr_ref in He.
  destruct (witnesses (ss_facts L) (ss_objs L) (map (obj_subst s) (ss_objs T))) as [ns|] eqn:Hw; [|discriminate].
  destruct (nodupN ns && forallb (fun i => Nat.ltb i (length (ss_objs L))) ns
            && entails (set_objs L (select (ss_objs L) ns)) T s)%bool eqn:Hc; [|discriminate].
  injection He as <-.
  apply andb_prop in Hc as [Hc Hent]. apply andb_prop in Hc as [Hnd Hlt].
  assert (Hlt' : forall i, In i ns -> (i < length (ss_objs L))%nat).
  { intros i Hi. apply Nat.ltb_lt. exact (proj1 (forallb_forall _ _) Hlt i Hi). }
  set (idxs := ns ++ complement ns (length (ss_objs L))).
  assert (Hperm : smatch segs rho (set_objs L (select (ss_objs L) idxs)) (tr, mkCfg ms md)).
  { apply smatch_select; [exact Hsm | apply nodupN_app_complement; exact Hnd | |].
    - intros i Hi. apply in_app_or in Hi as [Hi|Hi]; [apply Hlt'; exact Hi|]. apply complement_spec in Hi. lia.
    - intros i Hi. subst idxs. apply in_or_app. destruct (memN i ns) eqn:E.
      + left. apply memN_In. exact E.
      + right. apply complement_spec. split; [exact Hi|]. intros Hin. apply (proj2 (memN_In i ns)) in Hin. congruence. }
  assert (Hsplit : ss_objs (set_objs L (select (ss_objs L) idxs))
                   = select (ss_objs L) ns ++ select (ss_objs L) (complement ns (length (ss_objs L)))).
  { cbn. unfold select, idxs. apply map_app. }
  pose proof (smatch_frame_in segs rho _ _ _ tr ms md Hsplit Hperm) as Hin.
  pose proof (smatch_swf segs _ _ _ Hperm) as HwfP.
  destruct Hperm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HmemP & _). cbn [fst snd cfg_ms] in HmemP.
  rewrite Hsplit in HmemP. destruct HmemP as (HallP & HpdP & _).
  apply Forall_app in HallP as [_ HallR]. apply pairwise_disjoint_app_inv in HpdP as (_ & HpdR & _).
  split; [|split; [exact HallR | split; [exact HpdR | split]]].
  - eapply entails_sound; [exact Hent|]. exact Hin.
  - pose proof (swf_objs _ HwfP) as WO. rewrite Hsplit in WO. cbn [ss_next set_objs] in WO.
    apply forallb_forall. intros o Ho. apply (proj1 (forallb_forall _ _) WO). apply in_or_app. right. exact Ho.
  - intros o Ho. eapply select_In; [exact Ho|]. intros i Hi. apply complement_spec in Hi. lia.
Qed.

Lemma entails_fr_ranges : ltac2:(tb__ "0|2|
S22S22S88S1S1eA1M0S21S1S91A1M1Sd3S92S16S6G0A1SddR8R7R6A3S8G0R5A2A3S32Vsegs;R5R9SbG1Se0R4Se1R3R2A2A4A4S1eS1eS55S1eR2S29RbA1A3S55S1eR2RaA3S40S31S89S8dRaRbR8A3RcA2R4A2S31RaR3A2A2F_;F_;FoR;FoT;F_;F_;Fmd;Fms;Ftr;Frho;FR;Fs;FT;FL;").
Proof using .
  intros L T s R rho tr ms md He Hsm.
  rewrite entails_fr_eq in He. unfold entails_fr_ref in He.
  destruct (witnesses (ss_facts L) (ss_objs L) (map (obj_subst s) (ss_objs T))) as [ns|] eqn:Hw; [|discriminate].
  destruct (nodupN ns && forallb (fun i => Nat.ltb i (length (ss_objs L))) ns
            && entails (set_objs L (select (ss_objs L) ns)) T s)%bool eqn:Hc; [|discriminate].
  injection He as <-.
  apply andb_prop in Hc as [Hc Hent]. apply andb_prop in Hc as [Hnd Hlt].
  assert (Hlt' : forall i, In i ns -> (i < length (ss_objs L))%nat).
  { intros i Hi. apply Nat.ltb_lt. exact (proj1 (forallb_forall _ _) Hlt i Hi). }
  set (idxs := ns ++ complement ns (length (ss_objs L))).
  assert (Hperm : smatch segs rho (set_objs L (select (ss_objs L) idxs)) (tr, mkCfg ms md)).
  { apply smatch_select; [exact Hsm | apply nodupN_app_complement; exact Hnd | |].
    - intros i Hi. apply in_app_or in Hi as [Hi|Hi]; [apply Hlt'; exact Hi|]. apply complement_spec in Hi. lia.
    - intros i Hi. subst idxs. apply in_or_app. destruct (memN i ns) eqn:E.
      + left. apply memN_In. exact E.
      + right. apply complement_spec. split; [exact Hi|]. intros Hin. apply (proj2 (memN_In i ns)) in Hin. congruence. }
  assert (Hsplit : ss_objs (set_objs L (select (ss_objs L) idxs))
                   = select (ss_objs L) ns ++ select (ss_objs L) (complement ns (length (ss_objs L)))).
  { cbn. unfold select, idxs. apply map_app. }
  pose proof (smatch_frame_in segs rho _ _ _ tr ms md Hsplit Hperm) as Hin.
  destruct Hperm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HmemP & _). cbn [fst snd cfg_ms] in HmemP.
  rewrite Hsplit in HmemP. destruct HmemP as (_ & HpdP & _).
  apply pairwise_disjoint_app_inv in HpdP as (_ & _ & Hcross).
  intros oT oR HoT HoR.
  destruct (entails_ranges _ T s _ tr ms md Hent Hin oT HoT) as (oL & HoL & ->).
  cbn [set_objs ss_objs] in HoL.
  rewrite obj_range_absorb. apply Hcross; [exact HoL | exact HoR].
Qed.

End WithSegs.
