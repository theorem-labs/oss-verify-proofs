(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require AxSymExec3SoundK_blobs1 AxSymExec3SoundK_blobs2.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import SymStepR AxSymExec3K.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Rpl.
Ltac2 rplG () : string array := Array.of_list ["LinuxProcessSemantics.Riscv.Instr.aluop"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.bool"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.aluop_eqb"; "Corelib.Init.Datatypes.true"; "LinuxProcessSemantics.Riscv.Instr.ALU_ADD"; "Corelib.Init.Logic.eq_refl"; "Corelib.Init.Datatypes.false"; "Corelib.Init.Logic.eq_ind"; "Corelib.Init.Logic.False"; "Corelib.Init.Logic.True"; "Corelib.Init.Logic.I"; "Corelib.Init.Logic.False_ind"; "LinuxProcessSemantics.Riscv.Instr.ALU_SUB"; "LinuxProcessSemantics.Riscv.Instr.ALU_SLL"; "LinuxProcessSemantics.Riscv.Instr.ALU_SLT"; "LinuxProcessSemantics.Riscv.Instr.ALU_SLTU"; "LinuxProcessSemantics.Riscv.Instr.ALU_XOR"; "LinuxProcessSemantics.Riscv.Instr.ALU_SRL"; "LinuxProcessSemantics.Riscv.Instr.ALU_SRA"; "LinuxProcessSemantics.Riscv.Instr.ALU_OR"; "LinuxProcessSemantics.Riscv.Instr.ALU_AND"; "LinuxProcessSemantics.Riscv.Instr.mulop"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.mulop_eqb"; "LinuxProcessSemantics.Riscv.Instr.M_MUL"; "LinuxProcessSemantics.Riscv.Instr.M_MULH"; "LinuxProcessSemantics.Riscv.Instr.M_MULHSU"; "LinuxProcessSemantics.Riscv.Instr.M_MULHU"; "LinuxProcessSemantics.Riscv.Instr.M_DIV"; "LinuxProcessSemantics.Riscv.Instr.M_DIVU"; "LinuxProcessSemantics.Riscv.Instr.M_REM"; "LinuxProcessSemantics.Riscv.Instr.M_REMU"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.expr"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.expr_ind"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.expr_eqb"; "Corelib.Numbers.BinNums.Z"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.ELit"; "Stdlib.ZArith.BinInt.Z.eqb"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.eqb_eq"; "Corelib.Init.Logic.eq_ind_r"; "Corelib.Init.Datatypes.nat"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.EVar"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.EAlu"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.EAluw"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.EMd"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.EMdw"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.EExt"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.EBlob"; "Stdlib.Arith.PeanoNat.Nat.eqb"; "Stdlib.Arith.PeanoNat.Nat.eqb_eq"; "Corelib.Init.Datatypes.andb"; "Corelib.Init.Datatypes.andb_prop"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.aluop_eqb_eq"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.mulop_eqb_eq"; "Stdlib.Bool.Bool.eqb"; "Stdlib.Bool.Bool.eqb_prop"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.saddr"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.saddr_eqb"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.SA"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.expr_eqb_eq"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.env"; "stdpp.bitvector.definitions.bv"; "Corelib.Numbers.BinNums.Npos"; "stdpp.bitvector.definitions.Z_to_bv"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.v_add"; "Corelib.Numbers.BinNums.Z0"; "Corelib.Numbers.BinNums.N"; "stdpp.bitvector.definitions.bv_unsigned"; "stdpp.bitvector.definitions.bv_eq"; "Stdlib.ZArith.BinInt.Z.add"; "stdpp.bitvector.definitions.bv_wrap"; "stdpp.bitvector.definitions.bv_wrap_bv_unsigned"; "Stdlib.ZArith.BinInt.Z.add_0_r"; "stdpp.bitvector.definitions.Z_to_bv_unsigned"; "LinuxProcessSemantics.Riscv.Sem.alu64"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.alu_add"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.SymExec.v_add_comm"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.v_sub"; "Stdlib.ZArith.BinInt.Z.opp"; "Stdlib.ZArith.BinInt.Z.sub"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.SymExec.v_add_lit"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.SymExec.v_sub_lit"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.alu_sub"; "Corelib.Init.Logic.ex"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Numbers.BinNums.Zpos"; "Corelib.Init.Logic.ex_intro"; "Stdlib.ZArith.BinInt.Z.pow_pos_nonneg"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.pow_nonneg"; "Corelib.Init.Datatypes.nil"; "Stdlib.micromega.ZMicromega.ZArithProof"; "Corelib.Init.Datatypes.list"; "Stdlib.micromega.VarMap.Elt"; "Stdlib.micromega.VarMap.t"; "Stdlib.micromega.Tauto.A"; "Stdlib.micromega.RingMicromega.Formula"; "Stdlib.micromega.Tauto.eKind"; "Corelib.Init.Datatypes.unit"; "Stdlib.micromega.Tauto.isProp"; "Stdlib.micromega.RingMicromega.Build_Formula"; "Stdlib.micromega.EnvRing.PEX"; "Corelib.Numbers.BinNums.xH"; "Stdlib.micromega.RingMicromega.OpEq"; "Stdlib.micromega.EnvRing.PEadd"; "Stdlib.micromega.EnvRing.PEmul"; "Stdlib.micromega.EnvRing.PEc"; "Stdlib.micromega.EnvRing.PEpow"; "Corelib.Init.Datatypes.tt"; "Stdlib.micromega.Tauto.BFormula"; "Stdlib.micromega.ZMicromega.ZTautoChecker_sound"; "Stdlib.micromega.ZMicromega.ZTautoChecker"; "Stdlib.micromega.VarMap.find"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.eqm"; "Corelib.Init.Datatypes.cons"; "Stdlib.micromega.ZMicromega.RatProof"; "Stdlib.micromega.RingMicromega.PsatzAdd"; "Stdlib.micromega.RingMicromega.PsatzMulC"; "Stdlib.micromega.EnvRing.Pc"; "Corelib.Numbers.BinNums.Zneg"; "Stdlib.micromega.RingMicromega.PsatzIn"; "Corelib.Init.Datatypes.O"; "Stdlib.micromega.ZMicromega.DoneProof"; "Stdlib.micromega.VarMap.Branch"; "Stdlib.micromega.Tauto.IMPL"; "Corelib.Init.Datatypes.None"; "Stdlib.micromega.EnvRing.PEopp"; "Stdlib.micromega.VarMap.Empty"; "Corelib.Init.Datatypes.prod"; "Stdlib.setoid_ring.Ring_polynom.PExpr"; "Stdlib.setoid_ring.ZArithRing.Zr_ring_lemma1"; "Stdlib.setoid_ring.Ring_tac.ring_subst_niter"; "Stdlib.setoid_ring.Ring_polynom.PEmul"; "Stdlib.setoid_ring.Ring_polynom.PEX"; "Stdlib.setoid_ring.Ring_polynom.PEadd"; "Stdlib.setoid_ring.Ring_polynom.PEpow"; "Stdlib.setoid_ring.Ring_polynom.PEc"; "Stdlib.ZArith.BinInt.Z.to_N"; "Stdlib.setoid_ring.Ring_polynom.mk_monpol_list"; "Stdlib.ZArith.BinInt.Z.quotrem"; "Stdlib.setoid_ring.Ring_polynom.Mon"; "Stdlib.setoid_ring.Ring_polynom.Pol"; "Stdlib.setoid_ring.Ring_polynom.Peq"; "Stdlib.setoid_ring.Ring_polynom.norm_subst"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.div"; "Stdlib.ZArith.BinInt.Z.div_mod"; "Stdlib.micromega.Tauto.NOT"; "Stdlib.micromega.SatDivMod.Z_mod_nonneg_nonneg"; "Stdlib.micromega.SatDivMod.Z_div_nonneg_nonneg"; "Corelib.Init.Logic.not"; "Stdlib.ZArith.BinInt.Z.mod_pos_bound"; "Stdlib.ZArith.BinInt.Z.mod_neg_bound"; "Stdlib.omega.PreOmega.Z.div_0_r_ext"; "Stdlib.omega.PreOmega.Z.mod_0_r_ext"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.snorm_ref"; "Stdlib.ZArith.BinInt.Z.leb"; "Stdlib.micromega.EnvRing.PEsub"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.two64z"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.two64z_eq"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.snorm"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.snorm_eq"; "Stdlib.ZArith.BinInt.Z.mod_add"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.bv_wrap64_mod"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.eqm_mod"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.u_lit64a"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.edenot"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.lin"; "Corelib.Init.Datatypes.fst"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.LinDenot.tden"; "Corelib.Init.Datatypes.snd"; "Corelib.Init.Datatypes.list_ind"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.lins"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.LinDenot.uE"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.eqm_snorm"; "Corelib.Init.Datatypes.pair"; "Stdlib.micromega.RingMicromega.PsatzMulE"; "Stdlib.micromega.EnvRing.Pinj"; "Stdlib.micromega.EnvRing.PX"; "Stdlib.micromega.RingMicromega.OpLe"; "Stdlib.micromega.Tauto.TT"; "Corelib.Init.Datatypes.comparison"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.expr_cmp"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.LinDenot.lden"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.ladd"; "Stdlib.Lists.List.fold_right"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.eqm_trans"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.LinDenot.lins_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.lscale_terms"; "Stdlib.micromega.RingMicromega.PsatzC"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.lscale"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.LinDenot.lscale_terms_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.eqm_u_lit"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.v_mul"; "LinuxProcessSemantics.Riscv.Sem.mul_div"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.m_mul"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.v_sll"; "Stdlib.ZArith.BinInt.Z.shiftl"; "Corelib.Init.Logic.eq_sym"; "Stdlib.ZArith.Zdiv.Z.mod_mod_divide"; "Stdlib.ZArith.BinInt.Z.mul_comm"; "Stdlib.ZArith.BinInt.Z.shiftl_mul_pow2"; "Stdlib.micromega.RingMicromega.OpLt"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.alu_sll"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.lin_of"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.LinDenot.ladd_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.eqm_add"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.eqm_sym"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.LinDenot.u_add_eqm"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.LinDenot.lscale_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.eqm_mul_l"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.LinDenot.u_sub_eqm"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.LinDenot.u_sll_eqm"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.eqm_mul_r"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.LinDenot.u_mul_eqm"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.ev"; "LinuxProcessSemantics.Riscv.Prelude.sext"; "LinuxProcessSemantics.Riscv.Sem.alu32"; "LinuxProcessSemantics.Riscv.Sem.low32"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.ext_val"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.blob_val"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.eb"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.lterm"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.lterms"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.LinDenot.lterm_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.unlin"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.LinDenot.lterms_sound"; "Stdlib.ZArith.BinInt.Z.add_0_l"; "Stdlib.ZArith.BinInt.Z.add_comm"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.eqm_Z_to_bv"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.LinDenot.unlin_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.LinDenot.lin_of_sound"; "stdpp.bitvector.definitions.Z_to_bv_bv_unsigned"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.coeffs_div"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.tden"; "Stdlib.ZArith.BinInt.Z.mod_0_l"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.uE"; "Stdlib.ZArith.BinInt.Z.mul_0_l"; "Stdlib.ZArith.BinInt.Z.mul_mod"; "Stdlib.ZArith.BinInt.Z.add_mod"; "stdpp.tactics.f_equal_help"; "Stdlib.ZArith.BinInt.Z.pow_add_r"; "Stdlib.micromega.Tauto.AND"; "Stdlib.micromega.Tauto.X"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.pow2_div_64"; "Corelib.Init.Datatypes.option"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.lin_lowbits"; "Corelib.Init.Datatypes.Some"; "Corelib.Init.Logic.f_equal"; "Corelib.Numbers.BinNums.positive"; "Stdlib.ZArith.BinInt.Z.pos_div_eucl"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.lin_of_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.lden"; "Corelib.Init.Logic.conj"; "Stdlib.ZArith.BinInt.Z.mod_mod"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.coeffs_div_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.eqm_mod_pow2"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.shamt_of"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.lin_lowbits_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.v_srl"; "Stdlib.ZArith.BinInt.Z.shiftr"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.alu_srl"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.v_sra"; "stdpp.bitvector.definitions.bv_signed"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.alu_sra"; "Corelib.Init.Logic.or"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.v_sllw"; "stdpp.bitvector.definitions.bv_swrap"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.w_sllw"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.v_srlw"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.w_srlw"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.v_sraw"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.w_sraw"; "Stdlib.ZArith.BinInt.Z.mod_small"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.unlin_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.lscale_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.alu_sll_amt"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.v_and"; "Stdlib.ZArith.BinInt.Z.land"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.u64_range"; "Stdlib.ZArith.BinInt.Z.pow_le_mono_r"; "Stdlib.ZArith.BinInt.Z.pred"; "Stdlib.ZArith.BinInt.Z.shiftl_1_l"; "Stdlib.ZArith.BinInt.Z.ones"; "Stdlib.ZArith.BinInt.Z.land_ones"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.alu_and"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.is_lit"; "Corelib.Init.Logic.eq_trans"; "Stdlib.ZArith.BinInt.Z.bits_inj'"; "Stdlib.ZArith.BinInt.Z.lt_ge_cases"; "Stdlib.ZArith.BinInt.Z.testbit"; "Stdlib.ZArith.BinInt.Z.mod_pow2_bits_low"; "Stdlib.ZArith.BinInt.Z.div_pow2_bits"; "Stdlib.ZArith.BinInt.Z.mod_pow2_bits_high"; "Stdlib.ZArith.Zdiv.Zminus_mod_idemp_l"; "stdpp.bitvector.definitions.bv_half_modulus"; "Stdlib.NArith.BinNat.N.mul"; "Stdlib.NArith.BinNat.N.of_nat"; "Stdlib.ZArith.BinInt.Z.of_nat"; "stdpp.bitvector.definitions.bv_unsigned_in_range"; "stdpp.bitvector.definitions.bv_modulus"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.Z_to_bv64_swrap64"; "Stdlib.ZArith.BinInt.Z.div_1_r"; "Corelib.Init.Peano.le"; "Stdlib.micromega.ZifyClasses.rew_iff"; "Stdlib.micromega.ZifyClasses.mkrel"; "Stdlib.ZArith.Znat.Nat2Z.inj_le"; "Stdlib.ZArith.Znat.Nat2Z.is_nonneg"; "Stdlib.micromega.ZMicromega.CutProof"; "Stdlib.micromega.RingMicromega.PsatzLet"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.ext_Z"; "Corelib.Init.Nat.add"; "Stdlib.micromega.ZifyClasses.rew_iff_rev"; "Corelib.Init.Logic.iff_refl"; "Stdlib.micromega.ZifyClasses.mkapp2"; "Stdlib.micromega.ZifyClasses.inj"; "Stdlib.micromega.ZifyInst.Inj_Z_Z"; "Stdlib.micromega.ZifyClasses.mkapp"; "Stdlib.Arith.PeanoNat.Nat.add"; "Stdlib.ZArith.Znat.Nat2Z.inj_add"; "Stdlib.ZArith.BinInt.Z.div_div"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.slice_mod"; "stdpp.bitvector.definitions.bv_wrap_small"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.ext_Z_range"; "Stdlib.ZArith.BinInt.Z.ltb"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.two64"; "Stdlib.ZArith.BinInt.Z.leb_le"; "Stdlib.ZArith.BinInt.Z.ltb_lt"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.wrap64"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.ones64z"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.land64"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.two32z"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.ones32z"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.land32"; "Stdlib.ZArith.BinInt.Z.of_N"; "Stdlib.ZArith.Znat.N2Z.inj_mul"; "Stdlib.ZArith.Znat.nat_N_Z"; "Stdlib.micromega.ZifyClasses.and_morph"; "Stdlib.micromega.ZifyClasses.eq_iff"; "Corelib.Numbers.BinNums.N0"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.wrap64_mod"; "Corelib.Init.Datatypes.S"; "Stdlib.ZArith.Znat.Nat2Z.inj_succ"; "Stdlib.ZArith.BinInt.Z.succ"; "Stdlib.ZArith.BinInt.Z.pow_succ_r"; "Stdlib.ZArith.BinInt.Z.eq_decidable"; "Stdlib.micromega.Tauto.OR"; "Stdlib.ZArith.BinInt.Z.ltb_spec"; "Corelib.Init.Datatypes.BoolSpec"; "Stdlib.ZArith.BinInt.Z.mul_1_l"; "Stdlib.ZArith.BinInt.Z.shiftr_div_pow2"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.zext_fast"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.zext_lit"; "Stdlib.Arith.PeanoNat.Nat.leb"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.zext_fast_eq"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.ext_val_full"; "Stdlib.Arith.PeanoNat.Nat.leb_le"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.ext_val_compose"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.mkExt"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.ridx"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.u5_range"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Stdlib.ZArith.BinInt.Z.max"; "Corelib.Init.Logic.iff_sym"; "Stdlib.ZArith.Znat.Nat2Z.inj_iff"; "Stdlib.micromega.ZifyInst.of_nat_to_nat_eq"; "Stdlib.ZArith.BinInt.Z.max_spec"; "Corelib.Init.Datatypes.nat_ind"; "Corelib.Lists.ListDef.nth"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.sr_upd"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.getr"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.sr_get"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.regs_ok"; "LinuxProcessSemantics.Riscv.Prelude.bv_eqb"; "stdpp.bitvector.definitions.BV"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.regupd"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.bv_eqb_refl"; "stdpp.bitvector.definitions.BvWf"; "Stdlib.micromega.Tauto.EQ"; "Stdlib.micromega.Tauto.isBool"; "LinuxProcessSemantics.Riscv.Sem.reg_get"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.ridx_inj"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.getr_same"; "Stdlib.Arith.PeanoNat.Nat.eqb_refl"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.getr_other"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.nth_sr_upd"; "Corelib.Init.Peano.lt"; "Stdlib.ZArith.Znat.Nat2Z.inj_lt"; "Stdlib.ZArith.Znat.Z2Nat.id"; "Stdlib.Arith.PeanoNat.Nat.ltb"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.Env"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.reg_ev"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.sr_id"; "Corelib.Classes.Morphisms.trans_co_eq_inv_impl_morphism"; "Corelib.Classes.RelationClasses.eq_Transitive"; "Corelib.Classes.Morphisms.Reflexive_partial_app_morphism"; "Corelib.Classes.Morphisms.respectful"; "Corelib.Classes.Morphisms.reflexive_proper"; "Corelib.Classes.Morphisms.reflexive_reflexive_proxy"; "Corelib.Classes.Morphisms.reflexive_eq_dom_reflexive"; "Corelib.Classes.RelationClasses.eq_Reflexive"; "Corelib.Classes.Morphisms.eq_proper_proxy"; "Corelib.Classes.RelationClasses.symmetry"; "Corelib.Classes.RelationClasses.eq_Symmetric"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.ridx_roundtrip"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.ridx_range"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.sentry"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.StoreOk.mem_grows"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.mem_denot"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.StoreOk.mem_grows_refl"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.StoreOk.mem_grows_trans"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CatExec.wbytes"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.adenot"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.word_to_le_bytes"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.StoreOk.wbytes_grows"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.SE"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.a_base"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.a_off"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.estart"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.flat"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.kentry"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.rdn"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.elenZ"; "Corelib.Init.Datatypes.length"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.store_ok"; "Corelib.Lists.ListDef.Forall"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.kentry_ok"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.sidecond"; "LinuxProcessSemantics.Riscv.Instr.branch_cond"; "LinuxProcessSemantics.Riscv.Sem.branch_taken"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.extz"; "LinuxProcessSemantics.LinuxProcessSem.BvBase.bytes_le_to_Z"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.sc_denot"; "stdpp.bitvector.definitions.bv_add"; "LinuxProcessSemantics.LinuxProcessSem.BvBase.nat_to_word"; "stdpp.bitvector.definitions.bv_wrap_add_idemp_r"; "stdpp.bitvector.definitions.bv_add_unsigned"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.u_small"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.elen"; "Corelib.Init.Nat.sub"; "Corelib.Lists.ListDef.skipn"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.word_add_0"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.seg_rom"; "Stdlib.Arith.PeanoNat.Nat.sub"; "Stdlib.ZArith.Znat.Nat2Z.inj_sub_max"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.nat_to_word_add_merge"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.word1_nat"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.SeqExec.rdn_firstn"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.rdn_skipn"; "LinuxProcessSemantics.LinuxProcessSem.BvBase.Z_to_le_bytes"; "Corelib.Lists.ListDef.firstn"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.bytes_le_Z_to_le"; "Stdlib.ZArith.BinInt.Z.div_pos"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.firstn_Z_to_le_bytes"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.skipn_Z_to_le_bytes"; "Corelib.Init.Nat.min"; "Stdlib.ZArith.BinInt.Z.min"; "Stdlib.Arith.PeanoNat.Nat.min"; "Stdlib.ZArith.Znat.Nat2Z.inj_min"; "Stdlib.ZArith.BinInt.Z.min_spec"; "Stdlib.Lists.List.length_skipn"; "Stdlib.Lists.List.length_firstn"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.u8_range"; "Stdlib.ZArith.BinInt.Z.lor"; "Stdlib.ZArith.BinInt.Z.lxor"; "Stdlib.ZArith.BinInt.Z.add_nocarry_lxor"; "Stdlib.Bool.Bool.andb_false_r"; "Stdlib.ZArith.BinInt.Z.mul_pow2_bits_low"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.Z_testbit_high"; "Stdlib.ZArith.BinInt.Z.bits_0"; "Stdlib.ZArith.BinInt.Z.land_spec"; "Stdlib.ZArith.BinInt.Z.lxor_lor"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.Z_to_bv_u_plus0"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.u_add1"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.img_bytes"; "Corelib.Lists.ListDef.map"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.zbytes_le_to_Z"; "Corelib.Lists.ListDef.repeat"; "Stdlib.ZArith.BinInt.Z.lt_le_incl"; "stdpp.bitvector.definitions.bv_modulus_pos"; "Stdlib.ZArith.BinInt.Z.div_lt_upper_bound"; "stdpp.bitvector.definitions.bv_extract"; "Stdlib.NArith.BinNat.N.le"; "Stdlib.ZArith.Znumtheory.Zmod_div_mod"; "Stdlib.ZArith.Znat.N2Z.inj_le"; "Stdlib.ZArith.Znat.N2Z.is_nonneg"; "Stdlib.ZArith.BinInt.Z.shiftr_0_r"; "stdpp.bitvector.definitions.bv_extract_unsigned"; "LinuxProcessSemantics.Riscv.Prelude.zext"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.SymExec.zext64_lit"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.SymExec.sext64_lit"; "LinuxProcessSemantics.Riscv.Instr.msize"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.msize_bytes"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.bytes_le_to_Z_bound"; "LinuxProcessSemantics.Riscv.Instr.SZ1"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.sext64_small"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.zext64_small"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.extract0_Z_to_bv64"; "LinuxProcessSemantics.Riscv.Instr.SZ2"; "LinuxProcessSemantics.Riscv.Instr.SZ4"; "LinuxProcessSemantics.Riscv.Instr.SZ8"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.SymStepR.load_result"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.SymStepR.eff_sx"; "Corelib.Lists.ListDef.Forall_cons"; "Corelib.Init.Logic.iff"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.scs_denot"; "Stdlib.Lists.List.Forall_app"; "Corelib.Init.Datatypes.app"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.lres"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.log_lookup"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.rel_lit"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.rangerel"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.LHit"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.log_bytes_lit"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.lit_of_bytes"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.LStuck"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.ranges_apart"; "Stdlib.Lists.List.tl"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.SCDisj"; "Stdlib.Lists.List.app_assoc"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.lit_strip"; "Corelib.Init.Logic.or_introl"; "Corelib.Init.Logic.or_intror"; "Stdlib.ZArith.Zdiv.Zplus_mod_idemp_r"; "Stdlib.ZArith.Zdiv.Zplus_mod_idemp_l"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.know_ok"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.find_range"; "Stdlib.Lists.List.Forall_cons_iff"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.KWord"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.KZero"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.KBlob"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.KImg"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.KAlign"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.KRange"; "Corelib.BinNums.PosDef.Pos.add"; "Stdlib.ZArith.BinInt.Z.pos_sub"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.lit_strip_val"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.shifted_bound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.KWr"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.KDisj"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.KFill"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.KUnk"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.u_lit64"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.Z_land_range"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.two64_eq"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.v_or"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.Z_lor_range"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.alu_or"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.v_xor"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.Z_lxor_range"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.alu_xor"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.v_sltu"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.alu_sltu"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.v_slt"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.alu_slt"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.lit_shamt"; "Stdlib.ZArith.BinInt.Z.le_lt_trans"; "Stdlib.ZArith.BinInt.Z.div_le_upper_bound"; "Stdlib.micromega.RingMicromega.PsatzSquare"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.bv_signed_small"; "stdpp.bitvector.definitions.bv_swrap_small"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.v_addw"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.u_small_id"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.swrap32_small"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.swrap32_shift"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.w_addw"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.v_subw"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.w_subw"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.mod32_of_mod64"; "Stdlib.ZArith.BinInt.Z.mul_nonneg_nonneg"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.bv_wrap32_mod"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.v_mulhu"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.m_mulhu"; "Stdlib.ZArith.BinInt.Z.eqb_neq"; "stdpp.bitvector.definitions.bv_divu"; "stdpp.bitvector.definitions.bv_divu_unsigned"; "stdpp.bitvector.definitions.bv_modu"; "stdpp.bitvector.definitions.bv_modu_unsigned"; "Stdlib.ZArith.BinInt.Z.le_trans"; "Stdlib.ZArith.BinInt.Z.mod_le"; "Corelib.Classes.Morphisms.subrelation_proper"; "Stdlib.ZArith.BinInt.Z.Proper_instance_0"; "Corelib.Program.Basics.flip"; "Corelib.Program.Basics.impl"; "Corelib.Classes.Morphisms.subrelation_respectful"; "Corelib.Classes.Morphisms.subrelation_refl"; "Corelib.Classes.Morphisms.flip2"; "Corelib.Classes.Morphisms.iff_flip_impl_subrelation"; "Stdlib.ZArith.BinInt.Z.mul_le_mono_nonneg_r"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.u_ext_zx"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.bv_swrap_hi"; "Stdlib.micromega.ZifyClasses.not_morph"; "Stdlib.ZArith.Znat.N2Z.inj_iff"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.blob_bytes"; "Stdlib.Arith.PeanoNat.Nat.le_min_l"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.clampi"; "Stdlib.ZArith.BinInt.Z.mod_unique_pos"; "Stdlib.ZArith.BinInt.Z.ltb_ge"; "Stdlib.ZArith.BinInt.Z.log2_up"; "Stdlib.ZArith.BinInt.Z.eq_dec"; "Corelib.Init.Specif.sumbool"; "Stdlib.ZArith.BinInt.Z.log2_up_spec"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.mask_cover"; "Stdlib.ZArith.BinInt.Z.log2_up_nonneg"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.pow_cover"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.Z_bounded_by_bits"; "Stdlib.ZArith.BinInt.Z.lor_nonneg"; "Corelib.Init.Datatypes.orb"; "Stdlib.ZArith.BinInt.Z.lor_spec"; "Stdlib.ZArith.BinInt.Z.lxor_nonneg"; "Stdlib.micromega.Tauto.IFF"; "Corelib.Init.Datatypes.xorb"; "Stdlib.ZArith.BinInt.Z.lxor_spec"; "Stdlib.ZArith.Zbitwise.Z.add_lor_land"; "Stdlib.ZArith.BinInt.Z.ldiff"; "Stdlib.ZArith.BinInt.Z.lor_ldiff_and"; "Corelib.Init.Datatypes.negb"; "Stdlib.ZArith.BinInt.Z.ldiff_spec"; "Stdlib.ZArith.BinInt.Z.ldiff_nonneg"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.land_le_l"; "Stdlib.ZArith.BinInt.Z.land_comm"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.land_le_r"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.lor_ge_l"; "Stdlib.ZArith.BinInt.Z.lor_comm"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.lin_range"; "Stdlib.ZArith.BinInt.Z.leb_gt"; "Stdlib.ZArith.BinInt.Z.mul_sub_distr_r"; "Stdlib.ZArith.BinInt.Z.sub_1_r"; "Stdlib.Bool.Bool.andb_false_intro1"; "Stdlib.ZArith.BinInt.Z.shiftl_spec_low"; "Corelib.Init.Datatypes.andb_true_intro"; "Stdlib.Bool.Bool.andb_false_intro2"; "Stdlib.ZArith.BinInt.Z.testbit_ones"; "Stdlib.ZArith.BinInt.Z.shiftl_spec_high"; "Stdlib.ZArith.BinInt.Z.pow_nonzero"; "Stdlib.Bool.Bool.andb_true_r"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.testbit_mask"; "Stdlib.ZArith.Zdiv.Z_div_mult"; "Stdlib.ZArith.BinInt.Z.gt"; "Stdlib.micromega.RingMicromega.OpGt"; "Stdlib.ZArith.BinInt.Z.div_small"; "Stdlib.ZArith.BinInt.Z.div_add_l"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.ZBits.testbit_drop_low"; "Stdlib.ZArith.BinInt.Z.testbit_true"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.erange_f"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.lin_trivial"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.zdiv64"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.zmod64"; "Stdlib.ZArith.BinInt.Z.log2"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.zsigned64"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.two64m1"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.find_range_sound"; "Corelib.Init.Datatypes.Eq"; "Corelib.Init.Datatypes.Lt"; "Corelib.Init.Datatypes.Gt"; "Corelib.BinNums.PosDef.Pos.compare"; "Corelib.Init.Datatypes.CompOpp"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.zdiv64_eq2"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.lin_range_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.zmod64_eq"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.mod_wrap_hi"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.u_add64"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.mod_wrap_neg"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.u_sub64"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.lit_shamt_sound"; "Corelib.BinNums.PosDef.Pos.mul"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.u_sll64"; "Stdlib.micromega.Tauto.FF"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.u_slt64"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.u_sltu64"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.lxor_cover"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.u_xor64"; "Stdlib.ZArith.BinInt.Z.div_le_mono"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.u_srl64"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.u_sra64_nonneg"; "Stdlib.ZArith.BinInt.Z.max_lub"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.lor_ge_r"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.lor_cover"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.u_or64"; "Stdlib.ZArith.BinInt.Z.land_nonneg"; "Corelib.Init.Logic.proj1"; "Stdlib.ZArith.BinInt.Z.log2_nonneg"; "Stdlib.ZArith.BinInt.Z.ones_equiv"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.land_highmask"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.u_and64"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.u_addw_small"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.u_subw_small"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.u_sllw_small"; "Stdlib.Bool.Bool.orb_prop"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.u_srlw_small"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.u_sraw_small"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.u_mul64"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.u_mulhu64"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.u_divu64"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.u_remu64"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.u_ext_sx0_small"; "Corelib.BinNums.PosDef.Pos.of_succ_nat"; "Stdlib.ZArith.BinInt.Z.pow_pos"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.u_ext_sx0_high"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.u_ext_zx0_small"; "Corelib.BinNums.PosDef.Pos.pred_double"; "Corelib.Numbers.BinNums.xO"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.u_blob_zx"; "Stdlib.Lists.List.filter"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.is_factb"; "Stdlib.Lists.List.In"; "Stdlib.Lists.List.Forall_forall"; "Stdlib.Lists.List.filter_In"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.facts_of"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.facts_of_filter"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.erange0"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.erange_f_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.erange_fuel"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.facts_of_ok"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.deand"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.u_add_eqm"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.ctz_fuel"; "Stdlib.ZArith.BinInt.Z.divide"; "Stdlib.ZArith.BinInt.Z.pow_0_r"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.ctz_fuel_sound"; "Stdlib.omega.PreOmega.Z.divide_alt"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.ctz64"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.ctzp"; "Stdlib.ZArith.BinInt.Pos2Z.pos_is_pos"; "Corelib.Numbers.BinNums.xI"; "Stdlib.ZArith.BinInt.Pos2Z.inj_xO"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.ctzp_sound"; "Stdlib.setoid_ring.Ring_polynom.PEopp"; "Stdlib.ZArith.BinInt.Pos2Z.opp_pos"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.ctzq"; "Stdlib.setoid_ring.Ring_polynom.PEsub"; "Stdlib.ZArith.BinInt.Z.mul_assoc"; "Stdlib.ZArith.Zdiv.Zmod_eq_full"; "Stdlib.ZArith.BinInt.Z.pow_lt_mono_r"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.and_mask_align"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.atom_galign"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.ctzq_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.divide_mod_two64"; "Stdlib.ZArith.BinInt.Z.divide_1_l"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.and_mask_align_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.terms_galign"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.atom_galign_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.pow2_divide_le"; "Stdlib.setoid_ring.Algebra_syntax.equality"; "Stdlib.setoid_ring.Ncring.eq_notation"; "Stdlib.setoid_ring.Ncring_initial.Zops"; "Stdlib.ZArith.BinInt.Z.divide_transitive"; "Corelib.Classes.Morphisms.reflexive_proper_proxy"; "Stdlib.ZArith.BinInt.Z.divide_reflexive"; "Stdlib.setoid_ring.Ncring.ring_plus_comp"; "Stdlib.setoid_ring.Ncring_initial.Zr"; "Stdlib.setoid_ring.Ncring.ring_mult_comp"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.lin_galign"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.terms_galign_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.round_itv"; "Stdlib.ZArith.BinInt.Z.lt_succ_r"; "Stdlib.ZArith.BinInt.Z.div_le_lower_bound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.erange"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.erange0_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.lin_galign_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.round_itv_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.deand_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.base_range"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.erange_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.zlit64"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.lin_nowrap"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.lins_e"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.lins_e_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.lsub_e"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.find_align"; "Stdlib.ZArith.BinInt.Z.divide_sub_r"; "Stdlib.ZArith.BinInt.Z.divide_mul_l"; "Stdlib.ZArith.BinInt.Z.mod_eq"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.ealign0"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.find_align_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.ctz64_sound"; "Stdlib.ZArith.BinInt.Z.divide_trans"; "Stdlib.ZArith.BinInt.Z.mod_divide"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.divide_mod64"; "Stdlib.ZArith.BinInt.Z.divide_add_r"; "Stdlib.ZArith.BinInt.Z.mul_divide_mono_r"; "Stdlib.ZArith.BinInt.Z.shiftl_lor"; "Stdlib.ZArith.BinInt.Z.shiftr_spec"; "Stdlib.ZArith.BinInt.Z.le_ge_cases"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.find_and_atom_k"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.find_and_atom"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.find_and_atom_k_some"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.fold_lins_e_sg_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.pageup_low_k"; "Stdlib.ZArith.BinInt.Z.log2_spec"; "Stdlib.ZArith.BinInt.Z.bit_log2"; "Stdlib.ZArith.BinInt.Z.log2_unique"; "Stdlib.ZArith.BinInt.Z.le_gt_cases"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.u_and_mask"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.pageup_low"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.pageup_low_k_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.pageup_low_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.pageup_align"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.ealign0_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.pageup_align_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.ealign"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.srl_rem"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.srl_expand"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.highmask_s"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.lin_nowrap_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.u_srl_lit"; "Stdlib.ZArith.Zdiv.Z_div_exact_2"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.u_srl_rem"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.ealign_sound"; "Stdlib.ZArith.BinInt.Z.mul_0_r"; "Stdlib.ZArith.BinInt.Z.sub_0_r"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.fold_lins_e_sound"; "Stdlib.PArith.BinPos.Pos.size"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.sfact"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.sfact_ok"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.srl_expand_sound"; "Corelib.Lists.ListDef.Forall_nil"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.sum_fact_x"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.fact_nowrap"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.sum_facts"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.fact_nowrap_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.sum_fact_x_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.sub_fact"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.sum_subst"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.fact_quot"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.sub_fact_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.lin_test_rel"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.sum_facts_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.sum_subst_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.lin_test"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.lin_test_rel_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.lin_brange"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.lin_srange"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.srl_scale_need"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.has_srl"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.zcdiv"; "Stdlib.ZArith.BinInt.Z.leb_spec"; "Stdlib.ZArith.BinInt.Z.compare"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.tden_map_scale"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.xlo"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.zlit64_eq"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.lin_brange_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.lin_srange_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.xhi"; "Corelib.Init.Logic.proj2"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.lin_nowrapR"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.lin_test_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.lin_srange_exact"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.lin_apart"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.shares_var"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.lin_apart0"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.lin_nowrapR_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.lsub_e_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.xterms"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.xt_nowrap"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.xt_const"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.xt_lin"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.xt_den"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.lin_ge0_scaled"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.lin_align"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.lin_align_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.lin_slack"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.slack_test"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.lin_slack_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.slack_nonneg"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.slack_test2"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.lin_ge0"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.xt_lin_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.slack_test_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.slack_test2_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.lin_ge0_scaled_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.xinside"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.xinside0"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.lin_ge0_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.novars"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.xinside_num"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.xlo_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.xhi_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.base_range_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.sub_itv"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.xinside_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.kdisj_apart"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.if3_cases"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.sub_itv_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.kdisj_apart_sound_gen"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.kdisj_apart_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.lin_apart_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.sub_itv_x"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.kdisj_apart_x"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.sub_itv_x_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.know_lookupA0"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.SCInside"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.fill_lit"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.know_lookupA0_acc"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.know_bytes_lit"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.LMiss"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.know_lookupA"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.know_lookupA_acc"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.know_lookup"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.RInside"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.RDisjoint"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.RPartial"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.RUnknown"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.flat_u"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.w_add_nat"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.rdn_slice"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.SeqExec.rdn_wbytes_hit"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CatExec.length_N_to_le_bytes"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.slice_word_bytes"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.log_flat"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.log_byte_lit"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.rel_lit_inside"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.Lookups.word_byte_at"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.rdn_inside_wbytes"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.rel_lit_disjoint"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CatExec.rdn_wbytes_out"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.Lookups.log_byte_lit_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.Lookups.rdn_cons1"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.SymExec.Z_to_bv64_wrap_l"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.w_add_1"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.length_firstn_skipn"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.ext_hit_value"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.mkExt_denot"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.Lookups.log_bytes_lit_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.rdn_length"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.zbytes_map"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.ranges_apart_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.log_lookup_acc"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.scs_denot_app"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.scs_denot_cons"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.elenZ_elen"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.u_lit0"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.KLookup.u8_lit"; "Stdlib.Lists.List.map_repeat"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.KLookup.map_unsigned_repeat8"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.rdn_pointwise"; "Stdlib.Lists.List.repeat_length"; "Stdlib.Lists.List.nth_repeat"; "Stdlib.Lists.List.nth_indep"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.KLookup.fill_lit_denot"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.adenot_shift"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.extz_0"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.bytes_le_to_Z_repeat0"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.elenZ_lit"; "Stdlib.Arith.PeanoNat.Nat.ltb_lt"; "Stdlib.Lists.List.nth_skipn"; "Stdlib.Lists.List.nth_firstn"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.estart_lit0"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.rdn_img"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.KLookup.fill_read"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.know_byte_lit"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.word_byte_at"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.KLookup.rdn_one"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.KLookup.Z_to_bv8_mod"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.KLookup.know_byte_lit_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.rdn_cons1"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.KLookup.know_lookupA0_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.KLookup.know_bytes_lit_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.KLookup.know_lookupA_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.split_lit"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.v_addi"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.to_saddr"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.land_align_mask"; "Stdlib.ZArith.Znumtheory.Zdivide_mod"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.coeffs_divk"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.lin_lowbits_kn"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.coeffs_divk_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.ldiv_terms"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.sx32"; "Stdlib.ZArith.BinInt.Z.add_simpl_r"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.zfast"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.zalu"; "Corelib.Classes.Morphisms.trans_sym_co_inv_impl_morphism"; "Corelib.Classes.RelationClasses.Equivalence_PER"; "Corelib.Classes.RelationClasses.eq_equivalence"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.land_63"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.land64_eq"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.zfastw"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.zaluw"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.u_swrap32"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.land32_eq"; "Stdlib.ZArith.Zdiv.Zmult_mod_idemp_l"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.land_31"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.zfastm"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.zmd"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.wrap64_eq"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.Z_to_bv_wrap64"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.zfast_eq"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.wrap64_range"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.zalu_l"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.zfastw_eq"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.zaluw_l"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.zfastm_eq"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.zmd_l"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.shamt_of_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.unlin_lsll_amt"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.alu_srl_amt"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.u_lit_mod"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.alu_sra_amt"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.is_lit_some"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.zalu_l_eq"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.unlin_ladd"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.unlin_lsub"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.mkAlu"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.end_hi"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.mkAlu_denot"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.ranges_apart_x"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.end_hi_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.kdisj_apart_x_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.w_shift_amt"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.zaluw_l_eq"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.mkAluw"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.zmd_l_eq"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.unlin_lmul_l"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.unlin_lmul_r"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.mkMd"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.zmdw"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.mkMdw"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.lsplit_divc"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.lin_nowrap_l"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.ldiv_terms_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.mkSrl"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.mkSrl_denot"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.mkMd_denot"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.lin_lowbits_kn_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.mod_pow2_mod_pow2"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.lowbits"; "Stdlib.ZArith.Zdiv.Zminus_mod"; "Corelib.BinNums.PosDef.Pos.lxor"; "Corelib.BinNums.NatDef.N.succ_pos"; "Corelib.BinNums.NatDef.N.lxor"; "Corelib.BinNums.PosDef.Pos.pred_N"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.lxor_mod_pow2"; "Corelib.BinNums.PosDef.Pos.lor"; "Corelib.BinNums.NatDef.N.ldiff"; "Corelib.BinNums.NatDef.N.land"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.lor_mod_pow2"; "Stdlib.ZArith.BinInt.Z.land_0_r"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.land_mod_pow2"; "Corelib.BinNums.PosDef.Pos.land"; "Corelib.BinNums.NatDef.N.lor"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.u_mul_eqm"; "Stdlib.ZArith.BinInt.Z.mul_mod_idemp_l"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.lsplit_div"; "Stdlib.ZArith.BinInt.Z.sub_diag"; "Stdlib.ZArith.Zdiv.Zminus_mod_idemp_r"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.eqm_refl"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.split_mod_core"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.and_highmask_val"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.and_high_split"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.and_lowmask_val"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.and_low_split"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.and_mask_id"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.and_highmask_srl"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.lsplit_div_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.and_high_split_denot"; "Stdlib.ZArith.BinInt.Z.add_assoc"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.and_lowmask_zero"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.lowbits_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.and_low_split_denot"; "Stdlib.ZArith.BinInt.Z.add_1_r"; "Stdlib.ZArith.BinInt.Z.bits_above_log2"; "Stdlib.ZArith.BinInt.Z.log2_land"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.mkAnd0"; "Stdlib.Bool.Bool.eq_true_iff_eq"; "Corelib.Classes.RelationClasses.iff_equivalence"; "Corelib.Classes.RelationClasses.iff_Transitive"; "Stdlib.Bool.Bool.andb_true_iff"; "Corelib.Classes.Morphisms_Prop.and_iff_morphism"; "Corelib.Classes.RelationClasses.iff_Reflexive"; "Stdlib.ZArith.BinInt.Z.testbit_neg_r"; "Stdlib.ZArith.BinInt.Z.shiftl_spec"; "Stdlib.ZArith.BinInt.Z.log2_lt_pow2"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.testbit_pow_sub"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.narrow_mask"; "Corelib.BinNums.PosDef.Pos.eqb"; "Stdlib.ZArith.BinInt.Z.pow_lt_mono_r_iff"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.land_mask_narrow"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.mkAnd0_denot"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.mkAnd"; "Stdlib.ZArith.BinInt.Z.land_assoc"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.mkAnd_denot"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.mkAndK"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.itv_ltu"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.itv_lts"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.itv_ltu_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.bv_signed_hi"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.range_branch"; "LinuxProcessSemantics.Riscv.Instr.BC_EQ"; "LinuxProcessSemantics.Riscv.Instr.BC_NE"; "Stdlib.Bool.Bool.negb_true_iff"; "Stdlib.Bool.Bool.negb_false_iff"; "LinuxProcessSemantics.Riscv.Instr.BC_LT"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.itv_lts_sound"; "LinuxProcessSemantics.Riscv.Prelude.bv_lts"; "LinuxProcessSemantics.Riscv.Instr.BC_GE"; "Corelib.Init.Datatypes.option_map"; "LinuxProcessSemantics.Riscv.Instr.BC_LTU"; "LinuxProcessSemantics.Riscv.Prelude.bv_ltu"; "LinuxProcessSemantics.Riscv.Instr.BC_GEU"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.cond_on_eq"; "Stdlib.ZArith.BinInt.Z.eqb_refl"; "Stdlib.ZArith.BinInt.Z.ltb_irrefl"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.lin_branch"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.decide_branch"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.diff_branch"; "Stdlib.ZArith.BinInt.Z.eqb_spec"; "Corelib.Init.Datatypes.reflect"; "Stdlib.ZArith.ZArith_dec.Z_lt_le_dec"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.range_branch_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.cond_on_eq_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.lin_branch_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.lit_branch"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.or_disjoint"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.land_aligned_small"; "Stdlib.ZArith.BinInt.Z.lnot"; "Stdlib.ZArith.BinInt.Z.land_lnot_diag"; "Stdlib.ZArith.BinInt.Z.lnot_spec"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.or_as_and_not_plus"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.mkAndK_denot"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.or_disjoint_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.or_R1"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.mkOr"; "Stdlib.ZArith.Zbitwise.Z.sub_lxor_2rlandn"; "Stdlib.ZArith.ZArith_dec.Z_lt_dec"; "Stdlib.ZArith.BinInt.Z.lt_le_trans"; "Stdlib.ZArith.BinInt.Z.lxor_comm"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.eval_closed"; "stdpp.bitvector.definitions.bv_sub"; "stdpp.bitvector.definitions.bv_shiftl"; "stdpp.bitvector.definitions.bv_and"; "stdpp.bitvector.definitions.bv_xor"; "stdpp.bitvector.definitions.bv_shiftr"; "stdpp.bitvector.definitions.bv_ashiftr"; "stdpp.bitvector.definitions.bv_or"; "stdpp.bitvector.definitions.bv_mul"; "LinuxProcessSemantics.Riscv.Prelude.bv_mulhss"; "LinuxProcessSemantics.Riscv.Prelude.bv_mulhsu"; "LinuxProcessSemantics.Riscv.Prelude.bv_mulhuu"; "stdpp.bitvector.definitions.bv_quots"; "stdpp.bitvector.definitions.bv_rems"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.esubst"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.all_eval_to"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.evalS"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.eval_closed_range"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.all_eval_toS"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.evalS_eq"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.probeS"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.conc_try"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.closedb"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.evalS_def"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.conc_limit"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.all_eval_toS_eq"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.all_eval_to_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.eval_closed_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.esubst_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.concretize"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.nubE"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.subexprs"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.conc_try_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.concretize_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.foldK"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.decide_branch_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.mkSlt"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.mkSlt_denot"; "Stdlib.ZArith.BinInt.Z.lxor_nilpotent"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.lxor_ones64"; "Stdlib.ZArith.BinInt.Z.lor_diag"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.mkOr_denot"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.mkAluK0"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.mkAluK0_denot"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.foldK_denot"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.mkAluK"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.pow2_log"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.pow2_log_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.mkAluK_denot"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.mkMdK"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.zsx32"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.sx32_stable"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.zband32"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.bv_swrap_congr"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.swrap32_neg"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.mkAluw_denot"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.mkAluwK0"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.mkAluwK0_denot"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.mkAluwK"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.extK0"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.extK0_denot"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.extK"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.flat_sc"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.SCFlat"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.conc_expr"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.enum_branch"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.cond_probe"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.to_saddr_denot"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.to_saddrK"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.sym_state"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.mkst"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.asanreflect_fx"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.s_pc"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.s_log"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.s_regs"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.s_know"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.SymStepR.mkstR"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.StepSound.resv_denot"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.s_resv"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.StepSound.st_ok"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.StepSound.st_okR"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.clr"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.s_clean"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.SymStepR.msize_bytes"; "LinuxProcessSemantics.Riscv.Instr.awidth"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.SymStepR.amo_nbytes"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.amo_sz"; "LinuxProcessSemantics.Riscv.Instr.AW"; "LinuxProcessSemantics.Riscv.Instr.AD"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.SymStepR.amo_msize"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.StepSound.wrap_swrap"; "stdpp.bitvector.definitions.bv_wrap_bv_wrap"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.sext32_unsigned"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.low32_unsigned"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.scripts"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.sym_read"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.log_lookup_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.sc_hints"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.SCR"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.sc_dirs"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.sc_reads"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.s_next"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.SCReadBase"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.flat_sc_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.extK_denot"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.know_lookupA_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.storeok_sc"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.wr_covered_br"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.SCStoreOk"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.wr_covered"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.wr_covered_br_eq"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.resv_inval"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.SymStepR.resv_inval_w"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.saddr_eqb_eq"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.amo_alignedb"; "LinuxProcessSemantics.Riscv.Sem.amo_bytes"; "LinuxProcessSemantics.Riscv.Instr.amoop"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.amo_aluop"; "LinuxProcessSemantics.Riscv.Sem.amo_val"; "LinuxProcessSemantics.Riscv.Instr.AMO_SWAP"; "LinuxProcessSemantics.Riscv.Instr.AMO_ADD"; "LinuxProcessSemantics.Riscv.Instr.AMO_XOR"; "LinuxProcessSemantics.Riscv.Instr.AMO_AND"; "LinuxProcessSemantics.Riscv.Instr.AMO_OR"; "LinuxProcessSemantics.Riscv.Instr.AMO_MIN"; "LinuxProcessSemantics.Riscv.Instr.AMO_MAX"; "LinuxProcessSemantics.Riscv.Instr.AMO_MINU"; "LinuxProcessSemantics.Riscv.Instr.AMO_MAXU"; "LinuxProcessSemantics.LinuxProcessSem.BvBase.le_bytes_to_word"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.StepSound.low32_sext64_32"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.SeqExec.store_bytes_low32"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.StepSound.amo_val_alu32"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.mkAluwK_denot"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.StepSound.amo_val_swap"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.StepSound.amo_val_alu64"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.SymStepR.amo_store_bytes"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.amo_newval"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.fetch_word"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.is_ecall"; "LinuxProcessSemantics.Riscv.Instr.instr"; "LinuxProcessSemantics.Riscv.DecodeC.decode_any"; "LinuxProcessSemantics.Riscv.Instr.Load"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.stepres"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.sym_step"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.SOk"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.StepSound.msize_bytes_range"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_result"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.step"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.MachineOk"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.to_saddrK_denot"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.SSR"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.SStop"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.StepSound.sym_read_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.SymStepR.stepR_load"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.StepSound.msize_bytes_R"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.SymExec.v_addi_lit"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.regs_ok_upd"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.load_result_val"; "LinuxProcessSemantics.Riscv.Instr.Store"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.StepSound.storeok_sc_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.StoreOk.store_ok_mono"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.mem_denot_grows"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.SymStepR.stepR_store"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.StepSound.resv_inval_sound"; "LinuxProcessSemantics.Riscv.Instr.Lr"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.amo_sx"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.StepSound.v_addi_0"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.StepSound.amo_alignedb_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.SymStepR.stepR_lr"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.StepSound.amo_nbytes_sz"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.StepSound.amo_msize_sz"; "LinuxProcessSemantics.Riscv.Instr.Sc"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.SymStepR.stepR_sc_ok"; "LinuxProcessSemantics.Riscv.Instr.Amo"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.SymStepR.stepR_amo"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.StepSound.amo_store_bytes_newval"; "LinuxProcessSemantics.Riscv.Instr.Lui"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.sset"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.v_lui"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.SymStepR.stepR_lui"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.Z_to_bv64_u"; "LinuxProcessSemantics.Riscv.Instr.Auipc"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.v_auipc"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.SymStepR.stepR_auipc"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.SymExec.v_auipc_lit"; "LinuxProcessSemantics.Riscv.Instr.Jal"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.btgt"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.SymStepR.stepR_jal_link"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.SymExec.btgt_lit"; "LinuxProcessSemantics.Riscv.Instr.Jalr"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.conc_expr_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.SeqExec.v_jalr"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.SymStepR.stepR_jalr"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.jalr_tgtZ"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.SymExec.jalr_tgt_lit"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.Z_to_bv64_mod"; "LinuxProcessSemantics.Riscv.Instr.Branch"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.sjump"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.SymStepR.stepR_branch_tk_gen"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.SymStepR.stepR_branch_ft_gen"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.SCBr"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.enum_branch_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.StepSound.sym_step_sound_load"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.StepSound.sym_step_sound_store"; "LinuxProcessSemantics.Riscv.Instr.OpImm"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.SymStepR.stepR_opimm_gen"; "LinuxProcessSemantics.Riscv.Instr.ShiftImm"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.SymStepR.stepR_shiftimm_gen"; "LinuxProcessSemantics.Riscv.Instr.Op"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.SymStepR.stepR_op_gen"; "LinuxProcessSemantics.Riscv.Instr.OpImm32"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.SymStepR.stepR_opimm32_gen"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.SymExec.sext32_low32"; "LinuxProcessSemantics.Riscv.Instr.ShiftImm32"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.SymStepR.stepR_shiftimm32_gen"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.SymExec.zext32_low32"; "LinuxProcessSemantics.Riscv.Instr.Op32"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.SymStepR.stepR_op32_gen"; "LinuxProcessSemantics.Riscv.Instr.Fence"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.SymStepR.stepR_fence"; "LinuxProcessSemantics.Riscv.Instr.FenceI"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.SymStepR.stepR_fencei"; "LinuxProcessSemantics.Riscv.Instr.Ecall"; "LinuxProcessSemantics.Riscv.Instr.Ebreak"; "LinuxProcessSemantics.Riscv.Instr.Mul"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.SymStepR.stepR_mul_gen"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.mkMdK_denot"; "LinuxProcessSemantics.Riscv.Instr.Mul32"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.SymStepR.stepR_mul32_gen"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.mkMdw_denot"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.StepSound.sym_step_sound_lr"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.StepSound.sym_step_sound_sc"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.StepSound.sym_step_sound_amo"; "LinuxProcessSemantics.Riscv.Instr.csrop"; "LinuxProcessSemantics.Riscv.Instr.Csr"; "LinuxProcessSemantics.Riscv.Instr.CsrI"; "LinuxProcessSemantics.Riscv.Instr.ffmt"; "LinuxProcessSemantics.Riscv.Instr.FLoad"; "LinuxProcessSemantics.Riscv.Instr.FStore"; "LinuxProcessSemantics.Riscv.Instr.fmaop"; "LinuxProcessSemantics.Riscv.Instr.Fma"; "LinuxProcessSemantics.Riscv.Instr.fariop"; "LinuxProcessSemantics.Riscv.Instr.Fari"; "LinuxProcessSemantics.Riscv.Instr.Fsqrt"; "LinuxProcessSemantics.Riscv.Instr.fsgnop"; "LinuxProcessSemantics.Riscv.Instr.Fsgnj"; "LinuxProcessSemantics.Riscv.Instr.fminmaxop"; "LinuxProcessSemantics.Riscv.Instr.Fminmax"; "LinuxProcessSemantics.Riscv.Instr.fcmpop"; "LinuxProcessSemantics.Riscv.Instr.Fcmp"; "LinuxProcessSemantics.Riscv.Instr.fcvt_ty"; "LinuxProcessSemantics.Riscv.Instr.Fcvt"; "LinuxProcessSemantics.Riscv.Instr.fmvdir"; "LinuxProcessSemantics.Riscv.Instr.Fmv"; "LinuxProcessSemantics.Riscv.Instr.Fclass"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.StepSound.sym_step_soundR"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.StepSound.st_ok_R"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.sidecond_eqb"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.SCEq"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.sc_mem"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.sidecond_eqb_eq"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.sc_add"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.sc_mem_In"; "Corelib.Classes.Morphisms.iff_impl_subrelation"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.sym_exec_go"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.st_okR"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CatSim.msteps"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.s_clean_None"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CatSim.mst_refl"; "Stdlib.Lists.List.existsb"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.sc_add_denot"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.sym_step_soundR"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CatSim.mst_step"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.resv_denot"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_svc_pending"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.ExecSound.sym_exec_go_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.sym_exec"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.st_ok"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.st_ok_R"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.ExecSound.sym_exec_soundR"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.st_okR_ok"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.ExecSound.sym_exec_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.sym_execS_go"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.scr_nil"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.ExecSound.sym_execS_go_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.sym_execS"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.ExecSound.sym_execS_soundR"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.ExecSound.sym_execS_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.itab"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.itab_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.sym_execT_go"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.itab_lookup"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.itab_entry"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.ExecSound.sym_execT_go_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.sym_execT"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.ExecSound.sym_execT_soundR"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.ExecSound.sym_execT_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.XSound.eagree"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.XSound.eupd"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.evars_lt"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.XSound.st_okX"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.XSound.eagree_refl"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.XSound.eagree_trans"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_regs"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_mem"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.XSound.rd1"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.SeqExec.rdn_nth"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.zf_covers"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.kentry_overlay"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.XSound.zf_covers_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.kentry_readable"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.XSound.kentry_overlay_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.XSound.rdn_rd1"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.know_byte_cov"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.know_bytes_cov"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.XSound.know_byte_cov_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.kn_readable"; "Stdlib.Lists.List.existsb_exists"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.XSound.kentry_readable_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.XSound.know_bytes_cov_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.XSound.rdn_defined"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.kn_overlay"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.StoreOk.store_ok_of_all"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.wview"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.find_segment"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.seg_writable"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.segment_byte_at"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.seg_bytes"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.seg_base"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.find_readbase"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.x_filter"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.x_dischargeable"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.XSound.kn_readable_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.XSound.kn_overlay_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.XSound.edenot_evars_lt"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.rd_of"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.esize_le"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.XSound.eagree_upd"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.XSound.eagree_le"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.XSound.st_okR_parts"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.regs_ok_pin"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.XSound.eupd_at"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.cap_rd"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.sym_stepX"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.XSound.st_okX_R"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.XSound.x_filter_nil"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.XSound.find_readbase_In"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.XSound.x_discharge_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.XSound.cap_rd_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.sym_execTX_go"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.XSound.sym_stepX_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CatSim.msteps_trans"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.XSound.st_okX_clr"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.XSound.sym_execTX_go_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.sym_execTX"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.XSound.sym_execTX_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.sym_execSX_go"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.XSound.sym_execSX_go_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.sym_execSX"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CatExec.wbytes_below"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CatExec.wbytes_above"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.wbytes_out"; "Corelib.Init.Logic.and_ind"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.CarrySound.zf_kind"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.kcut"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.u_sub_eqm"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.CarrySound.kcut_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.CarrySound.zf_kind_zero"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.CarrySound.zf_kind_fill"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.CarrySound.zf_kind_unk"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.kzero_cut"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.CarrySound.kzero_cut_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.in_sides"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.disj_sides"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.in_sides_x"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.disj_sides_x"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.in_sides_br"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.disj_sides_br"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.in_sides_x_br"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.CarrySound.in_sides_eq"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.in_sides_br_eq"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.disj_sides_br_eq"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.CarrySound.in_sides_x_eq"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.in_sides_x_br_eq"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.disj_sides_x_br"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.disj_sides_x_br_eq"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.sp_rng"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.SPrep"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.sp_D"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.sp_h1"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.sp_Dx"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.ranges_apart_p"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.mk_sprep"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.kword_cut"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.ktrim"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.CarrySound.ranges_apart_p_eq"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.prune1p"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.prune1"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.prunep"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.prune"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.CarrySound.prune1p_eq"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.sprep"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.kbase"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.prune1pc"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.ranges_apart_pc"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.CarrySound.ranges_apart_pc_eq"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.CarrySound.br_cache_ok"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.br_lookup"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.prunepc"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.CarrySound.prune1pc_eq"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.CarrySound.br_lookup_ok"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.CarrySound.Forall_app_intro"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.CarrySound.Forall_one"; "Corelib.Classes.RelationClasses.flip_Reflexive"; "Corelib.Classes.RelationClasses.impl_Reflexive"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.CarrySound.zf_piece"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.prune_zf"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.CarrySound.ktrim_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.CarrySound.zf_frame"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.CarrySound.kcut_store"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.SymExec.Z_to_le_bytes_mod"; "Stdlib.Bool.Bool.orb_false_elim"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.CarrySound.word_slice_bytes"; "Stdlib.micromega.ZifyClasses.or_morph"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.ranges_apart_x_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.CarrySound.kentry_ok_frame"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.CarrySound.prune_zf_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.CarrySound.kword_cut_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.CarrySound.kimg_piece"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.CarrySound.kn_words_le8"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.CarrySound.prune1_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3K.AX2K.carry"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.CarrySound.prunepc_eq"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.CarrySound.prunep_eq"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.CarrySound.prune_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.CarrySound.know_ok_fill_intro_pt"; "Stdlib.Lists.List.nth_repeat_lt"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.CarrySound.wbytes_nth"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.rdn_ext"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.CarrySound.know_ok_unk_intro_pt"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3SoundK.AX2SK.CarrySound.kentry_ok_unk_grows"].

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.

Module AX2SK.
Import AX2K.
Export AX2K.

Lemma aluop_eqb_eq : forall a b, aluop_eqb a b = true -> a = b.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_001 ())).
Qed.

Lemma mulop_eqb_eq : forall a b, mulop_eqb a b = true -> a = b.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_002 ())).
Qed.

Lemma expr_eqb_eq : forall x y, expr_eqb x y = true -> x = y.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_003 ())).
Qed.

Lemma saddr_eqb_eq : forall a b, saddr_eqb a b = true -> a = b.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_004 ())).
Qed.

Lemma edenot_lit : forall E z, edenot E (ELit z) = Z_to_bv 64 z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_005 ())).
Qed.

Lemma alu64_add_0_r : forall v : word, alu64 ALU_ADD v (Z_to_bv 64 0) = v.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_006 ())).
Qed.

Lemma alu64_add_comm : forall a b : word, alu64 ALU_ADD a b = alu64 ALU_ADD b a.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_007 ())).
Qed.

Lemma alu64_sub_as_add : forall (v : word) y,
  alu64 ALU_SUB v (Z_to_bv 64 y) = alu64 ALU_ADD v (Z_to_bv 64 (- y)).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_008 ())).
Qed.

Definition eqm (a b : Z) : Prop := ltac2:(Rpl.RP.run_k (rplG ()) 2 (AxSymExec3SoundK_blobs1.kr_b_009 ())).

Lemma eqm_refl : forall a, eqm a a. Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_010 ())).
Qed.
Lemma eqm_sym : forall a b, eqm a b -> eqm b a. Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_011 ())).
Qed.
Lemma eqm_trans : forall a b c, eqm a b -> eqm b c -> eqm a c.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_012 ())).
Qed.
Lemma eqm_add : forall a b c d, eqm a b -> eqm c d -> eqm (a + c) (b + d).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_013 ())).
Qed.
Lemma eqm_mul_l : forall k a b, eqm a b -> eqm (k * a) (k * b).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_014 ())).
Qed.
Lemma eqm_mul_r : forall k a b, eqm a b -> eqm (a * k) (b * k).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_015 ())).
Qed.
Lemma eqm_mod : forall a, eqm (a mod 2 ^ 64) a.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_016 ())).
Qed.
Lemma two64z_eq : two64z = (2 ^ 64)%Z. Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_017 ())).
Qed.
Lemma eqm_snorm : forall k, eqm (snorm k) k.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_018 ())).
Qed.
Lemma eqm_Z_to_bv : forall a b, eqm a b -> Z_to_bv 64 a = Z_to_bv 64 b.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_019 ())).
Qed.
Lemma u_lit64a : forall z, bv_unsigned (Z_to_bv 64 z) = (z mod 2 ^ 64)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_020 ())).
Qed.
Lemma eqm_u_lit : forall z, eqm (bv_unsigned (Z_to_bv 64 z)) z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_021 ())).
Qed.

Section LinDenot.
Variable E : env.
Definition uE (e : expr) : Z := ltac2:(Rpl.RP.run_k (rplG ()) 1 (AxSymExec3SoundK_blobs1.kr_b_022 ())).

Fixpoint tden (ts : list (Z * expr)) : Z :=
  match ts with [] => 0 | (k, a) :: rest => k * uE a + tden rest end.
Definition lden (x : lin) : Z := ltac2:(Rpl.RP.run_k (rplG ()) 1 (AxSymExec3SoundK_blobs1.kr_b_023 ())).

Lemma lins_sound : forall k a ts, eqm (tden (lins k a ts)) (k * uE a + tden ts).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_024 ())).
Qed.

Lemma ladd_sound : forall x y, eqm (lden (ladd x y)) (lden x + lden y).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_025 ())).
Qed.

Lemma lscale_terms_sound : forall m ts, eqm (tden (lscale_terms m ts)) (m * tden ts).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_026 ())).
Qed.

Lemma lscale_sound : forall m x, eqm (lden (lscale m x)) (m * lden x).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_027 ())).
Qed.

Lemma u_add_eqm : forall x y : word, eqm (bv_unsigned (alu64 ALU_ADD x y)) (bv_unsigned x + bv_unsigned y).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_028 ())).
Qed.
Lemma u_sub_eqm : forall x y : word, eqm (bv_unsigned (alu64 ALU_SUB x y)) (bv_unsigned x - bv_unsigned y).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_029 ())).
Qed.
Lemma u_mul_eqm : forall x y : word, eqm (bv_unsigned (mul_div M_MUL x y)) (bv_unsigned x * bv_unsigned y).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_030 ())).
Qed.
Lemma u_sll_eqm : forall (x : word) s,
  eqm (bv_unsigned (alu64 ALU_SLL x (Z_to_bv 64 s))) (2 ^ (s mod 64) * bv_unsigned x).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_031 ())).
Qed.

Lemma lin_of_sound : forall e, eqm (lden (lin_of e)) (uE e).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_032 ())).
Qed.

Lemma lterm_sound : forall t, eqm (uE (lterm t)) (fst t * uE (snd t)).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_033 ())).
Qed.

Lemma lterms_sound : forall ts, eqm (uE (lterms ts)) (tden ts).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_034 ())).
Qed.

Lemma unlin_sound : forall x, eqm (uE (unlin x)) (lden x).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_035 ())).
Qed.

Lemma unlin_ladd : forall a b,
  edenot E (unlin (ladd (lin_of a) (lin_of b))) = alu64 ALU_ADD (edenot E a) (edenot E b).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_036 ())).
Qed.

Lemma unlin_lsub : forall a b,
  edenot E (unlin (ladd (lin_of a) (lscale (-1) (lin_of b)))) = alu64 ALU_SUB (edenot E a) (edenot E b).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_037 ())).
Qed.

Lemma unlin_lsll : forall a s,
  edenot E (unlin (lscale (2 ^ (s mod 64)) (lin_of a))) = alu64 ALU_SLL (edenot E a) (Z_to_bv 64 s).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_038 ())).
Qed.

Lemma unlin_lmul_l : forall x b,
  edenot E (unlin (lscale x (lin_of b))) = mul_div M_MUL (Z_to_bv 64 x) (edenot E b).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_039 ())).
Qed.

Lemma unlin_lmul_r : forall a y,
  edenot E (unlin (lscale y (lin_of a))) = mul_div M_MUL (edenot E a) (Z_to_bv 64 y).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_040 ())).
Qed.
End LinDenot.

Lemma coeffs_div_sound : forall E m ts, (0 < m)%Z -> coeffs_div m ts = true -> (tden E ts mod m = 0)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_041 ())).
Qed.

Lemma pow2_div_64 : forall k, (0 <= k <= 64)%Z -> (2 ^ k | 2 ^ 64)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_042 ())).
Qed.

Lemma eqm_mod_pow2 : forall a b k, (0 <= k <= 64)%Z -> eqm a b -> (a mod 2 ^ k = b mod 2 ^ k)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_043 ())).
Qed.

Lemma lin_lowbits_sound : forall E e k v, (0 <= k <= 64)%Z ->
  lin_lowbits e k = Some v -> (bv_unsigned (edenot E e) mod 2 ^ k = v)%Z /\ (0 <= v < 2 ^ k)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_044 ())).
Qed.

Lemma shamt_of_sound : forall E e bits s, (0 <= bits <= 64)%Z ->
  shamt_of e bits = Some s -> (bv_unsigned (edenot E e) mod 2 ^ bits = s)%Z /\ (0 <= s < 2 ^ bits)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_045 ())).
Qed.

Lemma alu_sll_amt : forall (x y : word) s, (bv_unsigned y mod 64 = s)%Z ->
  alu64 ALU_SLL x y = Z_to_bv 64 (bv_unsigned x * 2 ^ s).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_046 ())).
Qed.

Lemma alu_srl_amt : forall (x y y' : word), (bv_unsigned y mod 64 = bv_unsigned y' mod 64)%Z ->
  alu64 ALU_SRL x y = alu64 ALU_SRL x y'.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_047 ())).
Qed.

Lemma alu_sra_amt : forall (x y y' : word), (bv_unsigned y mod 64 = bv_unsigned y' mod 64)%Z ->
  alu64 ALU_SRA x y = alu64 ALU_SRA x y'.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_048 ())).
Qed.

Lemma w_shift_amt : forall op (x y y' : word),
  (op = ALU_SLL \/ op = ALU_SRL \/ op = ALU_SRA) ->
  (bv_unsigned y mod 32 = bv_unsigned y' mod 32)%Z ->
  (sext 64 (alu32 op (low32 x) (low32 y)) : word) = sext 64 (alu32 op (low32 x) (low32 y')).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_049 ())).
Qed.

Lemma u_lit_mod : forall s m, (0 <= s < 2 ^ 6)%Z -> (m = 64 \/ m = 32)%Z -> (s < m)%Z ->
  (bv_unsigned (Z_to_bv 64 s) mod m = s)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_050 ())).
Qed.

Lemma unlin_lsll_amt : forall E a (y : word) s, (bv_unsigned y mod 64 = s)%Z ->
  edenot E (unlin (lscale (2 ^ s) (lin_of a))) = alu64 ALU_SLL (edenot E a) y.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_051 ())).
Qed.

Lemma and_lowmask_val : forall (v : word) j, (0 <= j)%Z -> (j <= 64)%Z ->
  alu64 ALU_AND v (Z_to_bv 64 (2 ^ j - 1)) = Z_to_bv 64 (bv_unsigned v mod 2 ^ j).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_052 ())).
Qed.

Lemma is_lit_some : forall e z, is_lit e = Some z -> e = ELit z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_053 ())).
Qed.

Lemma slice_mod : forall a m k j, (0 <= k)%Z -> (0 <= j)%Z -> (k + j <= m)%Z ->
  (((a mod 2 ^ m) / 2 ^ k) mod 2 ^ j = (a / 2 ^ k) mod 2 ^ j)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_054 ())).
Qed.

Lemma Z_to_bv64_swrap64 : forall u, Z_to_bv 64 (bv_swrap 64 u) = Z_to_bv 64 u.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_055 ())).
Qed.

Lemma ext_val_full : forall sx (v : word), ext_val sx 0 8 v = v.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_056 ())).
Qed.

Lemma ext_Z_range : forall lo n z, (n <= 8)%nat ->
  (0 <= ext_Z false lo n z < 2 ^ 64)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_057 ())).
Qed.

Lemma ext_val_compose : forall sx lo n lo' n' (v : word),
  (lo + n <= n')%nat -> (n' <= 8)%nat ->
  ext_val sx lo n (ext_val false lo' n' v) = ext_val sx (lo' + lo) n v.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_058 ())).
Qed.

Lemma wrap64_mod : forall z, wrap64 z = (z mod 2 ^ 64)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_059 ())).
Qed.
Lemma land64_eq : forall z, land64 z = (z mod two64)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_060 ())).
Qed.
Lemma land32_eq : forall z, land32 z = (z mod 4294967296)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_061 ())).
Qed.
Lemma land_63 : forall y, Z.land y 63 = (y mod 64)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_062 ())).
Qed.
Lemma land_31 : forall y, Z.land y 31 = (y mod 32)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_063 ())).
Qed.

Lemma zext_fast_eq : forall sx lo n x, (0 <= x < 2 ^ 64)%Z -> zext_fast sx lo n x = zext_lit sx lo n x.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_064 ())).
Qed.

Lemma mkExt_denot : forall E sx lo n e, (n <= 8)%nat ->
  edenot E (mkExt sx lo n e) = ext_val sx lo n (edenot E e).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_065 ())).
Qed.

Lemma ridx_inj : forall r r' : reg, ridx r = ridx r' -> r = r'.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_066 ())).
Qed.

Lemma nth_sr_upd : forall n sr e i,
  nth i (sr_upd sr n e) (ELit 0) = if Nat.eqb i n then e else nth i sr (ELit 0).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_067 ())).
Qed.

Definition regs_ok (E : env) (sr : list expr) (regs : bvmap 5 word) : Prop := ltac2:(Rpl.RP.run_k (rplG ()) 3 (AxSymExec3SoundK_blobs1.kr_b_068 ())).

Lemma regs_ok_upd : forall E sr regs rd v e,
  regs_ok E sr regs -> edenot E e = v ->
  regs_ok E (if bv_eqb rd 0 then sr else sr_upd sr (ridx rd) e)
            (if bv_eqb rd 0 then regs else regupd regs rd v).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_069 ())).
Qed.

Lemma regs_ok_pin : forall E sr regs (r : reg) e,
  regs_ok E sr regs -> getr regs r = edenot E e ->
  regs_ok E (sr_upd sr (ridx r) e) regs.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_070 ())).
Qed.

Lemma ridx_range : forall r : reg, (ridx r < 32)%nat.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_071 ())).
Qed.

Lemma ridx_roundtrip : forall r : reg, Z_to_bv 5 (Z.of_nat (ridx r)) = r.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_072 ())).
Qed.

Definition reg_ev (regs : bvmap 5 word) (rest : nat -> word) : nat -> word := ltac2:(Rpl.RP.run_k (rplG ()) 2 (AxSymExec3SoundK_blobs1.kr_b_073 ())).

Lemma regs_ok_id : forall regs rest ebs, regs_ok (Env (reg_ev regs rest) ebs) sr_id regs.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_074 ())).
Qed.

Fixpoint mem_denot (E : env) (base : word -> option byte) (log : list sentry)
  : word -> option byte :=
  match log with
  | [] => base
  | SE a w v :: rest =>
      wbytes (mem_denot E base rest) (adenot E a) (word_to_le_bytes w (edenot E v))
  end.

Lemma mem_denot_grows : forall E base log, mem_grows base (mem_denot E base log).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_075 ())).
Qed.

Definition estart (E : env) (a : saddr) : Z := ltac2:(Rpl.RP.run_k (rplG ()) 2 (AxSymExec3SoundK_blobs1.kr_b_076 ())).
Definition elenZ (E : env) (n : expr) : Z := ltac2:(Rpl.RP.run_k (rplG ()) 2 (AxSymExec3SoundK_blobs1.kr_b_077 ())).

Definition flat (E : env) (a : saddr) (n : Z) : Prop := ltac2:(Rpl.RP.run_k (rplG ()) 3 (AxSymExec3SoundK_blobs1.kr_b_078 ())).

Lemma flat_u : forall E a n, flat E a n -> bv_unsigned (adenot E a) = estart E a.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_079 ())).
Qed.

Lemma flat_mono : forall E a n m, flat E a n -> (0 <= m <= n)%Z -> flat E a m.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_080 ())).
Qed.

Fixpoint log_flat (E : env) (log : list sentry) : Prop :=
  match log with
  | [] => True
  | SE a w _ :: rest => (w <= 8)%nat /\ flat E a (Z.of_nat w) /\ log_flat E rest
  end.

Definition extz (sx : bool) (n : nat) (u : Z) : Z := ltac2:(Rpl.RP.run_k (rplG ()) 3 (AxSymExec3SoundK_blobs1.kr_b_081 ())).

Definition kentry_ok (segs : list Segment) (E : env) (base : word -> option byte) (K : kentry) : Prop := ltac2:(Rpl.RP.run_k (rplG ()) 4 (AxSymExec3SoundK_blobs1.kr_b_082 ())).

Definition know_ok (segs : list Segment) (E : env) (base : word -> option byte) (kn : list kentry) : Prop := ltac2:(Rpl.RP.run_k (rplG ()) 4 (AxSymExec3SoundK_blobs1.kr_b_083 ())).

Definition sc_denot (segs : list Segment) (base : word -> option byte) (E : env) (s : sidecond) : Prop := ltac2:(Rpl.RP.run_k (rplG ()) 4 (AxSymExec3SoundK_blobs1.kr_b_084 ())).

Definition scs_denot (segs : list Segment) (base : word -> option byte) (E : env) (l : list sidecond) : Prop := ltac2:(Rpl.RP.run_k (rplG ()) 4 (AxSymExec3SoundK_blobs1.kr_b_085 ())).

Lemma w_add_nat : forall (a : word) (n : nat),
  a + nat_to_word n = Z_to_bv 64 (bv_unsigned a + Z.of_nat n).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_086 ())).
Qed.

Lemma w_add_1 : forall (a : word), a + 1 = Z_to_bv 64 (bv_unsigned a + 1).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_087 ())).
Qed.

Lemma u_small : forall z, (0 <= z < 2^64)%Z -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_088 ())).
Qed.

Lemma elenZ_elen : forall E n, (n <= 8)%nat -> elenZ E (elen n) = Z.of_nat n.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_089 ())).
Qed.

Lemma rdn_skipn : forall segs mem n (a : word) bs k,
  rdn segs mem a n = Some bs -> (k <= n)%nat ->
  rdn segs mem (a + nat_to_word k) (n - k)%nat = Some (skipn k bs).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_090 ())).
Qed.

Lemma rdn_slice : forall segs mem n (a : word) bs d k,
  rdn segs mem a n = Some bs -> (d + k <= n)%nat ->
  rdn segs mem (a + nat_to_word d) k = Some (firstn k (skipn d bs)).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_091 ())).
Qed.

Lemma skipn_Z_to_le_bytes : forall w d z, (d <= w)%nat ->
  skipn d (Z_to_le_bytes w z) = Z_to_le_bytes (w - d) (z / 2 ^ (8 * Z.of_nat d)).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_092 ())).
Qed.

Lemma firstn_Z_to_le_bytes : forall m n z, (n <= m)%nat ->
  firstn n (Z_to_le_bytes m z) = Z_to_le_bytes n z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_093 ())).
Qed.

Lemma slice_word_bytes : forall w d n (v : word), (d + n <= w)%nat ->
  bytes_le_to_Z (firstn n (skipn d (word_to_le_bytes w v)))
  = ((bv_unsigned v / 2 ^ (8 * Z.of_nat d)) mod 2 ^ (8 * Z.of_nat n))%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_094 ())).
Qed.

Lemma length_firstn_skipn : forall {A} (l : list A) d n,
  (d + n <= length l)%nat -> length (firstn n (skipn d l)) = n.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_095 ())).
Qed.

Lemma bytes_le_to_Z_bound : forall bs,
  (0 <= bytes_le_to_Z bs < 2 ^ (8 * Z.of_nat (length bs)))%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_096 ())).
Qed.

Lemma Z_to_bv_u_plus0 : forall a : word, Z_to_bv 64 (bv_unsigned a + 0) = a.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_097 ())).
Qed.

Lemma rdn_pointwise : forall segs mem n (a : word) bs,
  length bs = n ->
  (bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
  (forall j, (j < n)%nat ->
     mem (Z_to_bv 64 (bv_unsigned a + Z.of_nat j)) = Some (nth j bs (Z_to_bv 8 0))) ->
  rdn segs mem a n = Some bs.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_098 ())).
Qed.

Lemma rdn_img : forall segs mem n (a : word) zs,
  (bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
  (forall j, (j < n)%nat -> mem (Z_to_bv 64 (bv_unsigned a + Z.of_nat j)) = None) ->
  img_bytes segs (bv_unsigned a) n = Some zs ->
  exists bs, rdn segs mem a n = Some bs /\ map bv_unsigned bs = zs.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_099 ())).
Qed.

Lemma zbytes_map : forall bs, zbytes_le_to_Z (map bv_unsigned bs) = bytes_le_to_Z bs.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_100 ())).
Qed.

Lemma bytes_le_to_Z_repeat0 : forall n, bytes_le_to_Z (repeat (Z_to_bv 8 0) n) = 0%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_101 ())).
Qed.

Lemma extz_0 : forall sx n, extz sx n 0 = 0%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_102 ())).
Qed.

Lemma bv_extract0_lit : forall (m : N) (u : Z),
  bv_extract 0 m (Z_to_bv 64 u) = Z_to_bv m u ->  True.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_103 ())).
Qed.

Lemma extract0_Z_to_bv64 : forall (m : N) (u : Z), (m <= 64)%N ->
  bv_extract 0 m (Z_to_bv 64 u) = Z_to_bv m u.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_104 ())).
Qed.

Lemma zext64_small : forall (m : N) (u : Z), (m <= 64)%N -> (0 <= u < 2 ^ Z.of_N m)%Z ->
  zext 64 (Z_to_bv m u) = Z_to_bv 64 u.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_105 ())).
Qed.

Lemma sext64_small : forall (m : N) (u : Z), (m <= 64)%N -> (0 <= u < 2 ^ Z.of_N m)%Z ->
  sext 64 (Z_to_bv m u) = Z_to_bv 64 (bv_swrap m u).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_106 ())).
Qed.

Lemma load_result_val : forall sz sx bs,
  length bs = msize_bytes sz ->
  load_result sz sx bs = Z_to_bv 64 (extz (eff_sx sz sx) (msize_bytes sz) (bytes_le_to_Z bs)).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_107 ())).
Qed.

Lemma scs_denot_cons : forall segs base E s l,
  scs_denot segs base E (s :: l) <-> sc_denot segs base E s /\ scs_denot segs base E l.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_108 ())).
Qed.

Lemma scs_denot_app : forall segs base E l1 l2,
  scs_denot segs base E (l1 ++ l2) <-> scs_denot segs base E l1 /\ scs_denot segs base E l2.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_109 ())).
Qed.

Lemma log_lookup_acc : forall kn log rb rk n sx hints acc,
  match log_lookup kn log rb rk n sx hints acc with
  | LHit _ scs _ | LMiss scs _ => exists pre, scs = pre ++ acc
  | LStuck => True
  end.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_110 ())).
Qed.

Lemma lit_strip_val : forall E e v c,
  lit_strip e = (v, c) ->
  bv_unsigned (edenot E e) = ((bv_unsigned (edenot E v) + c) mod 2 ^ 64)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_111 ())).
Qed.

Lemma shifted_bound : forall (x : Z) c c' lo hi,
  (0 <= x < 2 ^ 64)%Z ->
  (lo <= (x + c') mod 2 ^ 64 <= hi)%Z ->
  (0 <= lo)%Z -> (lo <= hi)%Z -> (hi < 2 ^ 64)%Z -> (0 <= lo + (c - c'))%Z -> (hi + (c - c') < 2 ^ 64)%Z ->
  (lo + (c - c') <= (x + c) mod 2 ^ 64 <= hi + (c - c'))%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_112 ())).
Qed.

Lemma find_range_sound : forall segs E M kn e lo hi,
  know_ok segs E M kn -> find_range kn e = Some (lo, hi) ->
  (lo <= bv_unsigned (edenot E e))%Z /\ (bv_unsigned (edenot E e) <= hi)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_113 ())).
Qed.

Lemma u_lit64 : forall z, bv_unsigned (Z_to_bv 64 z) = (z mod two64)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_114 ())).
Qed.

Lemma two64_eq : two64 = (2 ^ 64)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_115 ())).
Qed.

Lemma u_add64 : forall x y : word,
  bv_unsigned (alu64 ALU_ADD x y) = ((bv_unsigned x + bv_unsigned y) mod 2 ^ 64)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_116 ())).
Qed.

Lemma u_sub64 : forall x y : word,
  bv_unsigned (alu64 ALU_SUB x y) = ((bv_unsigned x - bv_unsigned y) mod 2 ^ 64)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_117 ())).
Qed.

Lemma u_and64 : forall x y : word,
  bv_unsigned (alu64 ALU_AND x y) = Z.land (bv_unsigned x) (bv_unsigned y).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_118 ())).
Qed.

Lemma u_or64 : forall x y : word,
  bv_unsigned (alu64 ALU_OR x y) = Z.lor (bv_unsigned x) (bv_unsigned y).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_119 ())).
Qed.

Lemma u_xor64 : forall x y : word,
  bv_unsigned (alu64 ALU_XOR x y) = Z.lxor (bv_unsigned x) (bv_unsigned y).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_120 ())).
Qed.

Lemma u_sltu64 : forall x y : word,
  bv_unsigned (alu64 ALU_SLTU x y) = (if (bv_unsigned x <? bv_unsigned y)%Z then 1 else 0)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_121 ())).
Qed.

Lemma u_slt64 : forall x y : word,
  bv_unsigned (alu64 ALU_SLT x y) = (if (bv_signed x <? bv_signed y)%Z then 1 else 0)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_122 ())).
Qed.

Lemma lit_shamt_sound : forall E b s, lit_shamt b = Some s ->
  (bv_unsigned (edenot E b) mod 64 = s)%Z /\ (0 <= s < 64)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_123 ())).
Qed.

Lemma u_srl64 : forall x y : word,
  bv_unsigned (alu64 ALU_SRL x y) = (bv_unsigned x / 2 ^ (bv_unsigned y mod 64))%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_124 ())).
Qed.

Lemma u_sll64 : forall x y : word,
  bv_unsigned (alu64 ALU_SLL x y) = ((bv_unsigned x * 2 ^ (bv_unsigned y mod 64)) mod 2 ^ 64)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_125 ())).
Qed.

Lemma u_sra64_nonneg : forall x y : word, (bv_unsigned x < 2 ^ 63)%Z ->
  bv_unsigned (alu64 ALU_SRA x y) = (bv_unsigned x / 2 ^ (bv_unsigned y mod 64))%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_126 ())).
Qed.

Lemma swrap32_small : forall t, (0 <= t < 2 ^ 31)%Z -> bv_swrap 32 t = t.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_127 ())).
Qed.

Lemma swrap32_shift : forall t k, bv_swrap 32 (t + k * 2 ^ 32) = bv_swrap 32 t.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_128 ())).
Qed.

Lemma u_small_id : forall t, (0 <= t < 2 ^ 64)%Z -> (t mod two64 = t)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_129 ())).
Qed.

Lemma u_addw_small : forall (x y : word) (t : Z),
  (0 <= t < 2 ^ 31)%Z ->
  (exists k, bv_unsigned x + bv_unsigned y = t + k * 2 ^ 32)%Z ->
  bv_unsigned (sext 64 (alu32 ALU_ADD (low32 x) (low32 y)) : word) = t.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_130 ())).
Qed.

Lemma u_subw_small : forall (x y : word) (t : Z),
  (0 <= t < 2 ^ 31)%Z ->
  (bv_unsigned x - bv_unsigned y = t)%Z ->
  bv_unsigned (sext 64 (alu32 ALU_SUB (low32 x) (low32 y)) : word) = t.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_131 ())).
Qed.

Lemma mod32_of_mod64 : forall z, ((z mod 64) mod 32 = z mod 32)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_132 ())).
Qed.

Lemma u_sllw_small : forall (x y : word) s,
  (bv_unsigned y mod 64 = s)%Z ->
  (bv_unsigned x * 2 ^ (s mod 32) < 2 ^ 31)%Z ->
  bv_unsigned (sext 64 (alu32 ALU_SLL (low32 x) (low32 y)) : word) = (bv_unsigned x * 2 ^ (s mod 32))%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_133 ())).
Qed.

Lemma u_srlw_small : forall (x y : word) s,
  (bv_unsigned y mod 64 = s)%Z ->
  (bv_unsigned x < 2 ^ 32)%Z ->
  (bv_unsigned x / 2 ^ (s mod 32) < 2 ^ 31)%Z ->
  bv_unsigned (sext 64 (alu32 ALU_SRL (low32 x) (low32 y)) : word) = (bv_unsigned x / 2 ^ (s mod 32))%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_134 ())).
Qed.

Lemma u_sraw_small : forall (x y : word) s,
  (bv_unsigned y mod 64 = s)%Z ->
  (bv_unsigned x < 2 ^ 31)%Z ->
  bv_unsigned (sext 64 (alu32 ALU_SRA (low32 x) (low32 y)) : word) = (bv_unsigned x / 2 ^ (s mod 32))%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_135 ())).
Qed.

Lemma u_mul64 : forall x y : word,
  bv_unsigned (mul_div M_MUL x y) = ((bv_unsigned x * bv_unsigned y) mod 2 ^ 64)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_136 ())).
Qed.

Lemma u_mulhu64 : forall x y : word,
  bv_unsigned (mul_div M_MULHU x y) = (bv_unsigned x * bv_unsigned y / 2 ^ 64)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_137 ())).
Qed.

Lemma u_divu64 : forall x y : word, (0 < bv_unsigned y)%Z ->
  bv_unsigned (mul_div M_DIVU x y) = (bv_unsigned x / bv_unsigned y)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_138 ())).
Qed.

Lemma u_remu64 : forall x y : word, (0 < bv_unsigned y)%Z ->
  bv_unsigned (mul_div M_REMU x y) = (bv_unsigned x mod bv_unsigned y)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_139 ())).
Qed.

Lemma u_ext_zx : forall lo n (v : word),
  bv_unsigned (ext_val false lo n v) = ((bv_unsigned v / 2 ^ (8 * Z.of_nat lo)) mod 2 ^ (8 * Z.of_nat n))%Z
  /\ (bv_unsigned (ext_val false lo n v) <= 2 ^ (8 * Z.of_nat n) - 1)%Z
  /\ (bv_unsigned (ext_val false lo n v) <= two64 - 1)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_140 ())).
Qed.

Lemma u_ext_zx0_small : forall n (v : word),
  (bv_unsigned v < 2 ^ (8 * Z.of_nat n))%Z -> bv_unsigned (ext_val false 0 n v) = bv_unsigned v.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_141 ())).
Qed.

Lemma u_ext_sx0_small : forall n (v : word),
  (bv_unsigned v < 2 ^ (8 * Z.of_nat n) / 2)%Z -> bv_unsigned (ext_val true 0 n v) = bv_unsigned v.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_142 ())).
Qed.

Lemma u_ext_sx0_high : forall n (v : word),
  (2 ^ (8 * Z.of_nat n) / 2 <= bv_unsigned v < 2 ^ (8 * Z.of_nat n))%Z -> (1 <= n <= 8)%nat ->
  bv_unsigned (ext_val true 0 n v) = (2 ^ 64 - 2 ^ (8 * Z.of_nat n) + bv_unsigned v)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_143 ())).
Qed.

Lemma u_blob_zx : forall bs i n,
  (bv_unsigned (blob_val false bs i n) <= 2 ^ (8 * Z.of_nat n) - 1)%Z
  /\ (bv_unsigned (blob_val false bs i n) <= two64 - 1)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_144 ())).
Qed.

Lemma clampi_sound : forall (v : word) lo hi lo' hi',
  (lo <= bv_unsigned v <= hi)%Z -> clampi (lo, hi) = (lo', hi') -> (lo' <= bv_unsigned v <= hi')%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_145 ())).
Qed.
Lemma mod_wrap_hi : forall t, (2 ^ 64 <= t < 2 ^ 64 + 2 ^ 64)%Z -> (t mod 2 ^ 64 = t - 2 ^ 64)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_146 ())).
Qed.
Lemma mod_wrap_neg : forall t, (- 2 ^ 64 <= t < 0)%Z -> (t mod 2 ^ 64 = t + 2 ^ 64)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_147 ())).
Qed.
Lemma mask_cover_sound : forall h x, (0 <= x <= h)%Z -> (x <= mask_cover h)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_148 ())).
Qed.
Lemma pow_cover : forall h, (0 <= h)%Z -> (h + 1 <= 2 ^ Z.log2_up (h + 1))%Z /\ (0 <= Z.log2_up (h + 1))%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_149 ())).
Qed.
Lemma lor_cover : forall h x y, (0 <= x <= h)%Z -> (0 <= y <= h)%Z -> (Z.lor x y <= mask_cover h)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_150 ())).
Qed.
Lemma lxor_cover : forall h x y, (0 <= x <= h)%Z -> (0 <= y <= h)%Z -> (0 <= Z.lxor x y <= mask_cover h)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_151 ())).
Qed.
Lemma land_le_l : forall a b, (0 <= a)%Z -> (0 <= b)%Z -> (Z.land a b <= a)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_152 ())).
Qed.
Lemma land_le_r : forall a b, (0 <= a)%Z -> (0 <= b)%Z -> (Z.land a b <= b)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_153 ())).
Qed.
Lemma lor_ge_l : forall x y, (0 <= x)%Z -> (0 <= y)%Z -> (x <= Z.lor x y)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_154 ())).
Qed.
Lemma lor_ge_r : forall x y, (0 <= x)%Z -> (0 <= y)%Z -> (y <= Z.lor x y)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_155 ())).
Qed.

Ltac fr_case Hkn H :=
  lazymatch type of H with
  | match find_range ?kn ?e with _ => _ end = _ =>
      destruct (find_range kn e) as [[flo fhi]|] eqn:Hfr;
      [ pose proof (find_range_sound _ _ _ _ _ _ _ Hkn Hfr) as Hb; unfold clampi, two64m1 in H;
        injection H as <- <-; lazymatch goal with |- context [bv_unsigned ?v] => pose proof (u64_range v) end; unfold two64 in *; lia
      | clear Hfr ]
  end.

Ltac er_both IHe1 IHe2 Hkn H :=
  destruct (erange _ _) as [[al ah]|] eqn:He1 in H; [|try discriminate];
  destruct (erange _ _) as [[bl bh]|] eqn:He2 in H; [|try discriminate];
  try (specialize (IHe1 al ah Hkn eq_refl)); try (specialize (IHe2 bl bh Hkn eq_refl)).

Lemma lin_range_sound : forall E rng,
  (forall a lo hi, rng a = Some (lo, hi) -> (lo <= bv_unsigned (edenot E a) <= hi)%Z) ->
  forall c ts lo hi, lin_range rng c ts = Some (lo, hi) -> (lo <= c + tden E ts <= hi)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_156 ())).
Qed.

Lemma testbit_mask : forall j i, (0 <= j)%Z -> (j < 64)%Z -> (0 <= i)%Z ->
  Z.testbit (2 ^ 64 - 2 ^ j) i = ((j <=? i) && (i <? 64))%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_157 ())).
Qed.

Lemma land_align_mask : forall x j, (0 <= j)%Z -> (j < 64)%Z -> (0 <= x < 2 ^ 64)%Z ->
  (x mod 2 ^ j = 0)%Z -> Z.land x (2 ^ 64 - 2 ^ j) = x.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_158 ())).
Qed.

Section ZBits.
Local Open Scope Z_scope.
Lemma testbit_drop_low : forall q r j i, 0 <= j -> 0 <= r < 2 ^ j -> j <= i ->
  Z.testbit (q * 2 ^ j + r) i = Z.testbit (q * 2 ^ j) i.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_159 ())).
Qed.

Lemma land_highmask : forall x j, 0 <= j < 64 -> 0 <= x < 2 ^ 64 ->
  Z.land x (2 ^ 64 - 2 ^ j) = x - x mod 2 ^ j.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_160 ())).
Qed.
End ZBits.

Lemma erange_f_sound : forall segs E M kn fuel e rlo rhi,
  know_ok segs E M kn -> erange_f fuel kn e = Some (rlo, rhi) ->
  (rlo <= bv_unsigned (edenot E e) <= rhi)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_161 ())).
Qed.

Lemma facts_of_ok : forall segs E M kn, know_ok segs E M kn -> know_ok segs E M (facts_of kn).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_162 ())).
Qed.

Lemma erange0_sound : forall segs E M kn e rlo rhi,
  know_ok segs E M kn -> erange0 kn e = Some (rlo, rhi) ->
  (rlo <= bv_unsigned (edenot E e) <= rhi)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_163 ())).
Qed.

Lemma deand_sound : forall E e e' s,
  deand e = (e', s) ->
  (0 <= s)%Z /\ exists rho, (0 <= rho <= s)%Z /\ eqm (bv_unsigned (edenot E e)) (bv_unsigned (edenot E e') - rho)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_164 ())).
Qed.

Lemma ctz_fuel_sound : forall f z, (0 <= ctz_fuel f z)%Z /\ (2 ^ ctz_fuel f z | z)%Z /\ (ctz_fuel f z <= Z.of_nat f)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_165 ())).
Qed.

Lemma ctz64_sound : forall z, (0 <= ctz64 z <= 64)%Z /\ (2 ^ ctz64 z | z)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_166 ())).
Qed.

Lemma ctzp_sound : forall f p, (0 <= ctzp f p <= Z.of_nat f)%Z /\ (2 ^ ctzp f p | Z.pos p)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_167 ())).
Qed.

Lemma ctzq_sound : forall z, (0 <= ctzq z <= 12)%Z /\ (2 ^ ctzq z | z)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_168 ())).
Qed.

Lemma divide_mod_two64 : forall c z, (0 <= c <= 64)%Z -> (2 ^ c | z)%Z -> (2 ^ c | z mod two64)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_169 ())).
Qed.

Lemma pow2_divide_le : forall a b, (0 <= a <= b)%Z -> (2 ^ a | 2 ^ b)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_170 ())).
Qed.

Lemma and_mask_align_sound : forall E a mk,
  (0 <= and_mask_align mk)%Z /\ (2 ^ and_mask_align mk | bv_unsigned (edenot E (EAlu ALU_AND a (ELit mk))))%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_171 ())).
Qed.

Lemma atom_galign_sound : forall E a, (0 <= atom_galign a)%Z /\ (2 ^ atom_galign a | bv_unsigned (edenot E a))%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_172 ())).
Qed.

Lemma terms_galign_sound : forall E ts,
  (0 <= terms_galign ts <= 12)%Z /\ (2 ^ terms_galign ts | tden E ts)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_173 ())).
Qed.

Lemma lin_galign_sound : forall E l,
  (0 <= lin_galign l <= 12)%Z /\ (2 ^ lin_galign l | fst l + tden E (snd l))%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_174 ())).
Qed.

Lemma round_itv_sound : forall g lo hi v,
  (0 <= g)%Z -> (2 ^ g | v)%Z -> (lo <= v <= hi)%Z ->
  (fst (round_itv g lo hi) <= v <= snd (round_itv g lo hi))%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_175 ())).
Qed.

Lemma erange_sound : forall segs E M kn e rlo rhi,
  know_ok segs E M kn -> erange kn e = Some (rlo, rhi) ->
  (rlo <= bv_unsigned (edenot E e) <= rhi)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_176 ())).
Qed.

Lemma base_range_sound : forall segs E M kn e lo hi,
  know_ok segs E M kn -> base_range kn e = Some (lo, hi) ->
  (lo <= bv_unsigned (edenot E e))%Z /\ (bv_unsigned (edenot E e) <= hi)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_177 ())).
Qed.

Lemma zlit64_eq : forall z, zlit64 z = (z mod two64)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_178 ())).
Qed.

Lemma lin_nowrap_sound : forall segs E M kn e,
  know_ok segs E M kn -> lin_nowrap kn e = true ->
  bv_unsigned (edenot E e) = (fst (lin_of e) + tden E (snd (lin_of e)))%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_179 ())).
Qed.

Lemma lins_e_sound : forall E k a ts, tden E (lins_e k a ts) = (k * uE E a + tden E ts)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_180 ())).
Qed.

Lemma lsub_e_sound : forall E ts2 ts1, tden E (lsub_e ts2 ts1) = (tden E ts2 - tden E ts1)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_181 ())).
Qed.

Lemma find_align_sound : forall segs E base kn a m,
  know_ok segs E base kn -> find_align kn a = Some m ->
  (0 < m)%Z /\ (bv_unsigned (edenot E a) mod m = 0)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_182 ())).
Qed.

Lemma divide_mod64 : forall k t, (0 <= k <= 64)%Z -> (2 ^ k | t)%Z -> (2 ^ k | t mod 2 ^ 64)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_183 ())).
Qed.

Lemma ealign0_sound : forall segs E M kn e,
  know_ok segs E M kn ->
  (0 <= ealign0 kn e <= 64)%Z /\ (2 ^ ealign0 kn e | bv_unsigned (edenot E e))%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_184 ())).
Qed.

Lemma find_and_atom_k_some : forall sg ts y mm, find_and_atom_k sg ts = Some (y, mm) ->
  (0 < mm)%Z /\ Z.land (mm + 1) mm = 0%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_185 ())).
Qed.

Lemma find_and_atom_some : forall ts y mm, find_and_atom ts = Some (y, mm) ->
  (0 < mm)%Z /\ Z.land (mm + 1) mm = 0%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_186 ())).
Qed.

Lemma u_and_mask : forall E y mm k, (0 <= k <= 64)%Z -> (mm + 1 = 2 ^ k)%Z ->
  bv_unsigned (edenot E (EAlu ALU_AND y (ELit mm))) = (bv_unsigned (edenot E y) mod 2 ^ k)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_187 ())).
Qed.

Lemma fold_lins_e_sg_sound : forall E sg ts acc,
  tden E (fold_right (fun t a => lins_e (sg * fst t) (snd t) a) acc ts) = (sg * tden E ts + tden E acc)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_188 ())).
Qed.

Lemma fold_lins_e1_sound : forall E ts acc,
  tden E (fold_right (fun t a => lins_e (1 * fst t) (snd t) a) acc ts) = (tden E ts + tden E acc)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_189 ())).
Qed.

Lemma pageup_low_k_sound : forall sg E e m j r,
  (sg = 1 \/ sg = -1)%Z ->
  (0 <= j <= 64)%Z -> m = (2 ^ j)%Z -> pageup_low_k sg e m = Some r ->
  (bv_unsigned (edenot E e) mod m = r)%Z /\ (0 <= r < m)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_190 ())).
Qed.

Lemma pageup_low_sound : forall E e m j r,
  (0 <= j <= 64)%Z -> m = (2 ^ j)%Z -> pageup_low e m = Some r ->
  (bv_unsigned (edenot E e) mod m = r)%Z /\ (0 <= r < m)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_191 ())).
Qed.

Lemma pageup_align_sound : forall E e,
  (0 <= pageup_align e <= 64)%Z /\ (2 ^ pageup_align e | bv_unsigned (edenot E e))%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_192 ())).
Qed.

Lemma ealign_sound : forall segs E M kn e,
  know_ok segs E M kn ->
  (0 <= ealign kn e <= 64)%Z /\ (2 ^ ealign kn e | bv_unsigned (edenot E e))%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_193 ())).
Qed.

Lemma u_srl_lit : forall E e s,
  bv_unsigned (edenot E (EAlu ALU_SRL e (ELit s))) = (bv_unsigned (edenot E e) / 2 ^ ((s mod two64) mod 64))%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_194 ())).
Qed.

Lemma fold_lins_e_sound : forall E q ts acc,
  tden E (fold_right (fun t a => lins_e (q * fst t) (snd t) a) acc ts) = (q * tden E ts + tden E acc)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_195 ())).
Qed.

Lemma u_srl_rem : forall E e s, (0 <= s < 64)%Z ->
  bv_unsigned (edenot E (srl_rem e (2 ^ s))) = (bv_unsigned (edenot E e) mod 2 ^ s)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_196 ())).
Qed.

Lemma srl_expand_sound : forall segs E M kn ts c ts',
  know_ok segs E M kn -> srl_expand kn ts = (c, ts') ->
  tden E ts = (c + tden E ts')%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_197 ())).
Qed.

Definition sfact_ok (E : env) (f : sfact) : Prop := ltac2:(Rpl.RP.run_k (rplG ()) 2 (AxSymExec3SoundK_blobs1.kr_b_198 ())).

Lemma sum_fact_x_sound : forall segs E M allkn ts lo hi,
  know_ok segs E M allkn -> (lo <= tden E ts <= hi)%Z -> Forall (sfact_ok E) (sum_fact_x allkn ts lo hi).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_199 ())).
Qed.

Lemma fact_nowrap_sound : forall segs E M allkn e lo hi,
  know_ok segs E M allkn -> fact_nowrap allkn e hi = true ->
  (lo <= bv_unsigned (edenot E e) <= hi)%Z ->
  bv_unsigned (edenot E e) = (fst (lin_of e) + tden E (snd (lin_of e)))%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_200 ())).
Qed.

Lemma sum_facts_sound : forall segs E M allkn kn,
  know_ok segs E M allkn -> know_ok segs E M kn -> Forall (sfact_ok E) (sum_facts allkn kn).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_201 ())).
Qed.

Lemma sub_fact_sound : forall E q fts ts,
  tden E (sub_fact q fts ts) = (tden E ts - q * tden E fts)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_202 ())).
Qed.

Lemma sum_subst_sound : forall E fs ts lo hi hit ts' lo' hi' hit',
  Forall (sfact_ok E) fs ->
  sum_subst fs ts lo hi hit = (ts', (lo', hi'), hit') ->
  (tden E ts' + lo' <= tden E ts + lo)%Z /\ (tden E ts + hi <= tden E ts' + hi')%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_203 ())).
Qed.

Lemma lin_test_rel_sound : forall segs E M kn c ts test,
  know_ok segs E M kn -> lin_test_rel kn c ts test = true ->
  exists lo hi, test lo hi = true /\ (lo <= c + tden E ts <= hi)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_204 ())).
Qed.

Lemma lin_test_sound : forall segs E M kn c ts test,
  know_ok segs E M kn -> lin_test kn c ts test = true ->
  exists lo hi, test lo hi = true /\ (lo <= c + tden E ts <= hi)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_205 ())).
Qed.

Lemma lin_brange_sound : forall segs E M kn e lo hi,
  know_ok segs E M kn -> lin_brange kn e = Some (lo, hi) -> (lo <= bv_unsigned (edenot E e) <= hi)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_206 ())).
Qed.

Lemma tden_map_scale : forall E sc ts,
  tden E (List.map (fun t => ((sc * fst t)%Z, snd t)) ts) = (sc * tden E ts)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_207 ())).
Qed.
Lemma lin_srange_sound : forall segs E M kn e lo hi,
  know_ok segs E M kn -> lin_srange kn e = Some (lo, hi) -> (lo <= bv_unsigned (edenot E e) <= hi)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_208 ())).
Qed.
Lemma lin_srange_exact : forall segs E M kn e lo hi,
  know_ok segs E M kn -> lin_srange kn e = Some (lo, hi) ->
  bv_unsigned (edenot E e) = (fst (lin_of e) + tden E (snd (lin_of e)))%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_209 ())).
Qed.

Lemma xlo_sound : forall segs E M kn e lo,
  know_ok segs E M kn -> xlo kn e = Some lo -> (lo <= bv_unsigned (edenot E e))%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_210 ())).
Qed.

Lemma xhi_sound : forall segs E M kn e hi,
  know_ok segs E M kn -> xhi kn e = Some hi -> (bv_unsigned (edenot E e) <= hi)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_211 ())).
Qed.

Lemma lin_nowrapR_sound : forall segs E M kn e,
  know_ok segs E M kn -> lin_nowrapR kn e = true ->
  bv_unsigned (edenot E e) = (fst (lin_of e) + tden E (snd (lin_of e)))%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_212 ())).
Qed.

Lemma lin_apart_sound : forall segs E M kn b1 k1 n1 b2 k2 n2,
  know_ok segs E M kn -> lin_apart kn b1 k1 n1 b2 k2 n2 = true ->
  ((estart E (SA b1 k1) + n1 <= estart E (SA b2 k2))%Z
   \/ (estart E (SA b2 k2) + n2 <= estart E (SA b1 k1))%Z).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_213 ())).
Qed.

Fixpoint xt_den (E : env) (ts : xterms) : Z :=
  match ts with [] => 0 | (e, k) :: r => (bv_unsigned (edenot E e) + k + xt_den E r)%Z end.

Lemma xt_lin_sound : forall segs E M kn ts,
  know_ok segs E M kn -> xt_nowrap kn ts = true ->
  (xt_const ts + tden E (xt_lin ts))%Z = xt_den E ts.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_214 ())).
Qed.

Lemma lin_ge0_scaled_sound : forall segs E M kn c ts,
  know_ok segs E M kn -> lin_ge0_scaled kn c ts = true -> (0 <= c + tden E ts)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_215 ())).
Qed.

Lemma lin_align_sound : forall segs E M kn ts,
  know_ok segs E M kn ->
  (0 <= lin_align (ealign kn) ts <= 12)%Z /\ (2 ^ lin_align (ealign kn) ts | tden E ts)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_216 ())).
Qed.

Lemma lin_slack_sound : forall segs E M kn c ts,
  know_ok segs E M kn -> (0 < lin_slack (ealign kn) c ts)%Z /\ (lin_slack (ealign kn) c ts | c + tden E ts)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_217 ())).
Qed.

Lemma slack_nonneg : forall m v lo, (0 < m)%Z -> (m | v)%Z -> (- m < lo)%Z -> (lo <= v)%Z -> (0 <= v)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_218 ())).
Qed.

Lemma slack_test_sound : forall segs E M kn c ts lo hi,
  know_ok segs E M kn -> slack_test (ealign kn) c ts lo hi = true -> (lo <= c + tden E ts)%Z -> (0 <= c + tden E ts)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_219 ())).
Qed.

Lemma slack_test2_sound : forall segs E M kn c1 t1 c ts lo hi,
  know_ok segs E M kn -> slack_test2 (ealign kn) c1 t1 c ts lo hi = true ->
  (c1 + tden E t1 = c + tden E ts)%Z -> (lo <= c + tden E ts)%Z -> (0 <= c + tden E ts)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_220 ())).
Qed.

Lemma lin_ge0_sound : forall segs E M kn pos neg,
  know_ok segs E M kn -> lin_ge0 kn pos neg = true -> (xt_den E neg <= xt_den E pos)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_221 ())).
Qed.

Lemma xinside_sound : forall segs E M kn b1 k1 n1 b2 k2 n2,
  know_ok segs E M kn -> xinside kn b1 k1 n1 b2 k2 n2 = true ->
  (estart E (SA b2 k2) <= estart E (SA b1 k1))%Z
  /\ (estart E (SA b1 k1) + elenZ E n1 <= estart E (SA b2 k2) + elenZ E n2)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_222 ())).
Qed.

Lemma sub_itv_sound : forall segs E M allkn b k n c m,
  know_ok segs E M allkn -> sub_itv allkn b k n c m = true ->
  (estart E c <= estart E (SA b k))%Z /\ (estart E (SA b k) + n <= estart E c + elenZ E m)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_223 ())).
Qed.

Lemma if3_cases : forall (a b c d e : bool),
  (if (if a then b else false) then true else if (if c then d else false) then true else e) = true ->
  (a = true /\ b = true) \/ (c = true /\ d = true) \/ e = true.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_224 ())).
Qed.

Lemma kdisj_apart_sound_gen : forall segs E M allkn kn b1 k1 n1 b2 k2 n2,
  know_ok segs E M allkn -> know_ok segs E M kn -> kdisj_apart allkn kn b1 k1 n1 b2 k2 n2 = true ->
  ((estart E (SA b1 k1) + n1 <= estart E (SA b2 k2))%Z
   \/ (estart E (SA b2 k2) + n2 <= estart E (SA b1 k1))%Z).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_225 ())).
Qed.

Lemma kdisj_apart_sound : forall segs E M kn b1 k1 n1 b2 k2 n2,
  know_ok segs E M kn -> kdisj_apart kn kn b1 k1 n1 b2 k2 n2 = true ->
  ((estart E (SA b1 k1) + n1 <= estart E (SA b2 k2))%Z
   \/ (estart E (SA b2 k2) + n2 <= estart E (SA b1 k1))%Z).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_226 ())).
Qed.

Lemma ranges_apart_sound : forall segs E M kn b1 k1 n1 b2 k2 n2,
  know_ok segs E M kn -> ranges_apart kn b1 k1 n1 b2 k2 n2 = true ->
  ((estart E (SA b1 k1) + n1 <= estart E (SA b2 k2))%Z
   \/ (estart E (SA b2 k2) + n2 <= estart E (SA b1 k1))%Z).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_227 ())).
Qed.

Lemma sub_itv_x_sound : forall segs E M kn b k n c m,
  know_ok segs E M kn -> sub_itv_x kn b k n c m = true ->
  (estart E c <= estart E (SA b k))%Z /\ (estart E (SA b k) + elenZ E n <= estart E c + elenZ E m)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_228 ())).
Qed.

Lemma kdisj_apart_x_sound : forall segs E M allkn kn b1 k1 n1 b2 k2 n2,
  know_ok segs E M allkn -> know_ok segs E M kn -> kdisj_apart_x allkn kn b1 k1 n1 b2 k2 n2 = true ->
  ((estart E (SA b1 k1) + elenZ E n1 <= estart E (SA b2 k2))%Z
   \/ (estart E (SA b2 k2) + elenZ E n2 <= estart E (SA b1 k1))%Z).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_229 ())).
Qed.

Lemma know_lookupA0_acc : forall allkn segs kn rb rk n sx hints acc,
  match know_lookupA0 allkn segs kn rb rk n sx hints acc with
  | LHit _ scs _ | LMiss scs _ => exists pre, scs = pre ++ acc
  | LStuck => True
  end.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_230 ())).
Qed.

Lemma know_lookupA_acc : forall allkn segs kn rb rk n sx hints acc,
  match know_lookupA allkn segs kn rb rk n sx hints acc with
  | LHit _ scs _ | LMiss scs _ => exists pre, scs = pre ++ acc
  | LStuck => True
  end.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_231 ())).
Qed.

Lemma know_lookup_acc : forall segs kn rb rk n sx hints acc,
  match know_lookup segs kn rb rk n sx hints acc with
  | LHit _ scs _ | LMiss scs _ => exists pre, scs = pre ++ acc
  | LStuck => True
  end.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_232 ())).
Qed.

Lemma rel_lit_inside : forall E rb rk rn kb kk kn d,
  rel_lit rb rk rn kb kk kn = RInside d ->
  rb = kb /\ d = (rk - kk)%Z /\ (kk <= rk)%Z /\ (rk + rn <= kk + kn)%Z /\
  estart E (SA rb rk) = (estart E (SA kb kk) + d)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_233 ())).
Qed.

Lemma rel_lit_disjoint : forall E rb rk rn kb kk kn,
  rel_lit rb rk rn kb kk kn = RDisjoint ->
  rb = kb /\ ((estart E (SA rb rk) + rn <= estart E (SA kb kk))%Z
              \/ (estart E (SA kb kk) + kn <= estart E (SA rb rk))%Z).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_234 ())).
Qed.

Lemma rdn_inside_wbytes : forall segs E M (ka : saddr) w (V : word) (ra : saddr) n d,
  flat E ka (Z.of_nat w) -> flat E ra (Z.of_nat n) ->
  estart E ra = (estart E ka + d)%Z -> (0 <= d)%Z -> (d + Z.of_nat n <= Z.of_nat w)%Z ->
  rdn segs (wbytes M (adenot E ka) (word_to_le_bytes w V)) (adenot E ra) n
  = Some (firstn n (skipn (Z.to_nat d) (word_to_le_bytes w V))).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_235 ())).
Qed.

Lemma ext_hit_value : forall sx d n w (V : word),
  (0 <= d)%Z -> (Z.to_nat d + n <= w)%nat -> (n <= 8)%nat ->
  Z_to_bv 64 (extz sx n (bytes_le_to_Z (firstn n (skipn (Z.to_nat d) (word_to_le_bytes w V)))))
  = ext_val sx (Z.to_nat d) n V.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_236 ())).
Qed.

Section Lookups.
Variable segs : list Segment.
Variable scfg : SpuriousCfg.

Lemma rdn_cons1 : forall mem (a : word) n b bs,
  rdn segs mem a 1 = Some [b] -> rdn segs mem (a + 1) n = Some bs ->
  rdn segs mem a (S n) = Some (b :: bs).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_237 ())).
Qed.

Lemma word_byte_at : forall w d (V : word), (Z.to_nat d + 1 <= w)%nat -> (0 <= d)%Z ->
  firstn 1 (skipn (Z.to_nat d) (word_to_le_bytes w V))
  = [Z_to_bv 8 ((bv_unsigned V / 2 ^ (8 * d)) mod 256)%Z].
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_238 ())).
Qed.

Lemma log_byte_lit_sound : forall E base log rb rk b,
  log_flat E log ->
  log_byte_lit log rb rk = Some b ->
  flat E (SA rb rk) 1 ->
  rdn segs (mem_denot E base log) (adenot E (SA rb rk)) 1 = Some [Z_to_bv 8 b] /\ (0 <= b < 256)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_239 ())).
Qed.

Lemma log_bytes_lit_sound : forall E base log rb n rk zs,
  log_flat E log ->
  log_bytes_lit log rb rk n = Some zs ->
  flat E (SA rb rk) (Z.of_nat n) ->
  exists bs, rdn segs (mem_denot E base log) (adenot E (SA rb rk)) n = Some bs /\ map bv_unsigned bs = zs.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_240 ())).
Qed.

Lemma log_lookup_sound : forall E base kn log rb rk n sx hints acc,
  know_ok segs E base kn ->
  log_flat E log -> (1 <= n)%nat -> (n <= 8)%nat ->
  match log_lookup kn log rb rk n sx hints acc with
  | LHit v scs _ =>
      scs_denot segs base E scs -> flat E (SA rb rk) (Z.of_nat n) ->
      exists bs, rdn segs (mem_denot E base log) (adenot E (SA rb rk)) n = Some bs
                 /\ length bs = n
                 /\ Z_to_bv 64 (extz sx n (bytes_le_to_Z bs)) = edenot E v
  | LMiss scs _ =>
      scs_denot segs base E scs -> flat E (SA rb rk) (Z.of_nat n) ->
      rdn segs (mem_denot E base log) (adenot E (SA rb rk)) n
      = rdn segs base (adenot E (SA rb rk)) n
  | LStuck => True
  end.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_241 ())).
Qed.

End Lookups.

Lemma u_lit0 : bv_unsigned (Z_to_bv 64 0) = 0%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_242 ())).
Qed.

Lemma estart_lit0 : forall E rk, estart E (SA (ELit 0) rk) = rk.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_243 ())).
Qed.

Lemma adenot_shift : forall E (ka ra : saddr) nk nr d,
  flat E ka nk -> flat E ra nr -> estart E ra = (estart E ka + d)%Z -> (0 <= d)%Z ->
  adenot E ra = adenot E ka + nat_to_word (Z.to_nat d).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_244 ())).
Qed.

Lemma elenZ_lit : forall E l0, elenZ E (ELit l0) = (l0 mod 2 ^ 64)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_245 ())).
Qed.

Section KLookup.
Variable segs : list Segment.
Variable scfg : SpuriousCfg.

Lemma u8_lit : forall c, bv_unsigned (Z_to_bv 8 c) = (c mod 256)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_246 ())).
Qed.

Lemma map_unsigned_repeat8 : forall c n,
  map bv_unsigned (repeat (Z_to_bv 8 c) n) = repeat (c mod 256)%Z n.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_247 ())).
Qed.

Lemma fill_lit_denot : forall E sx n c,
  edenot E (fill_lit sx n c) = Z_to_bv 64 (extz sx n (bytes_le_to_Z (repeat (Z_to_bv 8 c) n))).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_248 ())).
Qed.

Lemma fill_read : forall E base (ka ra : saddr) n sx c L,
  (forall i, (0 <= i < L)%Z -> base (Z_to_bv 64 (estart E ka + i)) = Some (Z_to_bv 8 c)) ->
  flat E ra (Z.of_nat n) ->
  (estart E ka <= estart E ra)%Z -> (estart E ra + Z.of_nat n <= estart E ka + L)%Z ->
  exists bs, rdn segs base (adenot E ra) n = Some bs /\ length bs = n
             /\ Z_to_bv 64 (extz sx n (bytes_le_to_Z bs)) = edenot E (fill_lit sx n c).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_249 ())).
Qed.

Lemma know_lookupA0_sound : forall E M0 allkn base kn rb rk n sx hints acc,
  know_ok segs E M0 allkn ->
  know_ok segs E base kn -> (1 <= n)%nat -> (n <= 8)%nat ->
  match know_lookupA0 allkn segs kn rb rk n sx hints acc with
  | LHit v scs _ =>
      scs_denot segs base E scs -> flat E (SA rb rk) (Z.of_nat n) ->
      exists bs, rdn segs base (adenot E (SA rb rk)) n = Some bs
                 /\ length bs = n
                 /\ Z_to_bv 64 (extz sx n (bytes_le_to_Z bs)) = edenot E v
  | _ => True
  end.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_250 ())).
Qed.

Lemma rdn_one : forall mem (a : word) b,
  match mem a with Some b0 => Some b0 | None => seg_rom segs a end = Some b ->
  rdn segs mem a 1 = Some [b].
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_251 ())).
Qed.

Lemma Z_to_bv8_mod : forall c, Z_to_bv 8 (c mod 256) = Z_to_bv 8 c.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_252 ())).
Qed.

Lemma know_byte_lit_sound : forall E base kn rb rk b,
  know_ok segs E base kn ->
  know_byte_lit segs kn rb rk = Some b ->
  flat E (SA rb rk) 1 ->
  rdn segs base (adenot E (SA rb rk)) 1 = Some [Z_to_bv 8 b] /\ (0 <= b < 256)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_253 ())).
Qed.

Lemma know_bytes_lit_sound : forall E base kn rb n rk zs,
  know_ok segs E base kn ->
  know_bytes_lit segs kn rb rk n = Some zs ->
  flat E (SA rb rk) (Z.of_nat n) ->
  exists bs, rdn segs base (adenot E (SA rb rk)) n = Some bs /\ map bv_unsigned bs = zs.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_254 ())).
Qed.

Lemma know_lookupA_sound : forall E M0 allkn base kn rb rk n sx hints acc,
  know_ok segs E M0 allkn ->
  know_ok segs E base kn -> (1 <= n)%nat -> (n <= 8)%nat ->
  match know_lookupA allkn segs kn rb rk n sx hints acc with
  | LHit v scs _ =>
      scs_denot segs base E scs -> flat E (SA rb rk) (Z.of_nat n) ->
      exists bs, rdn segs base (adenot E (SA rb rk)) n = Some bs
                 /\ length bs = n
                 /\ Z_to_bv 64 (extz sx n (bytes_le_to_Z bs)) = edenot E v
  | _ => True
  end.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_255 ())).
Qed.

Lemma know_lookup_sound : forall E base kn rb rk n sx hints acc,
  know_ok segs E base kn -> (1 <= n)%nat -> (n <= 8)%nat ->
  match know_lookup segs kn rb rk n sx hints acc with
  | LHit v scs _ =>
      scs_denot segs base E scs -> flat E (SA rb rk) (Z.of_nat n) ->
      exists bs, rdn segs base (adenot E (SA rb rk)) n = Some bs
                 /\ length bs = n
                 /\ Z_to_bv 64 (extz sx n (bytes_le_to_Z bs)) = edenot E v
  | _ => True
  end.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_256 ())).
Qed.

End KLookup.

Lemma Z_to_bv64_u : forall z, Z_to_bv 64 (bv_unsigned (Z_to_bv 64 z)) = Z_to_bv 64 z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_257 ())).
Qed.

Lemma Z_to_bv64_mod : forall z, Z_to_bv 64 (z mod 2 ^ 64) = Z_to_bv 64 z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_258 ())).
Qed.

Lemma to_saddr_denot : forall E e imm,
  adenot E (to_saddr e imm) = v_addi (edenot E e) imm.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_259 ())).
Qed.

Lemma and_highmask_val : forall (v : word) j, (0 <= j)%Z -> (j < 64)%Z ->
  alu64 ALU_AND v (Z_to_bv 64 (- 2 ^ j)) = Z_to_bv 64 (bv_unsigned v - bv_unsigned v mod 2 ^ j).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_260 ())).
Qed.

Lemma and_mask_id : forall (v : word) j,
  (0 <= j)%Z -> (j < 64)%Z -> (bv_unsigned v mod 2 ^ j = 0)%Z ->
  alu64 ALU_AND v (Z_to_bv 64 (- 2 ^ j)) = v.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_261 ())).
Qed.

Lemma and_lowmask_zero : forall (v : word) j,
  (0 <= j)%Z -> (j <= 64)%Z -> (2 ^ j | bv_unsigned v)%Z ->
  alu64 ALU_AND v (Z_to_bv 64 (2 ^ j - 1)) = Z_to_bv 64 0.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_262 ())).
Qed.

Lemma coeffs_divk_sound : forall segs E M kn m ts,
  know_ok segs E M kn -> (0 < m)%Z -> coeffs_divk kn m ts = true -> (tden E ts mod m = 0)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_263 ())).
Qed.

Lemma lin_lowbits_kn_sound : forall segs E M kn e k v, know_ok segs E M kn -> (0 <= k <= 64)%Z ->
  lin_lowbits_kn kn e k = Some v -> (bv_unsigned (edenot E e) mod 2 ^ k = v)%Z /\ (0 <= v < 2 ^ k)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_264 ())).
Qed.

Lemma ldiv_terms_sound : forall E m ts, (0 < m)%Z -> coeffs_div m ts = true ->
  tden E ts = (m * tden E (ldiv_terms m ts))%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_265 ())).
Qed.

Lemma wrap64_eq : forall z, wrap64 z = (z mod two64)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_266 ())).
Qed.

Lemma u_swrap32 : forall t, bv_unsigned (Z_to_bv 64 (bv_swrap 32 t)) = sx32 (t mod 4294967296)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_267 ())).
Qed.

Lemma zfast_eq : forall op x y, (0 <= x < two64)%Z -> (0 <= y < two64)%Z -> zfast op x y = zalu op x y.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_268 ())).
Qed.

Lemma zfastw_eq : forall op x y, (0 <= x < two64)%Z -> (0 <= y < two64)%Z -> zfastw op x y = zaluw op x y.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_269 ())).
Qed.

Lemma zfastm_eq : forall op x y, (0 <= x < two64)%Z -> (0 <= y < two64)%Z -> zfastm op x y = zmd op x y.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_270 ())).
Qed.

Lemma wrap64_range : forall z, (0 <= wrap64 z < two64)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_271 ())).
Qed.
Lemma Z_to_bv_wrap64 : forall z, Z_to_bv 64 (wrap64 z) = Z_to_bv 64 z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_272 ())).
Qed.
Lemma zalu_l_eq : forall op x y, zalu_l op x y = zalu op x y.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_273 ())).
Qed.
Lemma zaluw_l_eq : forall op x y, zaluw_l op x y = zaluw op x y.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_274 ())).
Qed.
Lemma zmd_l_eq : forall op x y, zmd_l op x y = zmd op x y.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_275 ())).
Qed.

Lemma mkAlu_denot : forall E op a b,
  edenot E (mkAlu op a b) = alu64 op (edenot E a) (edenot E b).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_276 ())).
Qed.

Lemma end_hi_sound : forall segs E M kn b k n lo1 hi1 h1 e,
  know_ok segs E M kn -> base_range kn b = Some (lo1, hi1) -> xhi kn n = Some h1 ->
  end_hi kn b k n lo1 hi1 h1 = Some e ->
  (estart E (SA b k) + elenZ E n <= e)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_277 ())).
Qed.

Lemma ranges_apart_x_sound : forall segs E M kn b1 k1 n1 b2 k2 n2,
  know_ok segs E M kn -> ranges_apart_x kn b1 k1 n1 b2 k2 n2 = true ->
  ((estart E (SA b1 k1) + elenZ E n1 <= estart E (SA b2 k2))%Z
   \/ (estart E (SA b2 k2) + elenZ E n2 <= estart E (SA b1 k1))%Z).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_278 ())).
Qed.

Lemma mkAluw_denot : forall E op a b,
  edenot E (mkAluw op a b) = sext 64 (alu32 op (low32 (edenot E a)) (low32 (edenot E b))).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_279 ())).
Qed.

Lemma mkMd_denot : forall E op a b,
  edenot E (mkMd op a b) = mul_div op (edenot E a) (edenot E b).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_280 ())).
Qed.

Lemma mkMdw_denot : forall E op a b,
  edenot E (mkMdw op a b) = sext 64 (mul_div op (low32 (edenot E a)) (low32 (edenot E b))).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_281 ())).
Qed.

Lemma mkSrl_denot : forall segs E M kn a sh (y : word),
  know_ok segs E M kn -> (bv_unsigned y mod 64 = sh)%Z ->
  edenot E (mkSrl kn a sh) = alu64 ALU_SRL (edenot E a) y.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_282 ())).
Qed.

Lemma and_highmask_srl : forall segs E M kn a j, know_ok segs E M kn -> (0 <= j)%Z -> (j < 64)%Z ->
  edenot E (mkMd M_MUL (ELit (2 ^ j)%Z) (mkSrl kn a j))
  = Z_to_bv 64 (bv_unsigned (edenot E a) - bv_unsigned (edenot E a) mod 2 ^ j).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_283 ())).
Qed.

Lemma land_mod_pow2 : forall x y j, (0 <= j)%Z ->
  ((Z.land x y) mod 2 ^ j = Z.land (x mod 2 ^ j) (y mod 2 ^ j))%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_284 ())).
Qed.

Lemma lor_mod_pow2 : forall x y j, (0 <= j)%Z ->
  ((Z.lor x y) mod 2 ^ j = Z.lor (x mod 2 ^ j) (y mod 2 ^ j))%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_285 ())).
Qed.

Lemma lxor_mod_pow2 : forall x y j, (0 <= j)%Z ->
  ((Z.lxor x y) mod 2 ^ j = Z.lxor (x mod 2 ^ j) (y mod 2 ^ j))%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_286 ())).
Qed.

Lemma mod_pow2_mod_pow2 : forall x j k, (0 <= j <= k)%Z -> ((x mod 2 ^ k) mod 2 ^ j = x mod 2 ^ j)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_287 ())).
Qed.

Lemma lowbits_sound : forall segs E M kn e j v,
  know_ok segs E M kn -> (0 <= j <= 64)%Z ->
  lowbits kn e j = Some v -> (bv_unsigned (edenot E e) mod 2 ^ j = v)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_288 ())).
Qed.

Lemma lsplit_div_sound : forall kn m ts dts rts,
  lsplit_div kn m ts = (dts, rts) ->
  coeffs_divk kn m dts = true /\ forall E, tden E ts = (tden E dts + tden E rts)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_289 ())).
Qed.

Lemma split_mod_core : forall (ua ur SA : Z) j,
  (0 <= j <= 64)%Z -> (SA mod 2 ^ j = 0)%Z -> eqm ua (SA + ur) ->
  (ua mod 2 ^ j = ur mod 2 ^ j)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_290 ())).
Qed.

Lemma and_high_split_denot : forall segs E base kn bk j c dts rts (a : expr),
  know_ok segs E base kn -> (0 <= j)%Z -> (j < 64)%Z ->
  edenot E bk = Z_to_bv 64 (- 2 ^ j) ->
  coeffs_divk kn (2 ^ j) dts = true ->
  eqm (uE E a) (c + tden E dts + tden E rts) ->
  edenot E (and_high_split kn bk j c dts rts) = alu64 ALU_AND (edenot E a) (Z_to_bv 64 (- 2 ^ j)).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_291 ())).
Qed.

Lemma and_low_split_denot : forall segs E base kn bk j c dts rts (a : expr),
  know_ok segs E base kn -> (0 <= j)%Z -> (j < 64)%Z ->
  edenot E bk = Z_to_bv 64 (2 ^ j - 1) ->
  coeffs_divk kn (2 ^ j) dts = true ->
  eqm (uE E a) (c + tden E dts + tden E rts) ->
  edenot E (and_low_split kn bk j c rts) = alu64 ALU_AND (edenot E a) (Z_to_bv 64 (2 ^ j - 1)).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_292 ())).
Qed.

Lemma mkAnd0_denot : forall segs E base kn a b,
  know_ok segs E base kn ->
  edenot E (mkAnd0 kn a b) = alu64 ALU_AND (edenot E a) (edenot E b).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_293 ())).
Qed.

Lemma testbit_pow_sub : forall a i n : Z, (0 <= i <= a)%Z -> (0 <= n)%Z ->
  Z.testbit (2 ^ a - 2 ^ i)%Z n = (Z.leb i n && Z.ltb n a)%bool.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_294 ())).
Qed.

Lemma land_mask_narrow : forall x i j : Z, (0 <= i <= j)%Z -> (j <= 64)%Z -> (0 <= x < 2 ^ j)%Z ->
  Z.land x (2 ^ j - 2 ^ i)%Z = Z.land x (2 ^ 64 - 2 ^ i)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_295 ())).
Qed.

Lemma mkAnd_denot : forall segs E base kn a b,
  know_ok segs E base kn ->
  edenot E (mkAnd kn a b) = alu64 ALU_AND (edenot E a) (edenot E b).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_296 ())).
Qed.

Lemma mkAndK_denot : forall segs E base kn a b,
  know_ok segs E base kn ->
  edenot E (mkAndK kn a b) = alu64 ALU_AND (edenot E a) (edenot E b).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_297 ())).
Qed.

Lemma itv_ltu_sound : forall al ah bl bh x y t,
  (al <= x <= ah)%Z -> (bl <= y <= bh)%Z -> itv_ltu al ah bl bh = Some t -> (x <? y)%Z = t.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_298 ())).
Qed.

Lemma itv_lts_sound : forall al ah bl bh (x y : word) t,
  (al <= bv_unsigned x <= ah)%Z -> (bl <= bv_unsigned y <= bh)%Z ->
  itv_lts al ah bl bh = Some t -> (bv_signed x <? bv_signed y)%Z = t.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_299 ())).
Qed.

Lemma range_branch_sound : forall c al ah bl bh (x y : word) t,
  (al <= bv_unsigned x <= ah)%Z -> (bl <= bv_unsigned y <= bh)%Z ->
  range_branch c al ah bl bh = Some t -> branch_taken c x y = t.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_300 ())).
Qed.

Lemma cond_on_eq_sound : forall c (v : word), branch_taken c v v = cond_on_eq c.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_301 ())).
Qed.

Lemma lin_branch_sound : forall segs E M kn c a b t,
  know_ok segs E M kn -> lin_branch kn c a b = Some t ->
  branch_taken c (edenot E a) (edenot E b) = t.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_302 ())).
Qed.

Lemma decide_branch_sound : forall segs E M kn c a b t,
  know_ok segs E M kn -> decide_branch kn c a b = Some t ->
  branch_taken c (edenot E a) (edenot E b) = t.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_303 ())).
Qed.

Lemma land_aligned_small : forall x b k, (0 <= k)%Z -> (0 <= x)%Z -> (2 ^ k | x)%Z -> (0 <= b < 2 ^ k)%Z ->
  Z.land x b = 0%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_304 ())).
Qed.

Lemma or_disjoint_sound : forall segs E M kn a b,
  know_ok segs E M kn -> or_disjoint kn a b = true ->
  Z.lor (bv_unsigned (edenot E a)) (bv_unsigned (edenot E b)) = (bv_unsigned (edenot E a) + bv_unsigned (edenot E b))%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_305 ())).
Qed.

Lemma or_as_and_not_plus : forall x c, (0 <= x)%Z -> (0 <= c)%Z ->
  Z.lor x c = (Z.land x (Z.lnot c) + c)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_306 ())).
Qed.

Lemma or_R1 : forall segs E M kn a0 c, know_ok segs E M kn ->
  edenot E (mkAlu ALU_ADD (mkAndK kn a0 (ELit (Z.lnot (c mod two64)))) (ELit c))
  = alu64 ALU_OR (edenot E a0) (edenot E (ELit c)).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_307 ())).
Qed.

Lemma mkOr_denot : forall segs E M kn a b,
  know_ok segs E M kn -> edenot E (mkOr kn a b) = alu64 ALU_OR (edenot E a) (edenot E b).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_308 ())).
Qed.

Lemma lxor_ones64 : forall x, (0 <= x < 2^64)%Z -> Z.lxor x (2^64 - 1) = (2^64 - 1 - x)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_309 ())).
Qed.

Lemma eval_closed_sound : forall E e v, eval_closed e = Some v -> edenot E e = Z_to_bv 64 v.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_310 ())).
Qed.

Lemma esubst_sound : forall E s r e, edenot E r = edenot E s -> edenot E (esubst s r e) = edenot E e.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_311 ())).
Qed.

Lemma all_eval_to_sound : forall s e v lo cnt, all_eval_to s e v lo cnt = true ->
  forall z, (lo <= z < lo + Z.of_nat cnt)%Z -> eval_closed (esubst s (ELit z) e) = Some v.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_312 ())).
Qed.

Lemma eval_closed_range : forall e v, eval_closed e = Some v -> (0 <= v < two64)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_313 ())).
Qed.

Lemma evalS_eq : forall s z e, evalS s (wrap64 z) e = eval_closed (esubst s (ELit z) e).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_314 ())).
Qed.

Lemma all_eval_toS_eq : forall s e v lo cnt, all_eval_toS s e v lo cnt = all_eval_to s e v lo cnt.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_315 ())).
Qed.

Lemma probeS_eq : forall s e v z,
  probeS s e v z = match eval_closed (esubst s (ELit z) e) with Some w => Z.eqb w v | None => false end.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_316 ())).
Qed.

Lemma conc_try_sound : forall segs E M kn e cands v,
  know_ok segs E M kn -> conc_try kn e cands = Some v -> edenot E e = Z_to_bv 64 v.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_317 ())).
Qed.

Lemma concretize_sound : forall segs E M kn e v,
  know_ok segs E M kn -> concretize kn e = Some v -> edenot E e = Z_to_bv 64 v.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_318 ())).
Qed.

Lemma foldK_denot : forall segs E base kn e,
  know_ok segs E base kn -> edenot E (foldK kn e) = edenot E e.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_319 ())).
Qed.

Lemma mkSlt_denot : forall segs E base kn c op a b,
  know_ok segs E base kn ->
  (forall x y, alu64 op x y = if branch_taken c x y then Z_to_bv 64 1 else Z_to_bv 64 0) ->
  edenot E (mkSlt kn c op a b) = alu64 op (edenot E a) (edenot E b).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_320 ())).
Qed.

Lemma mkAluK0_denot : forall segs E base kn op a b,
  know_ok segs E base kn ->
  edenot E (mkAluK0 kn op a b) = alu64 op (edenot E a) (edenot E b).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_321 ())).
Qed.

Lemma mkAluK_denot : forall segs E base kn op a b,
  know_ok segs E base kn ->
  edenot E (mkAluK kn op a b) = alu64 op (edenot E a) (edenot E b).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_322 ())).
Qed.

Lemma pow2_log_sound : forall m k, pow2_log m = Some k ->
  (0 <= k < 64)%Z /\ ((m mod two64) = 2 ^ k)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_323 ())).
Qed.

Lemma mkMdK_denot : forall segs E base kn op a b,
  know_ok segs E base kn ->
  edenot E (mkMdK kn op a b) = mul_div op (edenot E a) (edenot E b).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_324 ())).
Qed.

Lemma swrap32_neg : forall v, (2 ^ 64 - 2 ^ 31 <= v < 2 ^ 64)%Z ->
  Z_to_bv 64 (bv_swrap 32 v) = Z_to_bv 64 v.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_325 ())).
Qed.

Lemma mkAluwK0_denot : forall segs E base kn op a b,
  know_ok segs E base kn ->
  edenot E (mkAluwK0 kn op a b) = sext 64 (alu32 op (low32 (edenot E a)) (low32 (edenot E b))).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_326 ())).
Qed.

Lemma mkAluwK_denot : forall segs E base kn op a b,
  know_ok segs E base kn ->
  edenot E (mkAluwK kn op a b) = sext 64 (alu32 op (low32 (edenot E a)) (low32 (edenot E b))).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_327 ())).
Qed.

Lemma extK0_denot : forall segs E base kn v,
  know_ok segs E base kn -> edenot E (extK0 kn v) = edenot E v.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_328 ())).
Qed.

Lemma extK_denot : forall segs E base kn v,
  know_ok segs E base kn -> edenot E (extK kn v) = edenot E v.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_329 ())).
Qed.

Lemma flat_sc_sound : forall segs E base kn a n rest,
  know_ok segs E base kn -> (1 <= n)%nat -> (n <= 8)%nat ->
  scs_denot segs base E (flat_sc kn a n ++ rest) ->
  flat E a (Z.of_nat n) /\ scs_denot segs base E rest.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_330 ())).
Qed.

Lemma conc_expr_sound : forall segs E M kn e,
  know_ok segs E M kn -> edenot E (conc_expr kn e) = edenot E e.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_331 ())).
Qed.

Lemma enum_branch_sound : forall segs E M kn c a b t,
  know_ok segs E M kn -> enum_branch kn c a b = Some t ->
  branch_taken c (edenot E a) (edenot E b) = t.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_332 ())).
Qed.

Lemma to_saddrK_denot : forall segs E M kn e imm,
  know_ok segs E M kn -> adenot E (to_saddrK kn e imm) = v_addi (edenot E e) imm.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_333 ())).
Qed.

Section StepSound.
Variable segs : list Segment.
Variable scfg : SpuriousCfg.

Definition st_ok (E : env) (base rom : word -> option byte)
                 (ss : sym_state) (ms : machine_state) : Prop := ltac2:(Rpl.RP.run_k (rplG ()) 5 (AxSymExec3SoundK_blobs1.kr_b_334 ())).

Definition resv_denot (E : env) (r : option saddr) : option word := ltac2:(Rpl.RP.run_k (rplG ()) 2 (AxSymExec3SoundK_blobs1.kr_b_335 ())).

Definition st_okR (E : env) (base rom : word -> option byte)
                  (ss : sym_state) (ms : machine_state) : Prop := ltac2:(Rpl.RP.run_k (rplG ()) 5 (AxSymExec3SoundK_blobs1.kr_b_336 ())).

Lemma st_ok_R : forall E base rom ss ms,
  st_ok E base rom ss ms -> st_okR E base rom (clr ss) ms.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_337 ())).
Qed.

Lemma st_okR_ok : forall E base rom ss ms,
  st_okR E base rom ss ms -> s_resv ss = None -> st_ok E base rom ss ms.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_338 ())).
Qed.

Lemma s_clean_None : forall ss, s_clean ss = true <-> s_resv ss = None.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_339 ())).
Qed.

Lemma s_resv_clr : forall ss, s_resv (clr ss) = None.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_340 ())).
Qed.

Lemma msize_bytes_range : forall sz, (1 <= msize_bytes sz)%nat /\ (msize_bytes sz <= 8)%nat.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_341 ())).
Qed.

Lemma msize_bytes_R : forall sz, SymStepR.msize_bytes sz = msize_bytes sz.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_342 ())).
Qed.

Lemma amo_nbytes_sz : forall wd, amo_nbytes wd = msize_bytes (amo_sz wd).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_343 ())).
Qed.

Lemma amo_msize_sz : forall wd, amo_msize wd = amo_sz wd.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_344 ())).
Qed.

Lemma v_addi_0 : forall x : word, v_addi x 0 = x.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_345 ())).
Qed.

Lemma wrap_swrap : forall n z, bv_wrap n (bv_swrap n z) = bv_wrap n z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_346 ())).
Qed.

Lemma low32_sext64_32 : forall v : bv 32, low32 (sext 64 v) = v.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_347 ())).
Qed.

Lemma sym_read_sound : forall E base ss scr a n sx' v scs scr' nx',
  sym_read segs ss (facts_of (s_know ss)) scr a n sx' = Some (v, scs, scr', nx') ->
  scs_denot segs base E scs ->
  log_flat E (s_log ss) -> know_ok segs E base (s_know ss) ->
  (1 <= n)%nat -> (n <= 8)%nat ->
  flat E a (Z.of_nat n) /\
  exists bs, rdn segs (mem_denot E base (s_log ss)) (adenot E a) n = Some bs
             /\ length bs = n
             /\ Z_to_bv 64 (extz sx' n (bytes_le_to_Z bs)) = edenot E v.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_348 ())).
Qed.

Lemma storeok_sc_sound : forall E base fk a n,
  know_ok segs E base fk -> flat E a (Z.of_nat n) -> (1 <= n)%nat -> (n <= 8)%nat ->
  scs_denot segs base E (storeok_sc fk a n) ->
  RiscvSemantics.store_ok segs base (adenot E a) n = true.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_349 ())).
Qed.

Lemma resv_inval_sound : forall E r a r',
  resv_inval r a = Some r' ->
  resv_inval_w (resv_denot E r) (adenot E a) = resv_denot E r'.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_350 ())).
Qed.

Lemma amo_alignedb_sound : forall E M kn e wd,
  know_ok segs E M kn -> amo_alignedb kn e wd = true ->
  (bv_unsigned (edenot E e) mod amo_bytes wd = 0)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_351 ())).
Qed.

Lemma amo_val_alu32 : forall op o (a b : bv 32),
  amo_aluop op = Some (Some o) -> amo_val op a b = alu32 o a b.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_352 ())).
Qed.

Lemma amo_val_alu64 : forall op o (a b : word),
  amo_aluop op = Some (Some o) -> amo_val op a b = alu64 o a b.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_353 ())).
Qed.

Lemma amo_val_swap : forall op n (a b : bv n),
  amo_aluop op = Some None -> amo_val op a b = b.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_354 ())).
Qed.

Lemma amo_store_bytes_newval : forall E M fk op aop wd bs vold src,
  know_ok segs E M fk ->
  amo_aluop op = Some aop ->
  length bs = msize_bytes (amo_sz wd) ->
  edenot E vold = load_result (amo_sz wd) true bs ->
  amo_store_bytes op wd bs (edenot E src)
  = word_to_le_bytes (msize_bytes (amo_sz wd)) (edenot E (amo_newval fk wd aop vold src)).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_355 ())).
Qed.

Lemma sym_step_sound_load : forall E base rom ss regs sz sx rd rs imm ss' scs scr scr' w,
  fetch_word segs (Z_to_bv 64 (s_pc ss)) = Some w ->
  is_ecall w = false ->
  decode_any w = Some (Load sz sx rd rs imm, 4%Z) ->
  sym_step segs (Load sz sx rd rs imm) ss scr = SOk ss' scs scr' ->
  scs_denot segs base E scs ->
  regs_ok E (s_regs ss) regs -> log_flat E (s_log ss) -> know_ok segs E base (s_know ss) ->
  exists ms', RiscvSemantics.step segs (mkstR regs (Z_to_bv 64 (s_pc ss)) (mem_denot E base (s_log ss)) rom
                                              (resv_denot E (s_resv ss))) = MachineOk ms'
              /\ st_okR E base rom ss' ms'.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_356 ())).
Qed.

Lemma sym_step_sound_store : forall E base rom ss regs sz rs1 rs2 imm ss' scs scr scr' w,
  fetch_word segs (Z_to_bv 64 (s_pc ss)) = Some w ->
  is_ecall w = false ->
  decode_any w = Some (Store sz rs1 rs2 imm, 4%Z) ->
  sym_step segs (Store sz rs1 rs2 imm) ss scr = SOk ss' scs scr' ->
  scs_denot segs base E scs ->
  regs_ok E (s_regs ss) regs -> log_flat E (s_log ss) -> know_ok segs E base (s_know ss) ->
  exists ms', RiscvSemantics.step segs (mkstR regs (Z_to_bv 64 (s_pc ss)) (mem_denot E base (s_log ss)) rom
                                              (resv_denot E (s_resv ss))) = MachineOk ms'
              /\ st_okR E base rom ss' ms'.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_357 ())).
Qed.

Lemma sym_step_sound_lr : forall E base rom ss regs wd aq rl rd rs ss' scs scr scr' w,
  fetch_word segs (Z_to_bv 64 (s_pc ss)) = Some w ->
  is_ecall w = false ->
  decode_any w = Some (Lr wd aq rl rd rs, 4%Z) ->
  sym_step segs (Lr wd aq rl rd rs) ss scr = SOk ss' scs scr' ->
  scs_denot segs base E scs ->
  regs_ok E (s_regs ss) regs -> log_flat E (s_log ss) -> know_ok segs E base (s_know ss) ->
  exists ms', RiscvSemantics.step segs (mkstR regs (Z_to_bv 64 (s_pc ss)) (mem_denot E base (s_log ss)) rom
                                              (resv_denot E (s_resv ss))) = MachineOk ms'
              /\ st_okR E base rom ss' ms'.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_358 ())).
Qed.

Lemma sym_step_sound_sc : forall E base rom ss regs wd aq rl rd rs1 rs2 ss' scs scr scr' w,
  fetch_word segs (Z_to_bv 64 (s_pc ss)) = Some w ->
  is_ecall w = false ->
  decode_any w = Some (Sc wd aq rl rd rs1 rs2, 4%Z) ->
  sym_step segs (Sc wd aq rl rd rs1 rs2) ss scr = SOk ss' scs scr' ->
  scs_denot segs base E scs ->
  regs_ok E (s_regs ss) regs -> log_flat E (s_log ss) -> know_ok segs E base (s_know ss) ->
  exists ms', RiscvSemantics.step segs (mkstR regs (Z_to_bv 64 (s_pc ss)) (mem_denot E base (s_log ss)) rom
                                              (resv_denot E (s_resv ss))) = MachineOk ms'
              /\ st_okR E base rom ss' ms'.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_359 ())).
Qed.

Lemma sym_step_sound_amo : forall E base rom ss regs op wd aq rl rd rs1 rs2 ss' scs scr scr' w,
  fetch_word segs (Z_to_bv 64 (s_pc ss)) = Some w ->
  is_ecall w = false ->
  decode_any w = Some (Amo op wd aq rl rd rs1 rs2, 4%Z) ->
  sym_step segs (Amo op wd aq rl rd rs1 rs2) ss scr = SOk ss' scs scr' ->
  scs_denot segs base E scs ->
  regs_ok E (s_regs ss) regs -> log_flat E (s_log ss) -> know_ok segs E base (s_know ss) ->
  exists ms', RiscvSemantics.step segs (mkstR regs (Z_to_bv 64 (s_pc ss)) (mem_denot E base (s_log ss)) rom
                                              (resv_denot E (s_resv ss))) = MachineOk ms'
              /\ st_okR E base rom ss' ms'.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_360 ())).
Qed.

Ltac alu_case STEP DEN :=
  match goal with
  | Hs : SOk _ _ _ = SOk _ _ _ |- _ =>
      injection Hs as <- <- <-;
      eexists; split; [ STEP |];
      eexists; split; [ f_equal; cbn [s_pc sset]; apply v_addi_lit |];
      cbn [s_regs s_log s_know sset];
      match goal with
      | Hregs : regs_ok _ _ _, Hlf : log_flat _ _, Hkn : know_ok _ _ _ _ |- _ =>
          split; [ apply regs_ok_upd; [exact Hregs|]; DEN | split; [exact Hlf | exact Hkn] ]
      end
  end.

Lemma sym_step_soundR : forall E base rom ss ms i ss' scs scr scr' w,
  fetch_word segs (Z_to_bv 64 (s_pc ss)) = Some w ->
  is_ecall w = false ->
  decode_any w = Some (i, 4%Z) ->
  sym_step segs i ss scr = SOk ss' scs scr' ->
  scs_denot segs base E scs ->
  st_okR E base rom ss ms ->
  exists ms', RiscvSemantics.step segs ms = MachineOk ms'
              /\ st_okR E base rom ss' ms'.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_361 ())).
Qed.

Lemma sym_step_sound : forall E base rom ss ms i ss' scs scr scr' w,
  fetch_word segs (Z_to_bv 64 (s_pc ss)) = Some w ->
  is_ecall w = false ->
  decode_any w = Some (i, 4%Z) ->
  sym_step segs i (clr ss) scr = SOk ss' scs scr' ->
  scs_denot segs base E scs ->
  st_ok E base rom ss ms ->
  exists ms', RiscvSemantics.step segs ms = MachineOk ms'
              /\ st_okR E base rom ss' ms'.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_362 ())).
Qed.

End StepSound.

Lemma sidecond_eqb_eq : forall x y, sidecond_eqb x y = true -> x = y.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_363 ())).
Qed.

Lemma sc_mem_In : forall x l, sc_mem x l = true -> In x l.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_364 ())).
Qed.

Lemma sc_add_denot : forall segs base E news acc,
  scs_denot segs base E (sc_add news acc) ->
  scs_denot segs base E news /\ scs_denot segs base E acc.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_365 ())).
Qed.

Section ExecSound.
Variable segs : list Segment.
Variable scfg : SpuriousCfg.

Local Ltac fetch_cases Hstop :=
  lazymatch goal with
  | |- context [fetch_word segs (Z_to_bv 64 (s_pc ?ss))] =>
      destruct (fetch_word segs (Z_to_bv 64 (s_pc ss))) as [w|] eqn:Hf; [|exact Hstop];
      destruct (is_ecall w) eqn:He; [exact Hstop|];
      destruct (decode_any w) as [[i sz]|] eqn:Hd; [|exact Hstop];
      destruct (Z.eqb sz 4) eqn:Hsz; cbn [negb]; [|exact Hstop];
      apply Z.eqb_eq in Hsz; subst sz
  end.

Lemma sym_exec_go_sound : forall fuel first stops scr ss acc ck E base rom,
  sym_exec_go segs fuel first stops scr ss acc ck = ck \/
  (let '(r, accr, _) := sym_exec_go segs fuel first stops scr ss acc ck in
   s_resv r = None /\
   (scs_denot segs base E accr -> scs_denot segs base E acc) /\
   (forall ms, scs_denot segs base E accr -> st_okR segs E base rom ss ms ->
      exists mr, msteps segs ms mr /\ st_okR segs E base rom r mr)).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs1.kr_b_366 ())).
Qed.

Lemma sym_exec_acc : forall fuel first stops scr ss acc E base,
  match sym_exec segs fuel first stops scr ss acc with
  | (ss', scs, scr') => scs_denot segs base E scs -> scs_denot segs base E acc
  end.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs2.kr_b_367 ())).
Qed.

Theorem sym_exec_soundR : forall fuel first stops scr ss acc ss' scs scr' E base rom ms,
  sym_exec segs fuel first stops scr ss acc = (ss', scs, scr') ->
  scs_denot segs base E scs ->
  st_ok segs E base rom ss ms ->
  s_resv ss' = None /\ exists ms', msteps segs ms ms' /\ st_okR segs E base rom ss' ms'.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs2.kr_b_368 ())).
Qed.

Theorem sym_exec_sound : forall fuel first stops scr ss acc ss' scs scr' E base rom ms,
  sym_exec segs fuel first stops scr ss acc = (ss', scs, scr') ->
  scs_denot segs base E scs ->
  st_ok segs E base rom ss ms ->
  exists ms', msteps segs ms ms' /\ st_ok segs E base rom ss' ms'.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs2.kr_b_369 ())).
Qed.

Theorem sym_exec_ex : forall fuel first stops scr ss acc ss' scs scr' E base rom ms,
  sym_exec segs fuel first stops scr ss acc = (ss', scs, scr') ->
  scs_denot segs base E scs ->
  st_ok segs E base rom ss ms ->
  exists R, regs_ok E (s_regs ss') R
         /\ log_flat E (s_log ss')
         /\ msteps segs ms (mkst R (Z_to_bv 64 (s_pc ss')) (mem_denot E base (s_log ss')) rom).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs2.kr_b_370 ())).
Qed.

Theorem sym_exec_resv : forall fuel first stops scr ss acc,
  s_resv (fst (fst (sym_exec segs fuel first stops scr ss acc))) = None.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs2.kr_b_371 ())).
Qed.

Lemma sym_execS_go_sound : forall fuel first stops ss ck E base rom,
  sym_execS_go segs fuel first stops ss ck = ck \/
  (let r := sym_execS_go segs fuel first stops ss ck in
   s_resv r = None /\
   (forall ms, st_okR segs E base rom ss ms -> exists mr, msteps segs ms mr /\ st_okR segs E base rom r mr)).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs2.kr_b_372 ())).
Qed.

Theorem sym_execS_soundR : forall fuel first stops ss E base rom ms,
  st_ok segs E base rom ss ms ->
  s_resv (sym_execS segs fuel first stops ss) = None /\
  exists ms', msteps segs ms ms' /\ st_okR segs E base rom (sym_execS segs fuel first stops ss) ms'.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs2.kr_b_373 ())).
Qed.

Theorem sym_execS_sound : forall fuel first stops ss E base rom ms,
  st_ok segs E base rom ss ms ->
  exists ms', msteps segs ms ms' /\ st_ok segs E base rom (sym_execS segs fuel first stops ss) ms'.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs2.kr_b_374 ())).
Qed.

Theorem sym_execS_ex : forall fuel first stops ss E base rom ms,
  st_ok segs E base rom ss ms ->
  let ss' := sym_execS segs fuel first stops ss in
  exists R, regs_ok E (s_regs ss') R
         /\ log_flat E (s_log ss')
         /\ know_ok segs E base (s_know ss')
         /\ msteps segs ms (mkst R (Z_to_bv 64 (s_pc ss')) (mem_denot E base (s_log ss')) rom).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs2.kr_b_375 ())).
Qed.

Theorem sym_execS_resv : forall fuel first stops ss,
  s_resv (sym_execS segs fuel first stops ss) = None.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs2.kr_b_376 ())).
Qed.

Lemma sym_execT_go_sound : forall t fuel first stops ss ck E base rom,
  itab_sound segs t ->
  sym_execT_go segs t fuel first stops ss ck = ck \/
  (let r := sym_execT_go segs t fuel first stops ss ck in
   s_resv r = None /\
   (forall ms, st_okR segs E base rom ss ms -> exists mr, msteps segs ms mr /\ st_okR segs E base rom r mr)).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs2.kr_b_377 ())).
Qed.

Theorem sym_execT_soundR : forall t fuel first stops ss E base rom ms,
  itab_sound segs t ->
  st_ok segs E base rom ss ms ->
  s_resv (sym_execT segs t fuel first stops ss) = None /\
  exists ms', msteps segs ms ms' /\ st_okR segs E base rom (sym_execT segs t fuel first stops ss) ms'.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs2.kr_b_378 ())).
Qed.

Theorem sym_execT_sound : forall t fuel first stops ss E base rom ms,
  itab_sound segs t ->
  st_ok segs E base rom ss ms ->
  exists ms', msteps segs ms ms' /\ st_ok segs E base rom (sym_execT segs t fuel first stops ss) ms'.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs2.kr_b_379 ())).
Qed.

Theorem sym_execT_ex : forall t fuel first stops ss E base rom ms,
  itab_sound segs t ->
  st_ok segs E base rom ss ms ->
  let ss' := sym_execT segs t fuel first stops ss in
  exists R, regs_ok E (s_regs ss') R
         /\ log_flat E (s_log ss')
         /\ know_ok segs E base (s_know ss')
         /\ msteps segs ms (mkst R (Z_to_bv 64 (s_pc ss')) (mem_denot E base (s_log ss')) rom).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs2.kr_b_380 ())).
Qed.

Theorem sym_execT_resv : forall t fuel first stops ss,
  itab_sound segs t ->
  s_resv (sym_execT segs t fuel first stops ss) = None.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs2.kr_b_381 ())).
Qed.

End ExecSound.

Section XSound.
Variable segs : list Segment.
Variable scfg : SpuriousCfg.

Definition eagree (b : nat) (E E' : env) : Prop := ltac2:(Rpl.RP.run_k (rplG ()) 3 (AxSymExec3SoundK_blobs2.kr_b_382 ())).

Definition eupd (E : env) (i : nat) (v : word) : env := ltac2:(Rpl.RP.run_k (rplG ()) 3 (AxSymExec3SoundK_blobs2.kr_b_383 ())).

Lemma eagree_refl : forall b E, eagree b E E.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs2.kr_b_384 ())).
Qed.

Lemma eagree_sym : forall b E E', eagree b E E' -> eagree b E' E.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs2.kr_b_385 ())).
Qed.

Lemma eagree_trans : forall b E1 E2 E3, eagree b E1 E2 -> eagree b E2 E3 -> eagree b E1 E3.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs2.kr_b_386 ())).
Qed.

Lemma eagree_le : forall b b' E E', eagree b' E E' -> (b <= b')%nat -> eagree b E E'.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs2.kr_b_387 ())).
Qed.

Lemma eagree_upd : forall E i v, eagree i E (eupd E i v).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs2.kr_b_388 ())).
Qed.

Lemma eupd_at : forall E i v, ev (eupd E i v) i = v.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs2.kr_b_389 ())).
Qed.

Lemma edenot_evars_lt : forall b E E' e,
  eagree b E E' -> evars_lt b e = true -> edenot E e = edenot E' e.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs2.kr_b_390 ())).
Qed.

Definition st_okX (E : env) (base rom : word -> option byte) (ss : sym_state) (ms : machine_state) : Prop := ltac2:(Rpl.RP.run_k (rplG ()) 5 (AxSymExec3SoundK_blobs2.kr_b_391 ())).

Lemma st_okX_R : forall E base rom ss ms, st_okX E base rom ss ms -> st_okR segs E base rom ss ms.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs2.kr_b_392 ())).
Qed.

Lemma st_okX_agree : forall E E' base rom ss ms,
  st_okX E base rom ss ms -> eagree (s_next ss) E E' -> st_okX E' base rom ss ms.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs2.kr_b_393 ())).
Qed.

Lemma st_okX_clr : forall E base rom ss ms,
  (forall E', eagree (s_next ss) E E' -> st_ok segs E' base rom ss ms) -> st_okX E base rom (clr ss) ms.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs2.kr_b_394 ())).
Qed.

Lemma st_okR_parts : forall E base rom ss ms,
  st_okR segs E base rom ss ms ->
  regs_ok E (s_regs ss) (ms_regs ms) /\ ms_mem ms = mem_denot E base (s_log ss)
  /\ log_flat E (s_log ss) /\ know_ok segs E base (s_know ss)
  /\ ms = mkstR (ms_regs ms) (Z_to_bv 64 (s_pc ss)) (mem_denot E base (s_log ss)) rom (resv_denot E (s_resv ss)).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs2.kr_b_395 ())).
Qed.

Definition rd1 (mem : word -> option byte) (x : word) : option byte := ltac2:(Rpl.RP.run_k (rplG ()) 2 (AxSymExec3SoundK_blobs2.kr_b_396 ())).

Lemma rdn_defined : forall mem n (a : word),
  (bv_unsigned a + Z.of_nat n <= 2 ^ 64)%Z ->
  (forall j, (j < n)%nat -> rd1 mem (Z_to_bv 64 (bv_unsigned a + Z.of_nat j)) <> None) ->
  exists bs, rdn segs mem a n = Some bs /\ length bs = n.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs2.kr_b_397 ())).
Qed.

Lemma rdn_rd1 : forall mem n (a : word) bs j,
  rdn segs mem a n = Some bs -> (j < n)%nat ->
  rd1 mem (a + nat_to_word j) <> None.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs2.kr_b_398 ())).
Qed.

Lemma zf_covers_sound : forall E M0 allkn rb rk n kb kk len,
  know_ok segs E M0 allkn -> (n <= 8)%nat ->
  zf_covers allkn rb rk n kb kk len = true ->
  (estart E (SA kb kk) <= estart E (SA rb rk))%Z
  /\ (estart E (SA rb rk) + Z.of_nat n <= estart E (SA kb kk) + elenZ E len)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs2.kr_b_399 ())).
Qed.

Lemma kentry_overlay_sound : forall E M0 allkn base rb rk n K,
  know_ok segs E M0 allkn -> kentry_ok segs E base K -> (1 <= n)%nat -> (n <= 8)%nat ->
  kentry_overlay allkn rb rk n K = true ->
  flat E (SA rb rk) (Z.of_nat n)
  /\ forall j, (j < n)%nat -> base (Z_to_bv 64 (estart E (SA rb rk) + Z.of_nat j)) <> None.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs2.kr_b_400 ())).
Qed.

Lemma kentry_readable_sound : forall E M0 allkn base rb rk n K,
  know_ok segs E M0 allkn -> kentry_ok segs E base K -> (1 <= n)%nat -> (n <= 8)%nat ->
  kentry_readable allkn rb rk n K = true ->
  flat E (SA rb rk) (Z.of_nat n)
  /\ forall j, (j < n)%nat -> rd1 base (Z_to_bv 64 (estart E (SA rb rk) + Z.of_nat j)) <> None.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs2.kr_b_401 ())).
Qed.

Lemma know_byte_cov_sound : forall img E base kn rb rk,
  know_ok segs E base kn -> know_byte_cov segs img kn rb rk = true ->
  flat E (SA rb rk) 1
  /\ (if img then rd1 base (Z_to_bv 64 (estart E (SA rb rk))) <> None
      else base (Z_to_bv 64 (estart E (SA rb rk))) <> None).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs2.kr_b_402 ())).
Qed.

Lemma know_bytes_cov_sound : forall img E base kn rb n rk,
  know_ok segs E base kn -> know_bytes_cov segs img kn rb rk n = true -> (1 <= n)%nat ->
  flat E (SA rb rk) (Z.of_nat n)
  /\ forall j, (j < n)%nat ->
       if img then rd1 base (Z_to_bv 64 (estart E (SA rb rk) + Z.of_nat j)) <> None
       else base (Z_to_bv 64 (estart E (SA rb rk) + Z.of_nat j)) <> None.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs2.kr_b_403 ())).
Qed.

Lemma kn_readable_sound : forall E M0 allkn base kn rb rk n,
  know_ok segs E M0 allkn -> know_ok segs E base kn -> (1 <= n)%nat -> (n <= 8)%nat ->
  kn_readable segs allkn kn rb rk n = true ->
  flat E (SA rb rk) (Z.of_nat n) /\ exists bs, rdn segs base (adenot E (SA rb rk)) n = Some bs /\ length bs = n.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs2.kr_b_404 ())).
Qed.

Lemma kn_overlay_sound : forall E M0 allkn base kn rb rk n,
  know_ok segs E M0 allkn -> know_ok segs E base kn -> (1 <= n)%nat -> (n <= 8)%nat ->
  kn_overlay segs allkn kn rb rk n = true ->
  flat E (SA rb rk) (Z.of_nat n) /\ RiscvSemantics.store_ok segs base (adenot E (SA rb rk)) n = true.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs2.kr_b_405 ())).
Qed.

Lemma find_readbase_In : forall i scs a n sx,
  find_readbase i scs = Some (a, n, sx) -> In (SCReadBase a n sx (EVar i)) scs.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs2.kr_b_406 ())).
Qed.

Lemma x_filter_nil : forall ss ss' scs sc,
  x_filter segs ss ss' scs = [] -> In sc scs ->
  x_dischargeable segs ss ss' (find_readbase (s_next ss) scs) sc = true.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs2.kr_b_407 ())).
Qed.

Lemma x_discharge_sound : forall E0 E base ss ss' rb sc,
  know_ok segs E base (s_know ss) ->
  eagree (s_next ss) E0 E ->
  x_dischargeable segs ss ss' rb sc = true ->
  (forall a n sx, rb = Some (a, n, sx) ->
      exists bs, rdn segs base (adenot E0 a) n = Some bs
                 /\ ev E (s_next ss) = Z_to_bv 64 (extz sx n (bytes_le_to_Z bs))) ->
  sc_denot segs base E sc.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs2.kr_b_408 ())).
Qed.

Lemma cap_rd_sound : forall K i E1 base rom ss' ms',
  (forall E'', eagree (s_next ss') E1 E'' -> st_okR segs E'' base rom ss' ms') ->
  exists E', eagree (s_next ss') E1 E'
    /\ (s_next ss' <= s_next (cap_rd K i ss'))%nat
    /\ st_okX E' base rom (cap_rd K i ss') ms'.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs2.kr_b_409 ())).
Qed.

Lemma sym_stepX_sound : forall K E base rom ss ms i ssx scr' w,
  fetch_word segs (Z_to_bv 64 (s_pc ss)) = Some w ->
  is_ecall w = false ->
  decode_any w = Some (i, 4%Z) ->
  sym_stepX segs K i ss scr_nil = SOk ssx [] scr' ->
  st_okX E base rom ss ms ->
  exists E' ms', eagree (s_next ss) E E'
    /\ (s_next ss <= s_next ssx)%nat
    /\ RiscvSemantics.step segs ms = MachineOk ms'
    /\ st_okX E' base rom ssx ms'.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs2.kr_b_410 ())).
Qed.

Lemma sym_execTX_go_sound : forall t K fuel first stops ss ck base rom,
  itab_sound segs t ->
  sym_execTX_go segs t K fuel first stops ss ck = ck \/
  (let r := sym_execTX_go segs t K fuel first stops ss ck in
   s_resv r = None /\ (s_next ss <= s_next r)%nat /\
   (forall E ms, st_okX E base rom ss ms ->
      exists E' mr, eagree (s_next ss) E E' /\ msteps segs ms mr /\ st_okX E' base rom r mr)).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs2.kr_b_411 ())).
Qed.

Theorem sym_execTX_sound : forall t K fuel first stops ss E base rom ms,
  itab_sound segs t ->
  (forall E', eagree (s_next ss) E E' -> st_ok segs E' base rom ss ms) ->
  let ss' := sym_execTX segs t K fuel first stops ss in
  exists E' ms', eagree (s_next ss) E E'
    /\ (s_next ss <= s_next ss')%nat
    /\ msteps segs ms ms'
    /\ (forall E'', eagree (s_next ss') E' E'' -> st_ok segs E'' base rom ss' ms').
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs2.kr_b_412 ())).
Qed.

Theorem sym_execTX_ex : forall t K fuel first stops ss E base rom ms,
  itab_sound segs t ->
  (forall E', eagree (s_next ss) E E' -> st_ok segs E' base rom ss ms) ->
  let ss' := sym_execTX segs t K fuel first stops ss in
  exists E' R, eagree (s_next ss) E E'
    /\ (s_next ss <= s_next ss')%nat
    /\ regs_ok E' (s_regs ss') R
    /\ log_flat E' (s_log ss')
    /\ know_ok segs E' base (s_know ss')
    /\ msteps segs ms (mkst R (Z_to_bv 64 (s_pc ss')) (mem_denot E' base (s_log ss')) rom)
    /\ (forall E'', eagree (s_next ss') E' E'' -> st_ok segs E'' base rom ss' (mkst R (Z_to_bv 64 (s_pc ss')) (mem_denot E' base (s_log ss')) rom)).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs2.kr_b_413 ())).
Qed.

Theorem sym_execTX_resv : forall t K fuel first stops ss,
  itab_sound segs t -> s_resv (sym_execTX segs t K fuel first stops ss) = None.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs2.kr_b_414 ())).
Qed.

Lemma sym_execSX_go_sound : forall K fuel first stops ss ck base rom,
  sym_execSX_go segs K fuel first stops ss ck = ck \/
  (let r := sym_execSX_go segs K fuel first stops ss ck in
   s_resv r = None /\ (s_next ss <= s_next r)%nat /\
   (forall E ms, st_okX E base rom ss ms ->
      exists E' mr, eagree (s_next ss) E E' /\ msteps segs ms mr /\ st_okX E' base rom r mr)).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs2.kr_b_415 ())).
Qed.

Theorem sym_execSX_sound : forall K fuel first stops ss E base rom ms,
  (forall E', eagree (s_next ss) E E' -> st_ok segs E' base rom ss ms) ->
  let ss' := sym_execSX segs K fuel first stops ss in
  exists E' ms', eagree (s_next ss) E E'
    /\ (s_next ss <= s_next ss')%nat
    /\ msteps segs ms ms'
    /\ (forall E'', eagree (s_next ss') E' E'' -> st_ok segs E'' base rom ss' ms').
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs2.kr_b_416 ())).
Qed.

Theorem sym_execSX_resv : forall K fuel first stops ss,
  s_resv (sym_execSX segs K fuel first stops ss) = None.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs2.kr_b_417 ())).
Qed.

End XSound.

Lemma wbytes_out : forall bs m (a x : word),
  (bv_unsigned a + Z.of_nat (length bs) <= 2 ^ 64)%Z ->
  (bv_unsigned x < bv_unsigned a \/ bv_unsigned a + Z.of_nat (length bs) <= bv_unsigned x)%Z ->
  wbytes m a bs x = m x.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs2.kr_b_418 ())).
Qed.

Section CarrySound.
Variable segs : list Segment.
Variable scfg : SpuriousCfg.

Lemma kentry_ok_frame : forall E M (wa : saddr) w (V : word) K (ka : saddr) (kl : expr),
  flat E wa (Z.of_nat w) ->
  kentry_ok segs E M K ->
  match K with
  | KWord a w' _ => ka = a /\ kl = elen w' /\ (w' <= 8)%nat
  | KZero a n => ka = a /\ kl = n
  | KBlob a n _ => ka = a /\ kl = n
  | KImg lo hi => ka = SA (ELit 0) lo /\ kl = ELit (hi - lo) /\ (hi - lo < 2 ^ 64)%Z
  | KAlign _ _ => True
  | KRange _ _ _ => True
  | KWr _ _ => True
  | KDisj _ _ _ _ => True
  | KFill a n _ => ka = a /\ kl = n
  | KUnk a n => ka = a /\ kl = n
  end ->
  ((estart E wa + Z.of_nat w <= estart E ka)%Z \/ (estart E ka + elenZ E kl <= estart E wa)%Z) ->
  kentry_ok segs E (wbytes M (adenot E wa) (word_to_le_bytes w V)) K.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs2.kr_b_419 ())).
Qed.

Lemma Forall_app_intro : forall {A} (P : A -> Prop) l1 l2,
  Forall P l1 -> Forall P l2 -> Forall P (l1 ++ l2).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs2.kr_b_420 ())).
Qed.

Lemma kzero_piece : forall E M (wb : expr) (wk : Z) w (V : word) (kk l0 i0 len : Z),
  flat E (SA wb wk) (Z.of_nat w) ->
  kentry_ok segs E M (KZero (SA wb kk) (ELit l0)) ->
  (0 <= i0)%Z -> (0 < len)%Z -> (i0 + len <= l0 mod 2 ^ 64)%Z ->
  ((kk + i0 + len <= wk)%Z \/ (wk + Z.of_nat w <= kk + i0)%Z) ->
  kentry_ok segs E (wbytes M (adenot E (SA wb wk)) (word_to_le_bytes w V))
            (KZero (SA wb (kk + i0)) (ELit len)).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs2.kr_b_421 ())).
Qed.

Lemma kimg_piece : forall E M (wa : saddr) w (V : word) (lo hi lo' hi' : Z),
  flat E wa (Z.of_nat w) ->
  kentry_ok segs E M (KImg lo hi) ->
  (lo <= lo')%Z -> (hi' <= hi)%Z ->
  ((hi' <= estart E wa)%Z \/ (estart E wa + Z.of_nat w <= lo')%Z) ->
  kentry_ok segs E (wbytes M (adenot E wa) (word_to_le_bytes w V)) (KImg lo' hi').
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs2.kr_b_422 ())).
Qed.

Lemma Forall_one : forall {A} (P : A -> Prop) x, P x -> Forall P [x].
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs2.kr_b_423 ())).
Qed.

Definition zf_kind (mk : saddr -> expr -> kentry) (byteof : option byte -> Prop) : Prop := ltac2:(Rpl.RP.run_k (rplG ()) 2 (AxSymExec3SoundK_blobs2.kr_b_424 ())).

Lemma zf_kind_zero : zf_kind KZero (fun x => x = Some (Z_to_bv 8 0)).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs2.kr_b_425 ())).
Qed.

Lemma zf_kind_fill : forall c, zf_kind (fun a n => KFill a n c) (fun x => x = Some (Z_to_bv 8 c)).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs2.kr_b_426 ())).
Qed.

Lemma zf_kind_unk : zf_kind KUnk (fun x => x <> None).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs2.kr_b_427 ())).
Qed.

Lemma kcut_sound : forall mk byteof E M0 M M' allkn wb wk wn kb kk len,
  zf_kind mk byteof ->
  know_ok segs E M0 allkn ->
  kentry_ok segs E M (mk (SA kb kk) len) ->
  (forall x : word,
     (bv_unsigned x < estart E (SA wb wk) \/ estart E (SA wb wk) + elenZ E wn <= bv_unsigned x)%Z ->
     M' x = M x) ->
  Forall (kentry_ok segs E M') (kcut mk allkn wb wk wn kb kk len).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs2.kr_b_428 ())).
Qed.

Lemma kzero_cut_sound : forall E M0 M M' allkn wb wk wn kb kk len,
  know_ok segs E M0 allkn ->
  kentry_ok segs E M (KZero (SA kb kk) len) ->
  (forall x : word,
     (bv_unsigned x < estart E (SA wb wk) \/ estart E (SA wb wk) + elenZ E wn <= bv_unsigned x)%Z ->
     M' x = M x) ->
  Forall (kentry_ok segs E M') (kzero_cut allkn wb wk wn kb kk len).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs2.kr_b_429 ())).
Qed.

Lemma kfill_cut_sound : forall c E M0 M M' allkn wb wk wn kb kk len,
  know_ok segs E M0 allkn ->
  kentry_ok segs E M (KFill (SA kb kk) len c) ->
  (forall x : word,
     (bv_unsigned x < estart E (SA wb wk) \/ estart E (SA wb wk) + elenZ E wn <= bv_unsigned x)%Z ->
     M' x = M x) ->
  Forall (kentry_ok segs E M') (kfill_cut c allkn wb wk wn kb kk len).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs2.kr_b_430 ())).
Qed.

Lemma kunk_cut_sound : forall E M0 M M' allkn wb wk wn kb kk len,
  know_ok segs E M0 allkn ->
  kentry_ok segs E M (KUnk (SA kb kk) len) ->
  (forall x : word,
     (bv_unsigned x < estart E (SA wb wk) \/ estart E (SA wb wk) + elenZ E wn <= bv_unsigned x)%Z ->
     M' x = M x) ->
  Forall (kentry_ok segs E M') (kunk_cut allkn wb wk wn kb kk len).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs2.kr_b_431 ())).
Qed.

Lemma kcut_store : forall mk byteof E M0 M allkn (wa : saddr) w (V : word) kb kk len,
  zf_kind mk byteof ->
  know_ok segs E M0 allkn -> (w <= 8)%nat -> flat E wa (Z.of_nat w) ->
  kentry_ok segs E M (mk (SA kb kk) len) ->
  Forall (kentry_ok segs E (wbytes M (adenot E wa) (word_to_le_bytes w V)))
         (kcut mk allkn (a_base wa) (a_off wa) (elen w) kb kk len).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs2.kr_b_432 ())).
Qed.

Lemma kzero_cut_store : forall E M0 M allkn (wa : saddr) w (V : word) kb kk len,
  know_ok segs E M0 allkn -> (w <= 8)%nat -> flat E wa (Z.of_nat w) ->
  kentry_ok segs E M (KZero (SA kb kk) len) ->
  Forall (kentry_ok segs E (wbytes M (adenot E wa) (word_to_le_bytes w V)))
         (kzero_cut allkn (a_base wa) (a_off wa) (elen w) kb kk len).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs2.kr_b_433 ())).
Qed.

Lemma in_sides_eq : forall allkn kn b1 k1 n1 b2 k2 n2,
  in_sides allkn (disj_sides allkn kn b1 k1 n1) b2 k2 n2 = kdisj_apart allkn kn b1 k1 n1 b2 k2 n2.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs2.kr_b_434 ())).
Qed.

Lemma in_sides_x_eq : forall allkn kn b1 k1 n1 b2 k2 n2,
  in_sides_x allkn (disj_sides_x allkn kn b1 k1 n1) b2 k2 n2 = kdisj_apart_x allkn kn b1 k1 n1 b2 k2 n2.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs2.kr_b_435 ())).
Qed.

Lemma ranges_apart_p_eq : forall kn b1 k1 n1 b2 k2 n2,
  ranges_apart_p kn (mk_sprep kn b1 k1 n1) b1 k1 n1 b2 k2 n2 = ranges_apart_x kn b1 k1 n1 b2 k2 n2.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs2.kr_b_436 ())).
Qed.

Lemma prune1p_eq : forall allkn wa w wv K hints,
  prune1p allkn (mk_sprep allkn (a_base wa) (a_off wa) (elen w)) wa w wv K hints = prune1 allkn wa w wv K hints.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs2.kr_b_437 ())).
Qed.

Lemma prunep_eq : forall allkn wa w wv kn hints,
  prunep allkn (mk_sprep allkn (a_base wa) (a_off wa) (elen w)) wa w wv kn hints = prune allkn wa w wv kn hints.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs2.kr_b_438 ())).
Qed.

Lemma ranges_apart_pc_eq : forall kn sp b1 k1 n1 b2 k2 n2,
  ranges_apart_pc kn sp b1 k1 n1 (base_range kn b2) b2 k2 n2 = ranges_apart_p kn sp b1 k1 n1 b2 k2 n2.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs2.kr_b_439 ())).
Qed.

Lemma prune1pc_eq : forall allkn sp wa w wv K hints br2,
  match kbase K with Some kb => br2 = base_range allkn kb | None => True end ->
  prune1pc allkn sp wa w wv K hints br2 = prune1p allkn sp wa w wv K hints.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs2.kr_b_440 ())).
Qed.

Definition br_cache_ok (allkn : list kentry) (c : list (expr * option (Z * Z))) : Prop := ltac2:(Rpl.RP.run_k (rplG ()) 2 (AxSymExec3SoundK_blobs2.kr_b_441 ())).

Lemma br_lookup_ok : forall allkn c b r, br_cache_ok allkn c -> br_lookup c b = Some r -> r = base_range allkn b.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs2.kr_b_442 ())).
Qed.

Lemma prunepc_eq : forall allkn sp wa w wv kn hints cache,
  br_cache_ok allkn cache ->
  prunepc allkn sp wa w wv kn hints cache = prunep allkn sp wa w wv kn hints.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs2.kr_b_443 ())).
Qed.

Lemma zf_piece : forall mk byteof E M (wb : expr) (wk : Z) w (V : word) (kk l0 i0 len : Z),
  zf_kind mk byteof ->
  flat E (SA wb wk) (Z.of_nat w) ->
  kentry_ok segs E M (mk (SA wb kk) (ELit l0)) ->
  (0 <= i0)%Z -> (0 < len)%Z -> (i0 + len <= l0 mod 2 ^ 64)%Z ->
  ((kk + i0 + len <= wk)%Z \/ (wk + Z.of_nat w <= kk + i0)%Z) ->
  kentry_ok segs E (wbytes M (adenot E (SA wb wk)) (word_to_le_bytes w V))
            (mk (SA wb (kk + i0)) (ELit len)).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs2.kr_b_444 ())).
Qed.

Lemma ktrim_sound : forall mk byteof E M (wb : expr) (wk : Z) w (V : word) kk l0,
  zf_kind mk byteof ->
  flat E (SA wb wk) (Z.of_nat w) ->
  kentry_ok segs E M (mk (SA wb kk) (ELit l0)) ->
  Forall (kentry_ok segs E (wbytes M (adenot E (SA wb wk)) (word_to_le_bytes w V))) (ktrim mk wb kk l0 wk w).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs2.kr_b_445 ())).
Qed.

Lemma zf_frame : forall mk byteof E M (wa : saddr) w (V : word) kb kk len,
  zf_kind mk byteof -> flat E wa (Z.of_nat w) ->
  kentry_ok segs E M (mk (SA kb kk) len) ->
  ((estart E wa + Z.of_nat w <= estart E (SA kb kk)) \/ (estart E (SA kb kk) + elenZ E len <= estart E wa))%Z ->
  kentry_ok segs E (wbytes M (adenot E wa) (word_to_le_bytes w V)) (mk (SA kb kk) len).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs2.kr_b_446 ())).
Qed.

Lemma prune_zf_sound : forall mk byteof E (anybase : word -> option byte) M0 allkn M (wb : expr) (wk : Z) w (V : word)
                              kb kk len apart hints diffbase kept scs hs',
  zf_kind mk byteof ->
  prune_zf mk allkn wb wk w (mk (SA kb kk) len) kb kk len apart hints diffbase = (kept, scs, hs') ->
  know_ok segs E M0 allkn -> (w <= 8)%nat -> flat E (SA wb wk) (Z.of_nat w) ->
  kentry_ok segs E M (mk (SA kb kk) len) ->
  (apart tt = true ->
   ((estart E (SA wb wk) + Z.of_nat w <= estart E (SA kb kk)) \/ (estart E (SA kb kk) + elenZ E len <= estart E (SA wb wk)))%Z) ->
  (diffbase tt = (kept, scs, hs') -> scs_denot segs anybase E scs ->
   Forall (kentry_ok segs E (wbytes M (adenot E (SA wb wk)) (word_to_le_bytes w V))) kept) ->
  scs_denot segs anybase E scs ->
  Forall (kentry_ok segs E (wbytes M (adenot E (SA wb wk)) (word_to_le_bytes w V))) kept.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs2.kr_b_447 ())).
Qed.

Lemma word_slice_bytes : forall w' d n (V : word), (d + n <= w')%nat -> (w' <= 8)%nat ->
  word_to_le_bytes n (ext_val false d n V) = firstn n (skipn d (word_to_le_bytes w' V)).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs2.kr_b_448 ())).
Qed.

Lemma kword_cut_sound : forall E M (wb : expr) (wk : Z) w (V : word) kk w' v,
  flat E (SA wb wk) (Z.of_nat w) ->
  kentry_ok segs E M (KWord (SA wb kk) w' v) ->
  (Z.leb (kk + Z.of_nat w') wk || Z.leb (wk + Z.of_nat w) kk)%bool = false ->
  Forall (kentry_ok segs E (wbytes M (adenot E (SA wb wk)) (word_to_le_bytes w V))) (kword_cut wb kk w' v wk w).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs2.kr_b_449 ())).
Qed.

Lemma prune1_sound : forall E (anybase : word -> option byte) M0 allkn M wa w wv K hints kept scs hs',
  let V := edenot E wv in
  prune1 allkn wa w wv K hints = (kept, scs, hs') ->
  know_ok segs E M0 allkn ->
  (w <= 8)%nat ->
  flat E wa (Z.of_nat w) ->
  kentry_ok segs E M K ->
  match K with KWord _ w' _ => (w' <= 8)%nat | _ => True end ->
  scs_denot segs anybase E scs ->
  Forall (kentry_ok segs E (wbytes M (adenot E wa) (word_to_le_bytes w V))) kept.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs2.kr_b_450 ())).
Qed.

Fixpoint kn_words_le8 (kn : list kentry) : Prop :=
  match kn with
  | [] => True
  | KWord _ w' _ :: r => (w' <= 8)%nat /\ kn_words_le8 r
  | _ :: r => kn_words_le8 r
  end.

Lemma know_ok_words_le8 : forall E M kn, know_ok segs E M kn -> kn_words_le8 kn.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs2.kr_b_451 ())).
Qed.

Lemma prune_sound : forall E (anybase : word -> option byte) M0 allkn M wa w wv kn hints kn' scs hs',
  prune allkn wa w wv kn hints = (kn', scs, hs') ->
  know_ok segs E M0 allkn ->
  (w <= 8)%nat -> flat E wa (Z.of_nat w) ->
  know_ok segs E M kn ->
  scs_denot segs anybase E scs ->
  know_ok segs E (wbytes M (adenot E wa) (word_to_le_bytes w (edenot E wv))) kn'.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs2.kr_b_452 ())).
Qed.

Lemma carry_sound : forall E (anybase : word -> option byte) base log kn hints kn' scs hs',
  carry log kn hints = (kn', scs, hs') ->
  log_flat E log -> know_ok segs E base kn -> scs_denot segs anybase E scs ->
  know_ok segs E (mem_denot E base log) kn'.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs2.kr_b_453 ())).
Qed.

Lemma wbytes_nth : forall bs m (a : word) j,
  (bv_unsigned a + Z.of_nat (length bs) <= 2 ^ 64)%Z -> (j < length bs)%nat ->
  wbytes m a bs (Z_to_bv 64 (bv_unsigned a + Z.of_nat j)) = Some (nth j bs (Z_to_bv 8 0)).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs2.kr_b_454 ())).
Qed.

Lemma know_ok_fill_intro_pt : forall E M (a : saddr) (n : expr) c,
  flat E a (elenZ E n) ->
  (forall i, (0 <= i < elenZ E n)%Z -> M (Z_to_bv 64 (estart E a + i)) = Some (Z_to_bv 8 c)) ->
  kentry_ok segs E M (KFill a n c).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs2.kr_b_455 ())).
Qed.

Lemma know_ok_fill_intro : forall E M (a : saddr) (n : nat) (ne : expr) c,
  flat E a (Z.of_nat n) -> elenZ E ne = Z.of_nat n ->
  kentry_ok segs E (wbytes M (adenot E a) (repeat (Z_to_bv 8 c) n)) (KFill a ne c).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs2.kr_b_456 ())).
Qed.

Lemma kentry_ok_frame_bytes : forall E M (wa : saddr) (bs : list byte) K (ka : saddr) (kl : expr),
  flat E wa (Z.of_nat (length bs)) ->
  kentry_ok segs E M K ->
  match K with
  | KWord a w' _ => ka = a /\ kl = elen w' /\ (w' <= 8)%nat
  | KZero a n => ka = a /\ kl = n
  | KBlob a n _ => ka = a /\ kl = n
  | KImg lo hi => ka = SA (ELit 0) lo /\ kl = ELit (hi - lo) /\ (hi - lo < 2 ^ 64)%Z
  | KAlign _ _ => True
  | KRange _ _ _ => True
  | KWr _ _ => True
  | KDisj _ _ _ _ => True
  | KFill a n _ => ka = a /\ kl = n
  | KUnk a n => ka = a /\ kl = n
  end ->
  ((estart E wa + Z.of_nat (length bs) <= estart E ka)%Z \/ (estart E ka + elenZ E kl <= estart E wa)%Z) ->
  kentry_ok segs E (wbytes M (adenot E wa) bs) K.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs2.kr_b_457 ())).
Qed.

Lemma know_ok_unk_intro_pt : forall E M (a : saddr) (n : expr),
  flat E a (elenZ E n) ->
  (forall i, (0 <= i < elenZ E n)%Z -> M (Z_to_bv 64 (estart E a + i)) <> None) ->
  kentry_ok segs E M (KUnk a n).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs2.kr_b_458 ())).
Qed.

Lemma know_ok_unk_intro : forall E M (a : saddr) (bs : list byte) (ne : expr),
  flat E a (Z.of_nat (length bs)) -> elenZ E ne = Z.of_nat (length bs) ->
  kentry_ok segs E (wbytes M (adenot E a) bs) (KUnk a ne).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs2.kr_b_459 ())).
Qed.

Lemma kunk_of_zero : forall E M a n, kentry_ok segs E M (KZero a n) -> kentry_ok segs E M (KUnk a n).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs2.kr_b_460 ())).
Qed.

Lemma kunk_of_fill : forall E M a n c, kentry_ok segs E M (KFill a n c) -> kentry_ok segs E M (KUnk a n).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs2.kr_b_461 ())).
Qed.

Lemma kunk_of_blob : forall E M a n k, kentry_ok segs E M (KBlob a n k) -> kentry_ok segs E M (KUnk a n).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs2.kr_b_462 ())).
Qed.

Lemma kentry_ok_unk_grows : forall E M M' a n,
  mem_grows M M' -> kentry_ok segs E M (KUnk a n) -> kentry_ok segs E M' (KUnk a n).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs2.kr_b_463 ())).
Qed.

Lemma kentry_ok_unk_frame : forall E M (wa : word) (bs : list byte) a n,
  kentry_ok segs E M (KUnk a n) -> kentry_ok segs E (wbytes M wa bs) (KUnk a n).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs2.kr_b_464 ())).
Qed.

Lemma kunk_store_ok : forall E M (a : saddr) (n : expr) d m,
  kentry_ok segs E M (KUnk a n) -> (0 <= d)%Z -> (d + Z.of_nat m <= elenZ E n)%Z ->
  RiscvSemantics.store_ok segs M (Z_to_bv 64 (estart E a + d)) m = true.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 (AxSymExec3SoundK_blobs2.kr_b_465 ())).
Qed.

End CarrySound.

End AX2SK.
