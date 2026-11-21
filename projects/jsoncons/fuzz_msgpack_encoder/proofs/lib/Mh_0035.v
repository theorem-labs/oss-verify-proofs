(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: changed Wf_inside, Wf_outside, Wn_outside and 43 more. *)
(* [comment removed for export] *)
Set Warnings "-require-in-module".
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel. From Stdlib Require ZArith List Lia Bool. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType. From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Module ArtAtomics.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StepTac OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.WalkTac.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_ArtAtomics () := "C47Corelib7Program6Basics4flipC46Stdlib5Lists4List6nth_okC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List:firstn_nilC47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List=repeat_lengthC56Stdlib6ZArith6BinInt1Z3addK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3divI47Corelib4Init5Logic2eq00C47Corelib7Classes?RelationClasses=eq_TransitiveC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes9Morphisms@reflexive_properC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismK47Corelib4Init5Logic2eq01K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7div_modC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z2leC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega6VarMap1t01C56Stdlib6ZArith6BinInt1Z7mod_addC56Stdlib6ZArith6BinInt1Z8add_commC56Stdlib6ZArith6BinInt1Z?add_mod_idemp_rK47Corelib7Numbers7BinNums8positive02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula07I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op201C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordK47Corelib4Init9Datatypes6option01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallI47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyK45stdpp9bitvector;definitions2bv01K4ELinuxProcessSemantics5Riscv5Instr5instr0FK47Corelib4Init9Datatypes4prod01C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=bytes_le_to_ZC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsDdecode_exec_accessesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_memC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=fetch_word_ovC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>fetch_tail_anyC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=fetch_failureK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsBdrop_access_reportC49OSSVerify5KrLib8PropExec6v_addiC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec5v_addC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC59OSSVerify5KrLib7Mh_00387CatExec6wbytesC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_regsC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8ms_fregsC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics9ms_pc_valC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_regC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_resvC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_fcsrC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_romK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state01C45stdpp9bitvector;definitions7Z_to_bvK4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsCinterp_eff_accessesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<access_valueC4ELinuxProcessSemantics5Riscv3Sem6c_regsC4ELinuxProcessSemantics5Riscv3Sem7c_fregsC4ELinuxProcessSemantics5Riscv3Sem4c_pcC4ELinuxProcessSemantics5Riscv3Sem6c_resvC4ELinuxProcessSemantics5Riscv3Sem6c_fcsrC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics?accessed_rangesC4ELinuxProcessSemantics5Riscv7DecodeCBis_defined_illegalC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC4ELinuxProcessSemantics5Riscv3Sem7reg_getC4ELinuxProcessSemantics5Riscv3Sem5is_x0C49OSSVerify5KrLib8PropExec=bv_eqb0_is_x0C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memC4ELinuxProcessSemantics5Riscv3Sem;amo_alignedC47Corelib4Init9Datatypes4negbC49OSSVerify5KrLib8PropExec7fp_regsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6fp_csrC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv3Sem3eff06C45stdpp9bitvector;definitions6bv_addC4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setK4ELinuxProcessSemantics5Riscv3Sem3eff01K4ELinuxProcessSemantics5Riscv3Sem3eff08K4ELinuxProcessSemantics5Riscv3Sem3eff07C56Stdlib6ZArith6BinInt1Z3eqbC45stdpp9bitvector;definitions5bv_eqC56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith6BinInt1Z6shiftrC45stdpp9bitvector;definitions7bv_wrapC45stdpp9bitvector;definitionsCbv_wrap_bv_unsignedC56Stdlib6ZArith6BinInt1Z:shiftr_0_rC45stdpp9bitvector;definitionsCbv_extract_unsignedC4ELinuxProcessSemantics5Riscv3Sem5alu64C49OSSVerify5KrLib8PropExec7alu_addC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6b_npc4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387CatExecCwrite_to_mem_wbytesC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec9le_word_vC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6ov_rdnC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8eqb_reflC4ELinuxProcessSemantics5Riscv3Sem9amo_bytesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5ms_pcC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C45stdpp9bitvector;definitions:bv_extractC4ELinuxProcessSemantics5Riscv3Sem7amo_valI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics5Riscv3Sem4core00K47Corelib7Numbers7BinNums1N01I47Corelib4Init9Datatypes3nat00K4ELinuxProcessSemantics5Riscv5Instr5amoop02I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00K4ELinuxProcessSemantics5Riscv5Instr6awidth02K47Corelib4Init5Logic4True01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessI4ELinuxProcessSemantics5Riscv3Sem3eff00I47Corelib7Numbers7BinNums1N00I47Corelib7Numbers7BinNums8positive00K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5instr0:c59OSSVerify5KrLib7Mh_0035:ArtAtomics5mkstrC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6regupdC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics5Riscv5Instr5aluop00C49OSSVerify5KrLib8PropExec5v_andC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7alu_andC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0035:ArtAtomics=art_step_op_rC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop0:C49OSSVerify5KrLib8PropExec5v_xorC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7alu_xorC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop06C49OSSVerify5KrLib8PropExec4v_orC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6alu_orC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop09K4ELinuxProcessSemantics5Riscv5Instr5instr05C45stdpp9bitvector;definitions9bv_signedC49OSSVerify5KrLib8PropExec4btgtC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem<branch_takenC4ELinuxProcessSemantics5Riscv7Prelude4sextC49OSSVerify5KrLib8PropExec9b_addsextC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics5Riscv5Instr;branch_cond00K4ELinuxProcessSemantics5Riscv5Instr5instr0DC49OSSVerify5KrLib8PropExec4v_lwC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec8b_lw_valC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr6awidth01K4ELinuxProcessSemantics5Riscv5Instr5instr0EC4ELinuxProcessSemantics5Riscv3Sem5low32C59OSSVerify5KrLib7Mh_00387SeqExecAstore_bytes_low32C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powc59OSSVerify5KrLib7Mh_0035:ArtAtomics@art_mod32_helperC1?~~~~~~~~~~~~~~~C35stdpp7tactics<f_equal_helpC56Stdlib6ZArith6BinInt1Z6of_natC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC46Stdlib9micromega;ZifyClasses;rew_iff_revC59OSSVerify5KrLib7Mh_00387SeqExecBZ_to_le_bytes_wrapC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega5Tauto8GFormula05C45stdpp9bitvector;definitions=bv_wrap_smallC45stdpp9bitvector;definitions@Z_to_bv_unsignedC45stdpp9bitvector;definitions?bv_add_unsignedC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib4Init5Logic4True00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205".
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Lemma art_mod32_helper : forall a b : Z,
  ((a + b mod 4294967296) mod 4294967296 = ((a + b) mod (4294967296 * 4294967296)) mod 4294967296)%Z.
Proof.
  intros a b. rewrite Z.add_mod_idemp_r by lia.
  set (x := (a + b)%Z). set (MM := (4294967296 * 4294967296)%Z).
  rewrite (Z.div_mod x MM) at 1 by lia.
  replace (MM * (x / MM))%Z with ((4294967296 * (x / MM)) * 4294967296)%Z by (unfold MM; lia).
  rewrite Z.add_comm, Z.mod_add by lia. reflexivity.
Qed.

Section FPX. Context {fx : PropExec.FPState}.

Lemma art_step_amoadd_d_x0 : forall segs regs pc mem rom w aq rl (rs1 rs2 : reg) (a v old : word) bs,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Amo AMO_ADD AD aq rl 0 rs1 rs2, 4%Z) ->
  getr regs rs1 = a -> (bv_unsigned a mod 8 = 0)%Z ->
  rdn segs mem a 8%nat = Some bs -> bytes_le_to_Z bs = bv_unsigned old ->
  getr regs rs2 = v ->
  RiscvSemantics.store_ok segs mem a 8%nat = true ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs (v_addi pc 4) (wbytes mem a (word_to_le_bytes 8 (v_add old v))) rom).
Proof.
  intros segs regs pc mem rom w aq rl rs1 rs2 a v old bs Hf He Hd Ha Hal Hread Hv Hrs2 Hok.
  step_pipeline Hf He Hd.
  unfold getr in Ha, Hrs2; rewrite ?bv_eqb0_is_x0 in Ha, Hrs2.
  rewrite Ha, Hrs2.
  unfold amo_aligned. cbn [amo_bytes]. rewrite Hal. rewrite Z.eqb_refl.
  cbv beta iota zeta delta
    [RiscvSemantics.interp_eff_accesses RiscvSemantics.width_bytes RiscvSemantics.width_bytesZ negb Sem.is_x0
     Sem.rget Sem.rset Sem.with_regs Sem.with_pc Sem.with_resv Sem.inval_resv Sem.c_regs Sem.c_fregs Sem.c_pc Sem.c_fcsr Sem.c_resv
     ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom ms_fregs ms_fcsr mkst].
  assert (Hz : bv_extract 0 64 old = old).
  { apply bv_eq. rewrite bv_extract_unsigned, Z.shiftr_0_r. apply bv_wrap_bv_unsigned. }
  rewrite ov_rdn, Hread; cbv beta iota.
  rewrite (le_word_v _ _ Hv), Hz.
  rewrite Hok; cbv beta iota.
  replace (bv_unsigned (0%bv : bv 5) =? 0)%Z with true by reflexivity. cbv beta iota.
  rewrite ?write_to_mem_wbytes, ?b_npc4, <- alu_add.
  reflexivity.
Qed.

(* [comment removed for export] *)
Definition mkstr (regs : bvmap 5 word) (pc : word) (mem rom : word -> option byte) (r : option word) : machine_state :=
  {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc; ms_svc_pending := None; ms_resv := r; ms_fcsr := fp_csr;
     ms_mem := mem; ms_rom := rom |}.

Lemma mkstr_none : forall regs pc mem rom, mkstr regs pc mem rom None = mkst regs pc mem rom.
Proof.
ltac2:(KReplay.run1 (kr_t_ArtAtomics ()) ["FPX"] "h03memh12pch24regsh33romp;1p;2p;5p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9g00YbR1p4p7210R0p1000ip4p710R2p8P0p100ZNp4p710p8p1000Np4p710P2p8p1001Gp4p710p1001fp4p710p8p1002Bp4p710P2p8g00Ooj10Tg00[Uj17Tg00\:j11Tg00\Xj12TP1j26Tg00];j15Tg00hSj54Tg00;Yj23Tg00Ui#0R1#7#1%01#0R1#0#0#0#1#2R2'6%11#2#5\2R1g01e9p,2fxf3f2f1f0D4'3X31W0X12W2o"). Qed.

#[local] Ltac step_pipeline_r Hfetch Hecall Hdecode :=
  unfold RiscvSemantics.step, RiscvSemantics.step_accesses;
  cbn [ms_pc ms_pc_val mkstr];
  rewrite Hfetch; cbv beta iota;
  unfold RiscvSemantics.drop_access_report, RiscvSemantics.decode_exec_accesses;
  rewrite Hecall; cbv beta iota;
  rewrite Hdecode;
  cbv beta iota zeta delta
    [RiscvSemantics.interp_eff_accesses RiscvSemantics.width_bytes RiscvSemantics.width_bytesZ
     Sem.exec Sem.load_val Sem.store_val Sem.rget Sem.rset Sem.with_regs Sem.with_pc Sem.with_resv Sem.inval_resv Sem.w0 Sem.w1
     Sem.c_regs Sem.c_fregs Sem.c_pc Sem.c_fcsr Sem.c_resv ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom ms_fregs ms_fcsr mkstr];
  rewrite ?bv_eqb0_is_x0.

(* [comment removed for export] *)
Lemma art_step_op_r : forall segs regs pc mem rom w op rd rs1 rs2 r,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op op rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (mkstr regs pc mem rom r) =
  MachineOk (mkstr (if bv_eqb rd 0 then regs else regupd regs rd (alu64 op (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom r).
Proof.
  intros segs regs pc mem rom w op rd rs1 rs2 r Hf He Hd.
  step_pipeline_r Hf He Hd.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  destruct (is_x0 rs1); destruct (is_x0 rs2); destruct (is_x0 rd); cbv beta iota; rewrite ?b_npc4; reflexivity.
Qed.

Lemma art_step_and_r : forall segs regs pc mem rom w rd rs1 rs2 r,
  fetch_word segs pc = Some w -> is_ecall w = false -> decode_any w = Some (Op ALU_AND rd rs1 rs2, 4%Z) -> bv_eqb rd 0 = false ->
  RiscvSemantics.step segs (mkstr regs pc mem rom r) = MachineOk (mkstr (regupd regs rd (v_and (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom r).
Proof.
ltac2:(KReplay.run1 (kr_t_ArtAtomics ()) ["FPX"] "h01bh12Hdh22Heh32Hfh43Hrdh51mh63memh72pch81rh92rdh:4regsh;3romh<3rs1h=3rs2h>4segsh?1wp;1p;2p;3p;4p;5p;6p;>p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9g00YbR1p4p7210R0g000iR2p4p710R3p8P0p100ZNp4p710p8p1000Np4p710P3p8p1001Gp4p710p1001fp4p710p8p1002Bp4p710P3p8g00A8j1NTg00Ooj11Tg00[Uj1ETg00\:j15Tg00\Xj18TP1j2ITg00];j17Tg00]]j2DTg00^_j2>Tg0059j30Tg00_Aj1ATg00`Aj2@Tg00`aj1?Tg01oBj4MTg003Aj1LTg00baj4KTg00aRj3HTg01G5j3=Tg00gKj1FTg00cAj26Tg01YLj3<Tg020kj33Tg0129j2;Tg01onj52Tg01b^j24Tg022Kj2:Tg00;Yj2CTg023>j2GTP2j69Tg01`[j2BTg0243l>JTg01hR#Ng00Ui#1R2#E#5R1%12R2#1R3#1#1R0#1#5#8R4'IR5%53#8#7\4R3%50#8R0%81R6%74%70f9R7f7R8'Df4R9,>030g00XER0f5R:#Ag01iQR;30g01j1R<g00RGR='@R>#7f6R?#?P<P=g0258R=P:P9f3R<CM%L2R2CK,>>30g00UKg01kJ5H1R>9=1?=00;g01e9R@#FRAP0P5A=18>R>f<R1161?RB161:RC5<=RD9318n0100000020000f;RE/;2RFf:RGP7P9D2,4@f0RHf=RIf8RJ16I8RK16I?RL':331;12R2PEPGP:D2,4@RM50AX5AP0P;P0P5PHPIA<=KL93IJn0100000020000P2PEPGP:D2,4@=0AMX00P41:BCR0A3IJHP2PEPGP:D2,4@=0AMX04A3180PFPGP7P9D2,4@,CAPD1GBCE9P>PHE9P1PEPGP7P9D2,BIPIP1PEPGP7PJP=P8P?P:P9P<f2f1M>JE9W4W1W2W3W8X=6X<6W9W?X;3W6X74W:W>o"). Qed.
Lemma art_step_xor_r : forall segs regs pc mem rom w rd rs1 rs2 r,
  fetch_word segs pc = Some w -> is_ecall w = false -> decode_any w = Some (Op ALU_XOR rd rs1 rs2, 4%Z) -> bv_eqb rd 0 = false ->
  RiscvSemantics.step segs (mkstr regs pc mem rom r) = MachineOk (mkstr (regupd regs rd (v_xor (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom r).
Proof.
ltac2:(KReplay.run1 (kr_t_ArtAtomics ()) ["FPX"] "h01bh12Hdh22Heh32Hfh43Hrdh51mh63memh72pch81rh92rdh:4regsh;3romh<3rs1h=3rs2h>4segsh?1wp;1p;2p;3p;4p;5p;6p;>p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9g00YbR1p4p7210R0g000iR2p4p710R3p8P0p100ZNp4p710p8p1000Np4p710P3p8p1001Gp4p710p1001fp4p710p8p1002Bp4p710P3p8g00A8j1NTg00Ooj11Tg00[Uj1ETg00\:j15Tg00\Xj18TP1j2ITg00];j17Tg00]]j2DTg00^_j2>Tg0059j30Tg00_Aj1ATg00`Aj2@Tg00`aj1?Tg01oBj4MTg003Aj1LTg00baj4KTg00aRj3HTg01G5j3=Tg00gKj1FTg00cAj26Tg01YLj3<Tg020kj33Tg0129j2;Tg01onj52Tg01b^j24Tg025dj2:Tg00;Yj2CTg026Wj2GTP2j69Tg01`[j2BTg0243l>JTg01hR#Ng00Ui#1R2#E#5R1%12R2#1R3#1#1R0#1#5#8R4'IR5%53#8#7\4R3%50#8R0%81R6%74%70f9R7f7R8'Df4R9,>030g00XER0f5R:#Ag01iQR;30g01j1R<g00RGR='@R>#7f6R?#?P<P=g027LR=P:P9f3R<CM%L2R2CK,>>30g00UKg01kJ5H1R>9=1?=00;g01e9R@#FRAP0P5A=18>R>f<R1161?RB161:RC5<=RD9318n0100000020000f;RE/;2RFf:RGP7P9D2,4@f0RHf=RIf8RJ16I8RK16I?RL':331;12R2PEPGP:D2,4@RM50AX5AP0P;P0P5PHPIA<=KL93IJn0100000020000P2PEPGP:D2,4@=0AMX00P41:BCR0A3IJHP2PEPGP:D2,4@=0AMX04A3180PFPGP7P9D2,4@,CAPD1GBCE9P>PHE9P1PEPGP7P9D2,BIPIP1PEPGP7PJP=P8P?P:P9P<f2f1M>JE9W4W1W2W3W8X=6X<6W9W?X;3W6X74W:W>o"). Qed.
Lemma art_step_or_r : forall segs regs pc mem rom w rd rs1 rs2 r,
  fetch_word segs pc = Some w -> is_ecall w = false -> decode_any w = Some (Op ALU_OR rd rs1 rs2, 4%Z) -> bv_eqb rd 0 = false ->
  RiscvSemantics.step segs (mkstr regs pc mem rom r) = MachineOk (mkstr (regupd regs rd (v_or (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom r).
Proof.
ltac2:(KReplay.run1 (kr_t_ArtAtomics ()) ["FPX"] "h01bh12Hdh22Heh32Hfh43Hrdh51mh63memh72pch81rh92rdh:4regsh;3romh<3rs1h=3rs2h>4segsh?1wp;1p;2p;3p;4p;5p;6p;>p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9g00YbR1p4p7210R0g000iR2p4p710R3p8P0p100ZNp4p710p8p1000Np4p710P3p8p1001Gp4p710p1001fp4p710p8p1002Bp4p710P3p8g00A8j1NTg00Ooj11Tg00[Uj1ETg00\:j15Tg00\Xj18TP1j2ITg00];j17Tg00]]j2DTg00^_j2>Tg0059j30Tg00_Aj1ATg00`Aj2@Tg00`aj1?Tg01oBj4MTg003Aj1LTg00baj4KTg00aRj3HTg01G5j3=Tg00gKj1FTg00cAj26Tg01YLj3<Tg020kj33Tg0129j2;Tg01onj52Tg01b^j24Tg0288j2:Tg00;Yj2CTg028jj2GTP2j69Tg01`[j2BTg0243l>JTg01hR#Ng00Ui#1R2#E#5R1%12R2#1R3#1#1R0#1#5#8R4'IR5%53#8#7\4R3%50#8R0%81R6%74%70f9R7f7R8'Df4R9,>030g00XER0f5R:#Ag01iQR;30g01j1R<g00RGR='@R>#7f6R?#?P<P=g029^R=P:P9f3R<CM%L2R2CK,>>30g00UKg01kJ5H1R>9=1?=00;g01e9R@#FRAP0P5A=18>R>f<R1161?RB161:RC5<=RD9318n0100000020000f;RE/;2RFf:RGP7P9D2,4@f0RHf=RIf8RJ16I8RK16I?RL':331;12R2PEPGP:D2,4@RM50AX5AP0P;P0P5PHPIA<=KL93IJn0100000020000P2PEPGP:D2,4@=0AMX00P41:BCR0A3IJHP2PEPGP:D2,4@=0AMX04A3180PFPGP7P9D2,4@,CAPD1GBCE9P>PHE9P1PEPGP7P9D2,BIPIP1PEPGP7PJP=P8P?P:P9P<f2f1M>JE9W4W1W2W3W8X=6X<6W9W?X;3W6X74W:W>o"). Qed.

(* [comment removed for export] *)
Lemma art_step_branch_tk_r : forall segs regs pc mem rom w c rs1 rs2 (imm : bv 13) r,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Branch c rs1 rs2 imm, 4%Z) ->
  branch_taken c (getr regs rs1) (getr regs rs2) = true ->
  RiscvSemantics.step segs (mkstr regs pc mem rom r) = MachineOk (mkstr regs (btgt pc (bv_signed imm)) mem rom r).
Proof.
  intros segs regs pc mem rom w c rs1 rs2 imm r Hfetch Hecall Hdecode Hc.
  step_pipeline_r Hfetch Hecall Hdecode.
  unfold getr in Hc; rewrite ?bv_eqb0_is_x0 in Hc.
  destruct (is_x0 rs1); destruct (is_x0 rs2); cbv beta iota; rewrite Hc; cbv beta iota; rewrite b_addsext; reflexivity.
Qed.
Lemma art_step_branch_ft_r : forall segs regs pc mem rom w c rs1 rs2 (imm : bv 13) r,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Branch c rs1 rs2 imm, 4%Z) ->
  branch_taken c (getr regs rs1) (getr regs rs2) = false ->
  RiscvSemantics.step segs (mkstr regs pc mem rom r) = MachineOk (mkstr regs (v_addi pc 4) mem rom r).
Proof.
  intros segs regs pc mem rom w c rs1 rs2 imm r Hfetch Hecall Hdecode Hc.
  step_pipeline_r Hfetch Hecall Hdecode.
  unfold getr in Hc; rewrite ?bv_eqb0_is_x0 in Hc.
  destruct (is_x0 rs1); destruct (is_x0 rs2); cbv beta iota; rewrite Hc; cbv beta iota; rewrite ?b_npc4; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma art_step_lr_w : forall segs regs pc mem rom w aq rl rd rs1 a bs v r,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Lr AW aq rl rd rs1, 4%Z) -> bv_eqb rd 0 = false ->
  getr regs rs1 = a -> (bv_unsigned a mod 4 = 0)%Z ->
  rdn segs mem a 4%nat = Some bs -> bytes_le_to_Z bs = bv_unsigned v ->
  RiscvSemantics.step segs (mkstr regs pc mem rom r) = MachineOk (mkstr (regupd regs rd (v_lw v)) (v_addi pc 4) mem rom (Some a)).
Proof.
  intros segs regs pc mem rom w aq rl rd rs1 a bs v r Hf He Hd Hrd Ha Hal Hread Hv.
  step_pipeline_r Hf He Hd.
  unfold getr in Ha; rewrite ?bv_eqb0_is_x0 in Ha. rewrite Ha.
  unfold amo_aligned. cbn [amo_bytes]. rewrite Hal, Z.eqb_refl.
  cbv beta iota zeta delta
    [RiscvSemantics.interp_eff_accesses RiscvSemantics.width_bytes RiscvSemantics.width_bytesZ negb Sem.is_x0
     Sem.rget Sem.rset Sem.with_regs Sem.with_pc Sem.with_resv Sem.inval_resv Sem.c_regs Sem.c_fregs Sem.c_pc Sem.c_fcsr Sem.c_resv
     ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom ms_fregs ms_fcsr mkstr].
  rewrite ov_rdn, Hread; cbv beta iota.
  rewrite (le_word_v _ _ Hv), b_lw_val, ?b_npc4.
  unfold bv_eqb in Hrd. change (bv_unsigned (0%bv : bv 5)) with 0%Z in Hrd. rewrite Hrd. cbv beta iota.
  reflexivity.
Qed.

#[local] Ltac amo_unfold :=
  cbv beta iota zeta delta
    [RiscvSemantics.interp_eff_accesses RiscvSemantics.width_bytes RiscvSemantics.width_bytesZ negb Sem.is_x0
     Sem.rget Sem.rset Sem.with_regs Sem.with_pc Sem.with_resv Sem.inval_resv Sem.c_regs Sem.c_fregs Sem.c_pc Sem.c_fcsr Sem.c_resv
     ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom ms_fregs ms_fcsr mkstr mkst].

(* [comment removed for export] *)
Lemma art_step_lr_d : forall segs regs pc mem rom w aq rl rd rs1 a bs v r,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Lr AD aq rl rd rs1, 4%Z) -> bv_eqb rd 0 = false ->
  getr regs rs1 = a -> (bv_unsigned a mod 8 = 0)%Z ->
  rdn segs mem a 8%nat = Some bs -> bytes_le_to_Z bs = bv_unsigned v ->
  RiscvSemantics.step segs (mkstr regs pc mem rom r) = MachineOk (mkstr (regupd regs rd v) (v_addi pc 4) mem rom (Some a)).
Proof.
  intros segs regs pc mem rom w aq rl rd rs1 a bs v r Hf He Hd Hrd Ha Hal Hread Hv.
  assert (Hz : bv_extract 0 64 v = v).
  { apply bv_eq. rewrite bv_extract_unsigned, Z.shiftr_0_r. apply bv_wrap_bv_unsigned. }
  step_pipeline_r Hf He Hd.
  unfold getr in Ha; rewrite ?bv_eqb0_is_x0 in Ha. rewrite Ha.
  unfold amo_aligned. cbn [amo_bytes]. rewrite Hal, Z.eqb_refl. amo_unfold.
  rewrite ov_rdn, Hread; cbv beta iota.
  rewrite (le_word_v _ _ Hv), Hz, ?b_npc4.
  unfold bv_eqb in Hrd. change (bv_unsigned (0%bv : bv 5)) with 0%Z in Hrd. rewrite Hrd. cbv beta iota.
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma art_step_sc_w_ok : forall segs regs pc mem rom w aq rl rd rs1 rs2 a v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Sc AW aq rl rd rs1 rs2, 4%Z) -> bv_eqb rd 0 = false ->
  getr regs rs1 = a -> (bv_unsigned a mod 4 = 0)%Z -> getr regs rs2 = v ->
  RiscvSemantics.store_ok segs mem a 4%nat = true ->
  RiscvSemantics.step segs (mkstr regs pc mem rom (Some a)) =
  MachineOk (mkst (regupd regs rd (Z_to_bv 64 0)) (v_addi pc 4) (wbytes mem a (word_to_le_bytes 4 v)) rom).
Proof.
  intros segs regs pc mem rom w aq rl rd rs1 rs2 a v Hf He Hd Hrd Ha Hal Hv Hok.
  step_pipeline_r Hf He Hd.
  unfold getr in Ha, Hv; rewrite ?bv_eqb0_is_x0 in Ha, Hv. rewrite Ha, Hv.
  unfold amo_aligned. cbn [amo_bytes]. rewrite Hal, !Z.eqb_refl. amo_unfold.
  rewrite Hok; cbv beta iota.
  rewrite ?write_to_mem_wbytes, ?store_bytes_low32, ?b_npc4.
  unfold bv_eqb in Hrd. change (bv_unsigned (0%bv : bv 5)) with 0%Z in Hrd. rewrite Hrd. cbv beta iota.
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma art_step_sc_d_ok : forall segs regs pc mem rom w aq rl rd rs1 rs2 a v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Sc AD aq rl rd rs1 rs2, 4%Z) -> bv_eqb rd 0 = false ->
  getr regs rs1 = a -> (bv_unsigned a mod 8 = 0)%Z -> getr regs rs2 = v ->
  RiscvSemantics.store_ok segs mem a 8%nat = true ->
  RiscvSemantics.step segs (mkstr regs pc mem rom (Some a)) =
  MachineOk (mkst (regupd regs rd (Z_to_bv 64 0)) (v_addi pc 4) (wbytes mem a (word_to_le_bytes 8 v)) rom).
Proof.
  intros segs regs pc mem rom w aq rl rd rs1 rs2 a v Hf He Hd Hrd Ha Hal Hv Hok.
  step_pipeline_r Hf He Hd.
  unfold getr in Ha, Hv; rewrite ?bv_eqb0_is_x0 in Ha, Hv. rewrite Ha, Hv.
  unfold amo_aligned. cbn [amo_bytes]. rewrite Hal, !Z.eqb_refl. amo_unfold.
  rewrite Hok; cbv beta iota.
  rewrite ?write_to_mem_wbytes, ?b_npc4.
  unfold bv_eqb in Hrd. change (bv_unsigned (0%bv : bv 5)) with 0%Z in Hrd. rewrite Hrd. cbv beta iota.
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma art_step_amoadd_w_x0 : forall segs regs pc mem rom w aq rl (rs1 rs2 : reg) (a v old : word) bs,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Amo AMO_ADD AW aq rl 0 rs1 rs2, 4%Z) ->
  getr regs rs1 = a -> (bv_unsigned a mod 4 = 0)%Z ->
  rdn segs mem a 4%nat = Some bs -> bytes_le_to_Z bs = bv_unsigned old -> (bv_unsigned old < 2 ^ 32)%Z ->
  getr regs rs2 = v ->
  RiscvSemantics.store_ok segs mem a 4%nat = true ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs (v_addi pc 4) (wbytes mem a (word_to_le_bytes 4 (v_add old v))) rom).
Proof.
  intros segs regs pc mem rom w aq rl rs1 rs2 a v old bs Hf He Hd Ha Hal Hread Hv Hold Hrs2 Hok.
  step_pipeline Hf He Hd.
  unfold getr in Ha, Hrs2; rewrite ?bv_eqb0_is_x0 in Ha, Hrs2. rewrite Ha, Hrs2.
  unfold amo_aligned. cbn [amo_bytes]. rewrite Hal, Z.eqb_refl. amo_unfold.
  rewrite ov_rdn, Hread; cbv beta iota.
  rewrite (le_word_v _ _ Hv).
  rewrite Hok; cbv beta iota.
  replace (bv_unsigned (0%bv : bv 5) =? 0)%Z with true by reflexivity. cbv beta iota.
  rewrite ?write_to_mem_wbytes, ?b_npc4.
  assert (Hb : Z_to_le_bytes 4 (bv_unsigned (amo_val AMO_ADD (bv_extract 0 32 old) (low32 v))) = word_to_le_bytes 4 (v_add old v)).
  { cbn [amo_val]. unfold low32, word_to_le_bytes, v_add.
    rewrite bv_add_unsigned, !bv_extract_unsigned, !Z.shiftr_0_r, Z_to_bv_unsigned.
    rewrite (bv_wrap_small 32 (bv_unsigned old)) by (pose proof (u64_range old); change (bv_modulus 32) with 4294967296%Z; lia).
    rewrite Z_to_le_bytes_wrap by (cbn; lia).
    rewrite <- (Z_to_le_bytes_wrap 4 32 (bv_wrap 64 _)) by (cbn; lia).
    rewrite <- (Z_to_le_bytes_wrap 4 32 (bv_unsigned old + bv_wrap 32 (bv_unsigned v))) by (cbn; lia).
    f_equal. unfold bv_wrap.
    change (bv_modulus 64) with (4294967296 * 4294967296)%Z. change (bv_modulus 32) with 4294967296%Z.
    apply art_mod32_helper. }
  rewrite Hb. reflexivity.
Qed.
End FPX.

End ArtAtomics.
Module ArtAtomics2.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StepTac OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.WalkTac OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0035.ArtAtomics.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_ArtAtomics2 () := "C47Corelib7Program6Basics4flipC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00C46Stdlib5Lists4List6nth_okC46Stdlib5Lists4List:firstn_nilC47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List=repeat_lengthI47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordK47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallI47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyK4ELinuxProcessSemantics5Riscv5Instr5instr0FK47Corelib7Numbers7BinNums1Z02K47Corelib4Init9Datatypes4prod01K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z6moduloK47Corelib4Init9Datatypes3nat02C49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=bytes_le_to_ZC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsDdecode_exec_accessesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_memC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=fetch_word_ovC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>fetch_tail_anyC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=fetch_failureK47Corelib4Init9Datatypes4list01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsBdrop_access_reportC49OSSVerify5KrLib8PropExec6regupdC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6v_addiC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec5v_addC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC59OSSVerify5KrLib7Mh_00387CatExec6wbytesC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_regsC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8ms_fregsC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics9ms_pc_valC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_regC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_resvC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_fcsrC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_romK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state01C45stdpp9bitvector;definitions7Z_to_bvK4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsCinterp_eff_accessesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<access_valueC4ELinuxProcessSemantics5Riscv3Sem6c_regsC4ELinuxProcessSemantics5Riscv3Sem7c_fregsC4ELinuxProcessSemantics5Riscv3Sem4c_pcK47Corelib4Init9Datatypes6option02C4ELinuxProcessSemantics5Riscv3Sem6c_resvC4ELinuxProcessSemantics5Riscv3Sem6c_fcsrC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics?accessed_rangesC4ELinuxProcessSemantics5Riscv7DecodeCBis_defined_illegalC4ELinuxProcessSemantics5Riscv3Sem7reg_getC4ELinuxProcessSemantics5Riscv3Sem5is_x0C49OSSVerify5KrLib8PropExec=bv_eqb0_is_x0C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordK47Corelib4Init9Datatypes4list02C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memC4ELinuxProcessSemantics5Riscv3Sem;amo_alignedC47Corelib4Init9Datatypes4negbC49OSSVerify5KrLib8PropExec7fp_regsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6fp_csrC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv3Sem3eff06C45stdpp9bitvector;definitions6bv_addC4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setK4ELinuxProcessSemantics5Riscv3Sem3eff01K4ELinuxProcessSemantics5Riscv3Sem3eff08K4ELinuxProcessSemantics5Riscv3Sem3eff07C56Stdlib6ZArith6BinInt1Z3eqbC45stdpp9bitvector;definitions5bv_eqC56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith6BinInt1Z6shiftrC45stdpp9bitvector;definitions7bv_wrapC45stdpp9bitvector;definitionsCbv_wrap_bv_unsignedC56Stdlib6ZArith6BinInt1Z:shiftr_0_rC45stdpp9bitvector;definitionsCbv_extract_unsignedC4ELinuxProcessSemantics5Riscv3Sem5alu64K47Corelib4Init5Logic2eq01C49OSSVerify5KrLib8PropExec7alu_addC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6b_npc4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387CatExecCwrite_to_mem_wbytesC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec9le_word_vC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6ov_rdnC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8eqb_reflC4ELinuxProcessSemantics5Riscv3Sem9amo_bytesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5ms_pcC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C45stdpp9bitvector;definitions:bv_extractC4ELinuxProcessSemantics5Riscv3Sem7amo_valI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics5Riscv3Sem4core00K47Corelib7Numbers7BinNums1N01K4ELinuxProcessSemantics5Riscv5Instr5amoop02I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00I47Corelib7Numbers7BinNums1Z00K4ELinuxProcessSemantics5Riscv5Instr6awidth02K47Corelib7Numbers7BinNums1Z01K47Corelib4Init5Logic4True01K47Corelib4Init9Datatypes3nat01K47Corelib4Init9Datatypes4bool01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessI4ELinuxProcessSemantics5Riscv3Sem3eff00I47Corelib7Numbers7BinNums1N00I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums8positive00I47Corelib4Init5Logic3and00K4ELinuxProcessSemantics5Riscv5Instr5aluop01C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltC49OSSVerify5KrLib8PropExec4v_lwC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics5Riscv7Prelude4sextC56Stdlib6ZArith6BinInt1Z3addc59OSSVerify5KrLib7Mh_0035:ArtAtomics@art_mod32_helperC1?~~~~~~~~~~~~~~~C35stdpp7tactics<f_equal_helpC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z2leC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revC59OSSVerify5KrLib7Mh_00387SeqExecBZ_to_le_bytes_wrapC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega5Tauto8GFormula05C45stdpp9bitvector;definitions=bv_wrap_smallC45stdpp9bitvector;definitions@Z_to_bv_unsignedC45stdpp9bitvector;definitions?bv_add_unsignedC49OSSVerify5KrLib8PropExec8b_lw_valC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K4ELinuxProcessSemantics5Riscv5Instr6awidth01C46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205K4ELinuxProcessSemantics5Riscv5Instr5instr08c59OSSVerify5KrLib7Mh_0035:ArtAtomics5mkstrC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics5Riscv5Instr5aluop00C45stdpp9bitvector;definitions9bv_signedC49OSSVerify5KrLib8PropExec8alu_addiC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0035;ArtAtomics2@art_step_opimm_rC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Section FPX. Context {fx : PropExec.FPState}.

#[local] Ltac amo_unfold :=
  cbv beta iota zeta delta
    [RiscvSemantics.interp_eff_accesses RiscvSemantics.width_bytes RiscvSemantics.width_bytesZ negb Sem.is_x0
     Sem.rget Sem.rset Sem.with_regs Sem.with_pc Sem.with_resv Sem.inval_resv Sem.c_regs Sem.c_fregs Sem.c_pc Sem.c_fcsr Sem.c_resv
     ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom ms_fregs ms_fcsr mkstr mkst].

(* [comment removed for export] *)
Lemma art_step_amoadd_d_rd : forall segs regs pc mem rom w aq rl (rd rs1 rs2 : reg) (a v old : word) bs,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Amo AMO_ADD AD aq rl rd rs1 rs2, 4%Z) -> bv_eqb rd 0 = false ->
  getr regs rs1 = a -> (bv_unsigned a mod 8 = 0)%Z ->
  rdn segs mem a 8%nat = Some bs -> bytes_le_to_Z bs = bv_unsigned old ->
  getr regs rs2 = v ->
  RiscvSemantics.store_ok segs mem a 8%nat = true ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd old) (v_addi pc 4) (wbytes mem a (word_to_le_bytes 8 (v_add old v))) rom).
Proof.
  intros segs regs pc mem rom w aq rl rd rs1 rs2 a v old bs Hf He Hd Hrd Ha Hal Hread Hv Hrs2 Hok.
  step_pipeline Hf He Hd.
  unfold getr in Ha, Hrs2; rewrite ?bv_eqb0_is_x0 in Ha, Hrs2.
  rewrite Ha, Hrs2.
  unfold amo_aligned. cbn [amo_bytes]. rewrite Hal. rewrite Z.eqb_refl.
  amo_unfold.
  assert (Hz : bv_extract 0 64 old = old).
  { apply bv_eq. rewrite bv_extract_unsigned, Z.shiftr_0_r. apply bv_wrap_bv_unsigned. }
  rewrite ov_rdn, Hread; cbv beta iota.
  rewrite (le_word_v _ _ Hv), Hz.
  rewrite Hok; cbv beta iota.
  unfold bv_eqb in Hrd. change (bv_unsigned (0%bv : bv 5)) with 0%Z in Hrd. rewrite Hrd. cbv beta iota.
  rewrite ?write_to_mem_wbytes, ?b_npc4, <- alu_add.
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma art_step_amoadd_w_rd : forall segs regs pc mem rom w aq rl (rd rs1 rs2 : reg) (a v old : word) bs,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Amo AMO_ADD AW aq rl rd rs1 rs2, 4%Z) -> bv_eqb rd 0 = false ->
  getr regs rs1 = a -> (bv_unsigned a mod 4 = 0)%Z ->
  rdn segs mem a 4%nat = Some bs -> bytes_le_to_Z bs = bv_unsigned old -> (bv_unsigned old < 2 ^ 32)%Z ->
  getr regs rs2 = v ->
  RiscvSemantics.store_ok segs mem a 4%nat = true ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd (v_lw old)) (v_addi pc 4) (wbytes mem a (word_to_le_bytes 4 (v_add old v))) rom).
Proof.
  intros segs regs pc mem rom w aq rl rd rs1 rs2 a v old bs Hf He Hd Hrd Ha Hal Hread Hv Hold Hrs2 Hok.
  step_pipeline Hf He Hd.
  unfold getr in Ha, Hrs2; rewrite ?bv_eqb0_is_x0 in Ha, Hrs2. rewrite Ha, Hrs2.
  unfold amo_aligned. cbn [amo_bytes]. rewrite Hal, Z.eqb_refl. amo_unfold.
  rewrite ov_rdn, Hread; cbv beta iota.
  rewrite (le_word_v _ _ Hv).
  rewrite Hok; cbv beta iota.
  unfold bv_eqb in Hrd. change (bv_unsigned (0%bv : bv 5)) with 0%Z in Hrd. rewrite Hrd. cbv beta iota.
  rewrite ?write_to_mem_wbytes, ?b_npc4, b_lw_val.
  assert (Hb : Z_to_le_bytes 4 (bv_unsigned (amo_val AMO_ADD (bv_extract 0 32 old) (low32 v))) = word_to_le_bytes 4 (v_add old v)).
  { cbn [amo_val]. unfold low32, word_to_le_bytes, v_add.
    rewrite bv_add_unsigned, !bv_extract_unsigned, !Z.shiftr_0_r, Z_to_bv_unsigned.
    rewrite (bv_wrap_small 32 (bv_unsigned old)) by (pose proof (u64_range old); change (bv_modulus 32) with 4294967296%Z; lia).
    rewrite Z_to_le_bytes_wrap by (cbn; lia).
    rewrite <- (Z_to_le_bytes_wrap 4 32 (bv_wrap 64 _)) by (cbn; lia).
    rewrite <- (Z_to_le_bytes_wrap 4 32 (bv_unsigned old + bv_wrap 32 (bv_unsigned v))) by (cbn; lia).
    f_equal. unfold bv_wrap.
    change (bv_modulus 64) with (4294967296 * 4294967296)%Z. change (bv_modulus 32) with 4294967296%Z.
    apply art_mod32_helper. }
  rewrite Hb. reflexivity.
Qed.

(* [comment removed for export] *)
#[local] Ltac step_pipeline_r Hfetch Hecall Hdecode :=
  unfold RiscvSemantics.step, RiscvSemantics.step_accesses;
  cbn [ms_pc ms_pc_val mkstr];
  rewrite Hfetch; cbv beta iota;
  unfold RiscvSemantics.drop_access_report, RiscvSemantics.decode_exec_accesses;
  rewrite Hecall; cbv beta iota;
  rewrite Hdecode;
  cbv beta iota zeta delta
    [RiscvSemantics.interp_eff_accesses RiscvSemantics.width_bytes RiscvSemantics.width_bytesZ
     Sem.exec Sem.load_val Sem.store_val Sem.rget Sem.rset Sem.with_regs Sem.with_pc Sem.with_resv Sem.inval_resv Sem.w0 Sem.w1
     Sem.c_regs Sem.c_fregs Sem.c_pc Sem.c_fcsr Sem.c_resv ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom ms_fregs ms_fcsr mkstr];
  rewrite ?bv_eqb0_is_x0.

Lemma art_step_opimm_r : forall segs regs pc mem rom w op rd rs (imm : bv 12) r,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (OpImm op rd rs imm, 4%Z) ->
  RiscvSemantics.step segs (mkstr regs pc mem rom r) =
  MachineOk (mkstr (if bv_eqb rd 0 then regs else regupd regs rd (alu64 op (getr regs rs) (sext 64 imm))) (v_addi pc 4) mem rom r).
Proof.
  intros segs regs pc mem rom w op rd rs imm r Hf He Hd.
  step_pipeline_r Hf He Hd.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  destruct (is_x0 rs); destruct (is_x0 rd); cbv beta iota; rewrite ?b_npc4; reflexivity.
Qed.
Lemma art_step_addi_r : forall segs regs pc mem rom w rd rs (imm : bv 12) r,
  fetch_word segs pc = Some w -> is_ecall w = false -> decode_any w = Some (OpImm ALU_ADD rd rs imm, 4%Z) -> bv_eqb rd 0 = false ->
  RiscvSemantics.step segs (mkstr regs pc mem rom r) = MachineOk (mkstr (regupd regs rd (v_addi (getr regs rs) (bv_signed imm))) (v_addi pc 4) mem rom r).
Proof.
ltac2:(KReplay.run1 (kr_t_ArtAtomics2 ()) ["FPX"] "h01bh12Hdh22Heh32Hfh43Hrdh53immh61mh73memh82pch91rh:2rdh;4regsh<3romh=2rsh>4segsh?1wp;1p;2p;3p;4p;6p;>p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9g000NR1p4p7210R0g001:R2p4p710R3p8P0p1001Xp4p710p8p1002_p4p710P3p8p1003:p4p710p1003Yp4p710p8p10045p4p710P3p8g004Wj1OTg0057j10Tg005\j1=Tg006Aj15Tg006_j16TP1j2JTg007Bj17Tg007dj2GTg008fj2;Tg009Hj31Tg009bj1DTg00:bj2BTg00;Bj1ATg024Xj4NTg00<_j1MTg00==j4LTg00=]j3ITg00>@j3@Tg00D6j1HTg00>mj2>Tg01S^j3:Tg017`j3<Tg00ODj33Tg00P8j28Tg025Dj62Tg01ALj24Tg026mj2?Tg018Hj2FTg027Uj3ETP2j69Tg01?Ij2KTg028Kl>CTg01Fa#Og01G`R2#0R1#=#5R3%01R1#0R0#0#0R4#0#5R5#6R6'JR7%50#6#7\6R0%54#6R4%63R8%=2#0#0#5R2#6%76%74f9R9f7R:'Gf4R;,;431g01HER4f5R<#Dg01HeR=31g01IER>g01J1R?'BR@#7f6RA#AP>P?g01P_R?P<P;f3R>CN%M1R1CL,;@31g01K<g01KZ5I3R@9@3A=14=g01CgRB#HRCp,2fxRDP4P7A@3:@R@f<R31>3AREA:25<5<?RF933:n0100000020000f;RG/81RHf:RIP9P;E2,4Bf0RJPDf=RKf8RL1>K:RM1?2A'8331831R1PGPIP<E2,4BRN51CX6CP4P=PDP4P7PJPKA:25A9<?M93KLn0100000020000P1PGPIP<E2,4B=1CNX04P61?2<,8ER4PDA3KLJP1PGPIP<E2,4B=1CNX06PDA33:4PHPIP9P;E2,4B,FCPFAEE2<E9P@PJE9PDP3PGPIP9P;E2,KKPKP3PGPIP9PLP?P:PAP<P;P>f2f1M>CE9W4W1W2W3W9W5X=8W:W?X<0W7X86W;W>o"). Qed.
End FPX.

End ArtAtomics2.
Module ArtRuns.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Inductive aev : Type :=
| AMmapFixed (addr len : Z)      (* [comment removed for export] *)
| AMmapNull (len r : Z)          (* [comment removed for export] *)
| AMmapFixedNR (addr len : Z)    (* [comment removed for export] *)
| AMunmap (addr len : Z)         (* [comment removed for export] *)
| AMadvise (addr len : Z).       (* [comment removed for export] *)

(* [comment removed for export] *)
Definition art_zfill (M : word -> option byte) (r len : Z) : word -> option byte :=
  fun a => if (r <=? bv_unsigned a) && (bv_unsigned a <? r + len) then Some (Z_to_bv 8 0) else M a.
Definition art_unmap (M : word -> option byte) (r len : Z) : word -> option byte :=
  fun a => if (r <=? bv_unsigned a) && (bv_unsigned a <? r + len) then None else M a.

(* [comment removed for export] *)
Definition art_shlo (r : Z) : Z := (r / 8 + 0x7fff8000) / 4096 * 4096.
Definition art_shhi (r len : Z) : Z := ((r + len) / 8 + 0x7fff8000 + 4095) / 4096 * 4096.
Definition art_reveal (M : word -> option byte) (lo hi : Z) : word -> option byte :=
  fun a => if (lo <=? bv_unsigned a) && (bv_unsigned a <? hi) then (match M a with Some b => Some b | None => Some (Z_to_bv 8 0) end) else M a.

Lemma art_reveal_in : forall M lo hi a, lo <= bv_unsigned a < hi -> art_reveal M lo hi a = match M a with Some b => Some b | None => Some (Z_to_bv 8 0) end.
Proof. intros M lo hi a H. unfold art_reveal. replace ((lo <=? bv_unsigned a) && (bv_unsigned a <? hi)) with true; [reflexivity|]. symmetry. apply andb_true_intro. split; [apply Z.leb_le|apply Z.ltb_lt]; lia. Qed.
Lemma art_reveal_out : forall M lo hi a, ~ (lo <= bv_unsigned a < hi) -> art_reveal M lo hi a = M a.
Proof.
  intros M lo hi a H. unfold art_reveal. destruct (lo <=? bv_unsigned a) eqn:E1; [|reflexivity]. destruct (bv_unsigned a <? hi) eqn:E2; [|reflexivity].
  apply Z.leb_le in E1. apply Z.ltb_lt in E2. exfalso. apply H. lia.
Qed.
Lemma art_reveal_some : forall M lo hi a b, M a = Some b -> art_reveal M lo hi a = Some b.
Proof. intros M lo hi a b H. unfold art_reveal. rewrite H. destruct ((lo <=? bv_unsigned a) && (bv_unsigned a <? hi)); reflexivity. Qed.
Lemma art_reveal_defined : forall M lo hi a, lo <= bv_unsigned a < hi -> art_reveal M lo hi a <> None.
Proof. intros M lo hi a H. rewrite art_reveal_in by exact H. destruct (M a); discriminate. Qed.

Lemma art_zfill_in : forall M r len a, r <= bv_unsigned a < r + len -> art_zfill M r len a = Some (Z_to_bv 8 0).
Proof. intros M r len a H. unfold art_zfill. replace ((r <=? bv_unsigned a) && (bv_unsigned a <? r + len)) with true; [reflexivity|]. symmetry. apply andb_true_intro. split; [apply Z.leb_le|apply Z.ltb_lt]; lia. Qed.
Lemma art_zfill_out : forall M r len a, ~ (r <= bv_unsigned a < r + len) -> art_zfill M r len a = M a.
Proof.
  intros M r len a H. unfold art_zfill. destruct (r <=? bv_unsigned a) eqn:E1; [|reflexivity]. destruct (bv_unsigned a <? r + len) eqn:E2; [|reflexivity].
  apply Z.leb_le in E1. apply Z.ltb_lt in E2. exfalso. apply H. lia.
Qed.
Lemma art_unmap_in : forall M r len a, r <= bv_unsigned a < r + len -> art_unmap M r len a = None.
Proof. intros M r len a H. unfold art_unmap. replace ((r <=? bv_unsigned a) && (bv_unsigned a <? r + len)) with true; [reflexivity|]. symmetry. apply andb_true_intro. split; [apply Z.leb_le|apply Z.ltb_lt]; lia. Qed.
Lemma art_unmap_out : forall M r len a, ~ (r <= bv_unsigned a < r + len) -> art_unmap M r len a = M a.
Proof.
  intros M r len a H. unfold art_unmap. destruct (r <=? bv_unsigned a) eqn:E1; [|reflexivity]. destruct (bv_unsigned a <? r + len) eqn:E2; [|reflexivity].
  apply Z.leb_le in E1. apply Z.ltb_lt in E2. exfalso. apply H. lia.
Qed.

Section Runs.
Variable segs : list Segment.
Variable EVOK : list aev -> aev -> Prop.
Variable GR : list aev -> (word -> option byte) -> Z -> Z -> Prop.
Context {fx : PropExec.FPState}.

Definition art_at_ecall (pc : word) : Prop := exists w, fetch_word segs pc = Some w /\ is_ecall w = true.

(* [comment removed for export] *)
Definition art_mmap_args (regs : bvmap 5 word) (addr len flags : Z) : Prop :=
  getr regs 17 = Z_to_bv 64 222 /\ getr regs 10 = Z_to_bv 64 addr /\ getr regs 11 = Z_to_bv 64 len /\ getr regs 12 = Z_to_bv 64 3
  /\ getr regs 13 = Z_to_bv 64 flags /\ getr regs 14 = Z_to_bv 64 (2 ^ 64 - 1) /\ getr regs 15 = Z_to_bv 64 0.
Definition art_munmap_args (regs : bvmap 5 word) (addr len : Z) : Prop :=
  getr regs 17 = Z_to_bv 64 215 /\ getr regs 10 = Z_to_bv 64 addr /\ getr regs 11 = Z_to_bv 64 len.
Definition art_madvise_args (regs : bvmap 5 word) (addr len : Z) : Prop :=
  getr regs 17 = Z_to_bv 64 233 /\ getr regs 10 = Z_to_bv 64 addr /\ getr regs 11 = Z_to_bv 64 len /\ getr regs 12 = Z_to_bv 64 4.

Inductive aruns (Q : list aev -> machine_state -> Prop) : list aev -> machine_state -> Prop :=
| ar_done : forall log s, Q log s -> aruns Q log s
| ar_steps : forall log s s', msteps segs s s' -> aruns Q log s' -> aruns Q log s
| ar_mmap_fixed : forall log regs (pc pc' : word) M rom addr len,
    art_at_ecall pc -> pc' = Z_to_bv 64 (bv_unsigned pc + 4) -> art_mmap_args regs addr len 50 -> EVOK log (AMmapFixed addr len) ->
    aruns Q (log ++ [AMmapFixed addr len]) (mkst (regupd regs 10 (Z_to_bv 64 addr)) pc' (art_zfill M addr len) rom) ->
    aruns Q log (mkst regs pc M rom)
| ar_mmap_null : forall log regs (pc pc' : word) M rom len,
    art_at_ecall pc -> pc' = Z_to_bv 64 (bv_unsigned pc + 4) -> art_mmap_args regs 0 len 34 -> EVOK log (AMmapNull len 0) ->
    (forall r, GR log M len r ->
       aruns Q (log ++ [AMmapNull len r]) (mkst (regupd regs 10 (Z_to_bv 64 r)) pc' (art_reveal (art_zfill M r len) (art_shlo r) (art_shhi r len)) rom)) ->
    aruns Q log (mkst regs pc M rom)
| ar_mmap_fixed_nr : forall log regs (pc pc' : word) M rom addr len,
    art_at_ecall pc -> pc' = Z_to_bv 64 (bv_unsigned pc + 4) -> art_mmap_args regs addr len 16434 -> EVOK log (AMmapFixedNR addr len) ->
    aruns Q (log ++ [AMmapFixedNR addr len]) (mkst (regupd regs 10 (Z_to_bv 64 addr)) pc' (art_zfill M addr len) rom) ->
    aruns Q log (mkst regs pc M rom)
| ar_munmap : forall log regs (pc pc' : word) M rom addr len,
    art_at_ecall pc -> pc' = Z_to_bv 64 (bv_unsigned pc + 4) -> art_munmap_args regs addr len -> EVOK log (AMunmap addr len) ->
    aruns Q (log ++ [AMunmap addr len]) (mkst (regupd regs 10 (Z_to_bv 64 0)) pc' (art_unmap M addr len) rom) ->
    aruns Q log (mkst regs pc M rom)
| ar_madvise : forall log regs (pc pc' : word) M rom addr len,
    art_at_ecall pc -> pc' = Z_to_bv 64 (bv_unsigned pc + 4) -> art_madvise_args regs addr len -> EVOK log (AMadvise addr len) ->
    aruns Q (log ++ [AMadvise addr len]) (mkst (regupd regs 10 (Z_to_bv 64 0)) pc' (art_zfill M addr len) rom) ->
    aruns Q log (mkst regs pc M rom).

Lemma aruns_mono : forall (Q Q' : list aev -> machine_state -> Prop) log s,
  aruns Q log s -> (forall log' s', Q log' s' -> Q' log' s') -> aruns Q' log s.
Proof.
  intros Q Q' log s H HQ. induction H.
  - apply ar_done. apply HQ. assumption.
  - eapply ar_steps; eassumption.
  - eapply ar_mmap_fixed; eassumption.
  - eapply ar_mmap_null; eassumption.
  - eapply ar_mmap_fixed_nr; eassumption.
  - eapply ar_munmap; eassumption.
  - eapply ar_madvise; eassumption.
Qed.

(* [comment removed for export] *)
Lemma aruns_bind : forall (Q1 Q2 : list aev -> machine_state -> Prop) log s,
  aruns Q1 log s -> (forall log' s', Q1 log' s' -> aruns Q2 log' s') -> aruns Q2 log s.
Proof.
  intros Q1 Q2 log s H HQ. induction H.
  - apply HQ. assumption.
  - eapply ar_steps; eassumption.
  - eapply ar_mmap_fixed; eassumption.
  - eapply ar_mmap_null; eassumption.
  - eapply ar_mmap_fixed_nr; eassumption.
  - eapply ar_munmap; eassumption.
  - eapply ar_madvise; eassumption.
Qed.

Lemma aruns_msteps_done : forall (Q : list aev -> machine_state -> Prop) log s s', msteps segs s s' -> Q log s' -> aruns Q log s.
Proof. intros Q log s s' H HQ. eapply ar_steps; [exact H|]. apply ar_done. exact HQ. Qed.

(* [comment removed for export] *)
Lemma aruns_of_msteps : forall (Q : list aev -> machine_state -> Prop) log s s',
  msteps segs s s' -> aruns Q log s' -> aruns Q log s.
Proof. intros. eapply ar_steps; eassumption. Qed.

End Runs.
Arguments aruns segs EVOK GR {fx} Q log s.

End ArtRuns.
From LinuxProcessSemantics.Riscv Require Prelude Instr. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056.
Module ArtMem.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StepTac OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.WalkTac OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056.MemSplit.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_ArtMem () := "C47Corelib7Program6Basics4flipC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00C46Stdlib5Lists4List6nth_okC46Stdlib5Lists4List:firstn_nilC47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List=repeat_lengthK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1N02C45stdpp9bitvector;definitions7bv_wrapI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC45stdpp9bitvector;definitions=bv_wrap_smallC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions@Z_to_bv_unsignedC56Stdlib6ZArith6BinInt1Z2leK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C56Stdlib6ZArith6BinInt1Z6moduloI45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions5bv_eqI47Corelib7Numbers7BinNums1N00C56Stdlib6ZArith6BinInt1Z3addC46Stdlib6ZArith4ZdivAZplus_mod_idemp_lc59OSSVerify5KrLib7Mh_00356ArtMem9art_zb_eqC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6v_addiC1?~~~~~~~~~~~~~~~C46Stdlib6ZArith4Zdiv9Zplus_modC49OSSVerify5KrLib8PropExec5v_addC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC46Stdlib6ZArith4Zdiv:Zminus_modC49OSSVerify5KrLib8PropExec5v_subC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC46Stdlib6ZArith4Zdiv9Zmult_modC49OSSVerify5KrLib8PropExec5v_mulC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6shiftlC46Stdlib6ZArith4ZdivAZmult_mod_idemp_lC56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C49OSSVerify5KrLib8PropExec6v_slliC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2c59OSSVerify5KrLib7Mh_00356ArtMem9art_u_litC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6v_srliC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z7div_mulC35stdpp7tactics<f_equal_helpK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula01K46Stdlib9micromega7EnvRing5PExpr05c59OSSVerify5KrLib7Mh_00356ArtMem;art_zb_srliC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic5False00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C56Stdlib6ZArith6BinInt1Z4landC49OSSVerify5KrLib8PropExec5v_andC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6v_andiC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C45stdpp9bitvector;definitions8bv_swrapK46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z9mod_smallC49OSSVerify5KrLib8PropExec4v_lwC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4v_lhC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=bytes_le_to_ZC49OSSVerify5KrLib8PropExec:bytes_le_NC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z7testbitC47Corelib4Init9Datatypes4andbC56Stdlib6ZArith6BinInt1Z;lt_ge_casesI47Corelib4Init5Logic2or00C46Stdlib4Bool4Bool<andb_false_rC56Stdlib6ZArith6BinInt1Z?shiftl_spec_lowC56Stdlib6ZArith6BinInt1Z3ltbC46Stdlib4Bool4Bool=andb_true_iffC56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z6leb_leC56Stdlib6ZArith6BinInt1Z6ltb_ltK47Corelib4Init5Logic3and01C47Corelib4Init5Logic6eq_symC46Stdlib4Bool4Bool;andb_true_rC56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z;testbit_0_lC56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z<log2_lt_pow2C56Stdlib6ZArith6BinInt1Z;lt_le_transC56Stdlib6ZArith6BinInt1Z?bits_above_log2C56Stdlib6ZArith6BinInt1Z<testbit_onesC56Stdlib6ZArith6BinInt1Z;shiftr_specC56Stdlib6ZArith6BinInt1Z@shiftl_spec_highC56Stdlib6ZArith6BinInt1Z9land_specC56Stdlib6ZArith6BinInt1Z9bits_inj'K47Corelib4Init9Datatypes4bool02C45stdpp9bitvector;definitions9bv_signedC45stdpp9bitvector;definitions>Z_to_bv_signedC49OSSVerify5KrLib8PropExec4v_lbC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC56Stdlib6ZArith6BinInt1Z9land_onesC56Stdlib6ZArith6BinInt1Z9land_commc59OSSVerify5KrLib7Mh_00356ArtMem?art_land_full_lC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC49OSSVerify5KrLib8PropExec4c_eqC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec5c_ltuC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03C56Stdlib6ZArith6BinInt1Z4lxorC56Stdlib6ZArith6BinInt1Z5ldiffC56Stdlib6ZArith6BinInt1Z4lnotC56Stdlib6ZArith6BinInt1Z4predC56Stdlib6ZArith6BinInt1Z:ones_equivC56Stdlib6ZArith8Zbitwise1Z?sub_land_same_lC56Stdlib6ZArith6BinInt1Z:ldiff_landC56Stdlib6ZArith6BinInt1Z@ldiff_ones_l_lowC49OSSVerify5KrLib8PropExec6v_xoriC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7v_sltiuC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00356ArtMem<art_c_ltu_zbC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6v_sltuC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00356ArtMem5apartC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula06I47Corelib4Init9Datatypes6option00C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC47Corelib4Init9Datatypes6lengthC59OSSVerify5KrLib7Mh_00387CatExecDlength_N_to_le_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387CatExec>rdn_wbytes_outC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00356ArtMem2WnC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00c59OSSVerify5KrLib7Mh_00356ArtMem4cellC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01c59OSSVerify5KrLib7Mh_00356ArtMem<rdn_Wn_otherC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387SeqExec>rdn_wbytes_hitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387CatExec6wbytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk<wbytes_growsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00356ArtMem3wokC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00356ArtMem8Wn_growsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk=store_ok_monoC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00356ArtMem2wrC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okc59OSSVerify5KrLib7Mh_00356ArtMem8wr_growsC1?~~~~~~~~~~~~~~~C46Stdlib6ZArith:ZArith_dec;Z_lt_le_decC59OSSVerify5KrLib7Mh_00387CatExec<wbytes_belowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387CatExec<wbytes_aboveC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6repeatc59OSSVerify5KrLib7Mh_00356ArtMem2WfC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00356ArtMem8Wf_growsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00356ArtMem9wok_growsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00356ArtMem<rdn_Wf_otherC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List=nth_repeat_ltC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib5Lists7ListDef3nthC47Corelib4Init5Peano2ltC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specC46Stdlib9micromega;ZifyClasses;rew_iff_revC59OSSVerify5KrLib7Mh_00568MemSplit=wbytes_insideC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula03C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_ltC59OSSVerify5KrLib7Mh_00387SeqExec?bytes_le_to_Z_8C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00356ArtMem:art_bytes1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00356ArtMem:art_bytes4C1?~~~~~~~~~~~~~~~".
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma art_u_lit : forall a, 0 <= a < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 a) = a.
Proof.
ltac2:(KReplay.run1 (kr_t_ArtMem ()) [] "h01Hh12Hah24__x1h32H0h47__arithh54__ffh66__sat0h76__sat1h88__varmaph95__with:1ah;1zp;1p;2p;3p;4p;7p;6p;8p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9p1000Np4p7210R1g001:R0p4p710R2p8P1p1001Xp4p710p8p1002_p4p710P2p8p1003:p4p710p1003Yp4p710p8p10045p4p710P2p8g004Wj12Tg005<j15Tg005Zj2=Tg0067j21Tg006SR2j23Tg006nj1CTg007Lj2ATg0082j39Tg008Lj2>Tg0094j3<Tg009Xj1;Tg00:8j1:Tg00:Xj2TTg00;6j1STg00;Tj1RTg00<?j2FTg00<bj27Tg00=Ej3ETg00=hj46Tg00>Sj1BTg00?5j7@Tg00?Yj2DTg00@;j2?Tg00@Uj2GTg00AAj3HTg00A`j4ITg00BRj3JTg00C>j2KTg00Cdj2LTg00DNj2MTP0j6NTg00E=j2OTg00EYj7PTg00F=j8QTg00FaR0f0R1'Op=0f1R3g00G?R4g00G^R5P5g00H>R6P1g00H^FPp=8f3R7P4P5P5P6f2R8P3P1GQp=4g00I>R9%01g00I\R:#2R;#5R<%2;#2#2#2#2R;#5R='=R>,11R?'3P9%C;R;/A3A9918X;91><=110<%0=110>[[%0<R@g00JARAA<<=3UW1%0>\A^1@P2%07117>f4R7#0117>'3P8f5#0f6/1>g00J]R7#;%:71T93%S9%R9R7P91F9:R:g00KI179<=E9;C6,87R<%B5R2P7P91790g00L0P:C6,87R:P2P7P4P5P5P6P:P<F@C4C41D76P1P8g00LWR7g00M7R6'?1G18=976dAH903CIb5b8b9X29%03%08118>'3[\?^29P1f8P3P8O3b4W3W0P3P1O2n2001000000121000000b6b79J;31K;3,L;1M;3ENW0W:o"). Qed.

Lemma art_zb_eq : forall x y, x mod 2 ^ 64 = y mod 2 ^ 64 -> Z_to_bv 64 x = Z_to_bv 64 y.
Proof.
ltac2:(KReplay.run1 (kr_t_ArtMem ()) [] "h02b1h12b2h21nh31zh41Hh52H0h61xh71yp;1p;2p;3p;6p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9p1000Np4p7210R1g001:R0p4p710R2p8P1p1001Xp4p710p8p1002_p4p710P2p8p1003:p4p710p1003Yp4p710p8p10045p4p710P2p8g004Wj11Tg005<j1:Tg005Zj2=Tg00MWj26Tg00N7j13Tg0082j34Tg00Cdj20Tg00NZj3<Tg006nj1;Tg00C>j28Tg007Lj25Tg00DNj27TP0j69Tg00I>R0f1R2f0R134p=2g00I\#1R3#:%13#1#1#1#1R3#:'=R4,621614'2g00O>R4%31R5%32R6g006Sf2R7#3?421f3R8/071082'2R9[10721071'2%38?472[R:f4R;#3?487\9A<721P1n2001000000120000000W1W0W2P:^16^05^24P1%;3R31838R41837R5P01538R61034R4,21X30P01537R:153;/21X30P2126:e10351737E9P41738E9O4b5W4X70X60o"). Qed.

Lemma art_zb_addi : forall x k, v_addi (Z_to_bv 64 x) k = Z_to_bv 64 (x + k).
Proof.
  intros x k. unfold v_addi. rewrite Z_to_bv_unsigned. apply art_zb_eq. unfold bv_wrap. change (bv_modulus 64) with (2^64).
  rewrite Zplus_mod_idemp_l. reflexivity.
Qed.
Lemma art_zb_add : forall x y, v_add (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (x + y).
Proof.
  intros x y. unfold v_add. rewrite !Z_to_bv_unsigned. apply art_zb_eq. unfold bv_wrap. change (bv_modulus 64) with (2^64).
  rewrite <- Zplus_mod. reflexivity.
Qed.
Lemma art_zb_sub : forall x y, v_sub (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (x - y).
Proof.
  intros x y. unfold v_sub. rewrite !Z_to_bv_unsigned. apply art_zb_eq. unfold bv_wrap. change (bv_modulus 64) with (2^64).
  rewrite <- Zminus_mod. reflexivity.
Qed.
Lemma art_zb_mul : forall x y, v_mul (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (x * y).
Proof.
  intros x y. unfold v_mul. rewrite !Z_to_bv_unsigned. apply art_zb_eq. unfold bv_wrap. change (bv_modulus 64) with (2^64).
  rewrite <- Zmult_mod. reflexivity.
Qed.
Lemma art_zb_slli : forall x k, 0 <= k -> v_slli (Z_to_bv 64 x) k = Z_to_bv 64 (x * 2 ^ k).
Proof.
  intros x k Hk. unfold v_slli. rewrite Z_to_bv_unsigned, Z.shiftl_mul_pow2 by lia. apply art_zb_eq. unfold bv_wrap.
  change (bv_modulus 64) with (2^64). rewrite Zmult_mod_idemp_l. reflexivity.
Qed.
Lemma art_zb_srli : forall x k, 0 <= x < 2 ^ 64 -> 0 <= k -> v_srli (Z_to_bv 64 x) k = Z_to_bv 64 (x / 2 ^ k).
Proof.
ltac2:(KReplay.run1 (kr_t_ArtMem ()) [] "h04__x1h11Hh22H0h32Hah47__arithh54__ffh66__sat0h76__sat1h88__varmaph95__with:1zh;2Hkh<2Hxh=1kh>1xp;1p;2p;3p;4p;6p;7p;8p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9p1000Np4p7210R1g001:R0p4p710R2p8P1p1001Xp4p710p8p1002_p4p710P2p8p1003:p4p710p1003Yp4p710p8p10045p4p710P2p8g004Wj12Tg005<j1:Tg005Zj25Tg0067j21Tg006SR2j26Tg006nj1MTg00N7j1GTg00Yfj29Tg00C>j23Tg00ZFj2>Tg0082j34Tg00@;j2?Tg008Lj2WTg0094j3VTg009Xj1UTg00:8j1RTg00:Xj2QTg00;6j1NTg00;Tj1LTg00<bj28Tg00<?j2KTg00=hj4<Tg00>Sj1FTg00?Yj2ETg00@Uj2HTg00AAj3DTg00A`j4ITg00Zcj3JTP0j6=Tg00Cdj2CTg00=Ej3BTg00?5j7ATg00[Lj2OTg00\Ij2PTg00E=j2@Tg00EYj7STg00F=j8TTg00FaR0f0R1'@p=0f1R3g00G?R4g00G^R5P5g00H>R6P1g00H^FSp=;f3R7P4P5P5P6f2R8P3P1GTp=7g00I>R9%03R:g00I\R;#2R<#:R=%2<#2#2#2#2R<#:R>'5R?,13'6P9P7%M<R<#GR@1917,3<f415=7'>,3<RA34X:9P915=8,>7RB13<1=4@AX:913<BRB,?@19781W=>RA110=%0>110?[[RC%0=RDg00JAREAV=>3UW3R>%0?\E^3DRDP2f5RE#0RF11E?REPFP7f7RG#0RHf8/1?RIg00J]RJ#URK%RJRJ1Q93RL%N9RM%L9RNP91890g00L01K9;R;C<,;NRO%F5RPPOC71EN6RQP1P8g00LWRRg00M7RS'?1H18=4RSdAD903CIR0b5b8b9X09%01P:[^09P1f9PGO2b4W2W1P3P1O2n2001000000120000000b6b79J78E=13<7RG,C<PAPCP>PDP2PFPEf6RE#011E?'6P7PKPJPLPMPNP9P;g00KI189==B9<C<,;NR<PPPNPOPPPNP4P5P5P6POP<FAC7C7PQP0b5b8b9X09111?%08118?'6\:[^09P1f:P3P8O3b4X2IX1HP3P1O2n2001000000121000000b6b7,O7E=1PG8=4@BeX;:W<X=9W>o"). Qed.
Lemma art_zb_srli_exact : forall x k y, 0 <= k -> 0 <= y -> x = y * 2 ^ k -> y < 2 ^ 64 -> y * 2 ^ k < 2 ^ 64 ->
  v_srli (Z_to_bv 64 x) k = Z_to_bv 64 y.
Proof.
  intros x k y Hk Hy Hx Hy' Hyk. subst x. rewrite art_zb_srli by lia. f_equal. apply Z.div_mul. pose proof (Z.pow_pos_nonneg 2 k). lia.
Qed.
Lemma art_zb_and : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> v_and (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (Z.land x y).
Proof.
ltac2:(KReplay.run1 (kr_t_ArtMem ()) [] "h01Hh12H0h22H1h32H2h42Hah57__arithh66__sat0h76__sat1h84__x1h91zh:2Hxh;2Hyh<4__ffh=8__varmaph>5__with?1xh@1yp;1p;2p;3p;4p;7p;6p;8p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9p1000Np4p7210R1g001:R0p4p710R2p8P1p1001Xp4p710p8p1002_p4p710P2p8p1003:p4p710p1003Yp4p710p8p10045p4p710P2p8g004Wj14Tg005<j1<Tg005Zj2CTg0067j20Tg006SR2j22Tg006nj1MTg00N7j1GTg00C>j23Tg00Cdj2=Tg00gVj26Tg0082j35Tg00@;j2?Tg008Lj2UTg0094j3TTg009Xj1STg00:8j1RTg00:Xj2QTg00;6j1NTg00;Tj1LTg00<?j2KTg00<bj2;Tg00=Ej3FTg00=hj4:Tg00>Sj1ETg00?5j7HTg00?Yj2DTg00@Uj2ITg00AAj3JTg00A`j4BTg00[Lj29TP0j6>Tg00h4j2ATg00E=j2OTg00EYj7PTg00F=j8@Tg00FaR0f0R1'Op=1f1R3g00G?R4g00G^R5P5g00H>R6P1g00H^FPp=8f3R7P4P5P5P6f2R8P3P1G@p=7g00I>R9%13R:g00I\R;#4R<#<R=%4<#4#4#4#4R<#<R>'CR?,03'2R@P9P7%M<R<#GRA13<7RB,=<RC,61,3<f4RD/67,3<RE35X99P9P816D1,3<=5AEX991678,3<RE,?A13<8RF,=<1U=>RG100=%1>100?[[RH%1=RIg00JARJAT=>3UW4R>%1?\J^4IRIP2%1DRJ10D?RDf5RK#110K?'2P8f6RL#1RMf7RN/0?ROP2f9RP#1RQ10P?RP12QPPNf;#1RRf</0?RSg00J]RT#S%RT1Q93%N9%L9RTP91K9;R;g00KI1;9==F9<C:,8TR<%E5R=PTP91;90g00L0P;C:,8TR;P=PTP4P5P5P6P;P<FHC7C71DT6P1P8g00LWRTg00M7R6'?1I18=5T6dAJ903CBb<b=b>X89R0101?%18108?'2\:[^89R:P1f=PKPLO3b5W3W2P3P1O2n2001000000121000000W1W0P3P1O2n2001000000121000000b6b7,98E>PCPGPHP>PIP2PJPD10L?,2MP8P2PQPPf:RP#110P?'2PNP0P:P1f>P3P8O3b5X3SX2RP3P1O2n2001000000121000000X1OX0MP3P1O2n2001000000121000000b6b7,97E>1ABF=5AEeX;@W:X@9W?o"). Qed.
Lemma art_zb_andi : forall x k, 0 <= x < 2 ^ 64 -> 0 <= k < 2 ^ 64 -> v_andi (Z_to_bv 64 x) k = Z_to_bv 64 (Z.land x k).
Proof.
ltac2:(KReplay.run1 (kr_t_ArtMem ()) [] "h01Hh12H0h22H1h32H2h42Hah57__arithh66__sat0h76__sat1h84__x1h91zh:2Hkh;2Hxh<4__ffh=8__varmaph>5__with?1kh@1xp;1p;2p;3p;4p;7p;6p;8p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9p1000Np4p7210R1g001:R0p4p710R2p8P1p1001Xp4p710p8p1002_p4p710P2p8p1003:p4p710p1003Yp4p710p8p10045p4p710P2p8g004Wj13Tg005<j1:Tg005Zj2BTg0067j20Tg006SR2j22Tg006nj1LTg00N7j1FTg007Lj29Tg00gVj25Tg00C>j24Tg0082j36Tg00@;j2>Tg008Lj2WTg0094j3VTg009Xj1UTg00:8j1RTg00:Xj2QTg00;6j1NTg00;Tj1KTg00<?j2HTg00<bj27Tg00=Ej3ETg00=hj48Tg00>Sj1DTg00?5j7GTg00?Yj2CTg00@Uj2ITg00AAj3JTg00A`j4ATg00BRj3MTP0j6<Tg00Cdj2@Tg00[Lj2OTg00hgj2PTg00E=j2?Tg00EYj7STg00F=j8TTg00FaR0f0R1'?p=1f1R3g00G?R4g00G^R5P5g00H>R6P1g00H^FSp==f3R7P4P5P5P6f2R8P3P1GTp=;g00I>R9%13R:g00I\R;#3R<#:R=%3<#3#3#3#3R<#:R>'BR?,03'2R@P9P7%L<R<#FRA19<7,51,4<f4RB/57,4<RC36X99P9P815B1,4<=6ACX991578,4<RC,>A19<81W=>RD100=%1>100?[[RE%1=RFg00JARGAV=>3UW4R>%1?\G^4FRFP2%1BRG10B?RBf5RH#110H?'2P8f6RI#1RJf7RK/0?RLP2f9RM#1RN10M?RM12NMPKf;#1ROf</0?RPg00J]RQ#U%RQ1Q93%N9%K9RQP91H9;R;g00KI179==E9<C8,=QR=%D5RRPQP91790g00L0P;C8,=QR;PRPQP4P5P5P6P;P=FGC;C;1CQ6P1P8g00LWRQg00M7R6'>1I18=6Q6dAJ903CAb<b=b>X89R0101?%18108?'2\:[^89R:P1f=PHPIO3b5W3W2P3P1O2n2001000000121000000W1W0P3P1O2n2001000000121000000b6b79M<8E<14<7RH,@<PDPEP>PFP2PGPB10I?,2JP8P2PNPMf:RM#110M?'2PKP0P:P1f>P3P8O3b5X3PX2OP3P1O2n2001000000121000000X1LX0JP3P1O2n2001000000121000000b6b7,O7E<1PH8=6ACeX:@W;X?9W@o"). Qed.

Lemma art_v_lw_small : forall z, 0 <= z < 2 ^ 31 -> v_lw (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold v_lw. rewrite art_u_lit by lia. f_equal. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32). rewrite Z.mod_small by lia. lia.
Qed.

Lemma art_v_lh_small : forall z, 0 <= z < 2 ^ 15 -> v_lh (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold v_lh. rewrite art_u_lit by lia. f_equal. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 16) with (2^15). change (bv_modulus 16) with (2^16). rewrite Z.mod_small by lia. lia.
Qed.
Lemma art_bytes2 : forall z, 0 <= z < 2 ^ 16 -> bytes_le_to_Z (word_to_le_bytes 2 (Z_to_bv 64 z)) = bv_unsigned (Z_to_bv 64 z).
Proof.
  intros z Hz. rewrite bytes_le_N. change (2 ^ (8 * Z.of_nat 2)) with (2^16). rewrite art_u_lit by lia. apply Z.mod_small. lia.
Qed.
Lemma art_land_m8 : forall x, 0 <= x < 2 ^ 64 -> Z.land x 18446744073709551608 = x / 8 * 8.
Proof.
  intros x Hx. change 18446744073709551608 with (Z.shiftl (Z.ones 61) 3).
  change 8 with (2 ^ 3). rewrite <- Z.shiftr_div_pow2, <- Z.shiftl_mul_pow2 by lia.
  apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
  destruct (Z.lt_ge_cases i 3) as [L|G].
  - rewrite !Z.shiftl_spec_low by lia. apply Bool.andb_false_r.
  - rewrite !Z.shiftl_spec_high by lia. rewrite Z.shiftr_spec by lia. rewrite Z.testbit_ones by lia.
    replace (i - 3 + 3) with i by lia.
    destruct (Z.lt_ge_cases i 64) as [L2|G2].
    + replace ((0 <=? i - 3) && (i - 3 <? 61))%bool with true by (symmetry; apply Bool.andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
      apply Bool.andb_true_r.
    + assert (Tf : Z.testbit x i = false).
      { destruct (Z.eq_dec x 0) as [->|NZ]. apply Z.testbit_0_l. apply Z.bits_above_log2; [lia|]. 
        apply Z.lt_le_trans with (m := 64); [|lia]. apply Z.log2_lt_pow2; lia. }
      rewrite Tf. reflexivity.
Qed.
Lemma art_v_lb_small : forall z, 0 <= z < 128 -> v_lb (Z_to_bv 8 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold v_lb. f_equal. rewrite Z_to_bv_signed. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 8) with 128. change (bv_modulus 8) with 256. rewrite Z.mod_small by lia. lia.
Qed.
Lemma art_bytes1 : forall z, 0 <= z < 2 ^ 64 -> word_to_le_bytes 1 (Z_to_bv 64 z) = [Z_to_bv 8 z].
Proof.
  intros z Hz. unfold word_to_le_bytes. cbn. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 8) with 256. change (bv_modulus 64) with (2^64). rewrite (Z.mod_small z (2^64)) by lia. reflexivity.
Qed.
Lemma art_u8_lit : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
Proof.
ltac2:(KReplay.run1 (kr_t_ArtMem ()) [] "h04__x1h11zh21Hh32H0h42Hzh57__arithh64__ffh78__varmaph85__witp;2p;1p;3p;4p;7p;6p;8p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9p1000Np4p7210R1g001:R0p4p710R2p8P1p1001Xp4p710p8p1002_p4p710P2p8p1003:p4p710p1003Yp4p710p8p10045p4p710P2p8g00E=j21Tg004Wj10Tg005<j1@Tg0067j22Tg006SR2j28Tg006nj1NTg007Lj2CTg0082j33Tg009Xj1>Tg00:8j1=Tg00:Xj2<Tg00;6j1:Tg00;Tj19Tg00<?j2OTg00<bj27Tg00=hj46Tg00>Sj1MTg00?5j7LTg00?Yj2BTg00@;j2ATg00@Uj2?Tg00AAj3DTg00A`j4ETg00BRj3FTg00C>j2GTg00Cdj2HTg00DNj2ITP0j6JTg00EYj7KTg00F=j8;Tf1R0g00G?R1g00G^R3P3g00H>R4f0R5g00H^FKp=5f3R6P1P3P3P4f2R7P0P5G;p=4g00I>R8g00FaR9/15g00I\R:#0#0#0R;#0#0#0#0#0#@R<,25R='8P8%N;R;/C0A3857X18P21190R2120<1197127<'8R>P51196f4/2<g00J]R6#>%=61<80%:8%98R6P81O8:R:g00KI178<C6,56R<%M3R?P6P81789g00L0P:C6,56R:P?P6P1P3P3P4P:P<FLC4C41B64P5P7g00LWR6g00M7R4'A1?57=364dAD890CEb6b7b8X08P>\2\=^08P5f6P0P7O3b5W3W2P0P5O2n20010000001200000009F;01G;0,H;1I;0EJW4W1o"). Qed.
Lemma art_bytes4 : forall z, 0 <= z < 2 ^ 32 -> bytes_le_to_Z (word_to_le_bytes 4 (Z_to_bv 64 z)) = bv_unsigned (Z_to_bv 64 z).
Proof.
  intros z Hz. rewrite bytes_le_N. change (2 ^ (8 * Z.of_nat 4)) with (2^32). rewrite art_u_lit by lia. apply Z.mod_small. lia.
Qed.


Lemma art_land_full_l : forall x, 0 <= x < 2 ^ 64 -> Z.land 18446744073709551615 x = x.
Proof.
ltac2:(KReplay.run1 (kr_t_ArtMem ()) [] "h01Hh12H0h22Hah37__arithh44__ffh56__sat0h66__sat1h78__varmaph85__with94__x1h:2Hxh;1xh<1zp;1p;2p;3p;4p;7p;6p;8p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9p1000Np4p7210R1g001:R0p4p710R2p8P1p1001Xp4p710p8p1002_p4p710P2p8p1003:p4p710p1003Yp4p710p8p10045p4p710P2p8g004Wj14Tg005<j18Tg005Zj2ATg0067j22Tg006SR2j29Tg00i[j10Tg00gVj25Tg0082j3<Tg00MWj2>Tg008Lj2ZTg0094j3VTg009Xj1UTg00:8j1STg00:Xj2RTg00;6j1NTg00;Tj1JTg00<?j2ITg00<bj27Tg006nj1ETg00=Ej3DTg00=hj4:Tg00>Sj1GTg00?5j7HTg00?Yj2BTg00@;j2KTg00@Uj2@Tg00AAj3LTg00A`j4MTg00kmj3?Tg011Qj1OTg00bEj1PTg01CVj3QTP0j6=Tg01D9j2TTg00E=j2YTg00EYj7XTg00F=j8WTg00FaR0f0R1'Yp=1%01#0p=F%01#0#0#0p=C%01#0#0#0#0#0#0#0p=3f1R3g00G?R4g00G^R5P5g00H>R6P1g00H^FXp=6f3R7P4P5P5P6f2R8P3P1GWp=;g00I>R9%11g00I\R:#4R;#8R<%4;#4#4#4#4R;#8R='AR>,21R?'9P9%0:#F#C#3#3#3#3#3#3#3#8R@,53A<918X<9RAP91>3>PA1Z<=RA120<%1=RB120>[[RC%1<RDg00JAREAV<=3UW2RF%1>\E^2DRDP2%17RE127>R7f4RG#112G>'9P8f5#1RGf6/2>RHg00J]RI#URJ%SIRI1R93%N9RK%J9RLP91I9:R:g00KI179<%E;5D9C:,6LR;%G5R<PLP91790RMg00L0RNP:C:,6LR:P<PLP4P5P5P6P:P;FHC;C;1BL6R6P1P8g00LWR;g00M7R:'K1@18=<;:dAL903CMR0b4b7b8X99%13%18128>'9[\?^99P1f8P3P8O3b3W1W0P3P1O2n2001000000121000000b5b69?3>%O=,53PAPCPFPDP2PEP7PBP8PJPI%P9PKP9PMPN179=C:,6LP6P0b4b7b8PBP1b3X1HX0GP3P1O2n2001000000120000000b5b69Q3=E=15@31T@3E=W:W;o"). Qed.
Lemma art_land_full_r : forall x, 0 <= x < 2 ^ 64 -> Z.land x 18446744073709551615 = x.
Proof.
ltac2:(KReplay.run1 (kr_t_ArtMem ()) [] "h02Hxh11xh21zp;2p;1p;3p;6p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9p1000Np4p7210R1g001:R0p4p710R2p8P1p1001Xp4p710p8p1002_p4p710P2p8p1003:p4p710p1003Yp4p710p8p10045p4p710P2p8g00E=j2>Tg004Wj12Tg005<j13Tg005Zj25Tg0067j2=Tg006Sj2:Tg00i[j10Tg00gVj24Tg0082j38Tg01D\j29Tg01D9j2<TP0j6;Tf0R0#0#0p=7%00#0#0#0p=6%00#0#0#0#0#0#0#0p=1g00I>R2g00Fa/>0g00I\R1#2R3#3%23#2#2#2#2#3'5,=0':P2%01#7#6#1#1#1#1#1#1#1#3R1f1R3'4f29820X22193014311<31E;W0W1o"). Qed.

(* [comment removed for export] *)
Lemma art_c_eq_zb : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> c_eq (Z_to_bv 64 x) (Z_to_bv 64 y) = Z.eqb x y.
Proof.
ltac2:(KReplay.run1 (kr_t_ArtMem ()) [] "h01Hh12H0h22H1h32H2h42Hah57__arithh66__sat0h76__sat1h84__x1h91zh:2Hxh;2Hyh<4__ffh=8__varmaph>5__with?1xh@1yp;1p;2p;3p;4p;7p;6p;8p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9p1000Np4p7210R1g001:R0p4p710R2p8P1p1001Xp4p710p8p1002_p4p710P2p8p1003:p4p710p1003Yp4p710p8p10045p4p710P2p8g004Wj13Tg005<j1;Tg005Zj2CTg0067j20Tg006SR2j22Tg006nj1LTg00C>j2>Tg00Cdj26Tg01E_j25Tg0082j34Tg00@;j2?Tg008Lj2@Tg0094j3TTg009Xj1STg00:8j1RTg00:Xj2OTg00;6j1NTg00;Tj1MTg00<?j2KTg00<bj2<Tg00=Ej3HTg00=hj47Tg00>Sj1FTg00?5j7ETg00?Yj2GTg00@Uj2DTg00AAj3ITg00A`j4JTg00[Lj29TP0j6=Tg01F<j2BTg00E=j2ATg00EYj7PTg00F=j8QTg00FaR0f0R1'Ap=1f1R3g00G?R4g00G^R5P5g00H>R6P1g00H^FPp=8f3R7P4P5P5P6f2R8P3P1GQp=:g00I>R9%13R:g00I\R;#3R<#;R=%3<#3#3#3#3R<#;R>'CR?,03'2R@P9P7g00LWRA%L<R<1><7RB'6RC,51f4RD/57RE34X99P9P815D1=4AEX991578RE,?A1><8RF,6<1@=>RG100=%1>100?[[RH%1=RIg00JARJAT=>3UW4R>%1?\J^4IRIP2%1DRJ10D?RDf5RK#110K?'2P8f6RL#1RMf7RN/0?ROP2f9RP#1RQ10P?RP12QPPNf;#1RRf</0?RSg00J]RT#S%RT1O93%N9%M9RTP91K9;R;g00KI1<9==H9<C7,8TR<%F5R=PTP91<90g00L0P;C7,8TR;P=PTP4P5P5P6P;P<FEC:C:1GT6P1P8g00M7RT,?A1D18=4ATdAI903CJb<b=b>X89R0101?%18108?'2\:[^89R:P1f=PKPLO3b5W3W2P3P1O2n2001000000121000000W1W0P3P1O2n2001000000121000000b6b7,98E=PCPGPHP>PIP2PJPD10L?,2MP8P2PQPPf:RP#110P?'2PNP0P:P1f>P3P8O3b5X3SX2RP3P1O2n2001000000121000000X1OX0MP3P1O2n2001000000121000000b6b7,97E=1BBF=4AEeX;@W:X@9W?o"). Qed.
Lemma art_c_ltu_zb : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> c_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = Z.ltb x y.
Proof.
ltac2:(KReplay.run1 (kr_t_ArtMem ()) [] "h01Hh12H0h22H1h32H2h42Hah57__arithh66__sat0h76__sat1h84__x1h91zh:2Hxh;2Hyh<4__ffh=8__varmaph>5__with?1xh@1yp;1p;2p;3p;4p;7p;6p;8p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9p1000Np4p7210R1g001:R0p4p710R2p8P1p1001Xp4p710p8p1002_p4p710P2p8p1003:p4p710p1003Yp4p710p8p10045p4p710P2p8g004Wj13Tg005<j1;Tg005Zj2CTg0067j20Tg006SR2j22Tg006nj1LTg00C>j2>Tg00Cdj26Tg0156j25Tg0082j34Tg00@;j2?Tg008Lj2@Tg0094j3TTg009Xj1STg00:8j1RTg00:Xj2OTg00;6j1NTg00;Tj1MTg00<?j2KTg00<bj2<Tg00=Ej3HTg00=hj47Tg00>Sj1FTg00?5j7ETg00?Yj2GTg00@Uj2DTg00AAj3ITg00A`j4JTg00[Lj29TP0j6=Tg01Fnj2BTg00E=j2ATg00EYj7PTg00F=j8QTg00FaR0f0R1'Ap=1f1R3g00G?R4g00G^R5P5g00H>R6P1g00H^FPp=8f3R7P4P5P5P6f2R8P3P1GQp=:g00I>R9%13R:g00I\R;#3R<#;R=%3<#3#3#3#3R<#;R>'CR?,03'2R@P9P7g00LWRA%L<R<1><7RB'6RC,51f4RD/57RE34X99P9P815D1=4AEX991578RE,?A1><8RF,6<1@=>RG100=%1>100?[[RH%1=RIg00JARJAT=>3UW4R>%1?\J^4IRIP2%1DRJ10D?RDf5RK#110K?'2P8f6RL#1RMf7RN/0?ROP2f9RP#1RQ10P?RP12QPPNf;#1RRf</0?RSg00J]RT#S%RT1O93%N9%M9RTP91K9;R;g00KI1<9==H9<C7,8TR<%F5R=PTP91<90g00L0P;C7,8TR;P=PTP4P5P5P6P;P<FEC:C:1GT6P1P8g00M7RT,?A1D18=4ATdAI903CJb<b=b>X89R0101?%18108?'2\:[^89R:P1f=PKPLO3b5W3W2P3P1O2n2001000000121000000W1W0P3P1O2n2001000000121000000b6b7,98E=PCPGPHP>PIP2PJPD10L?,2MP8P2PQPPf:RP#110P?'2PNP0P:P1f>P3P8O3b5X3SX2RP3P1O2n2001000000121000000X1OX0MP3P1O2n2001000000121000000b6b7,97E=1BBF=4AEeX;@W:X@9W?o"). Qed.

Lemma art_zb_xori_m1 : forall x, 0 <= x < 2 ^ 64 -> v_xori (Z_to_bv 64 x) (-1) = Z_to_bv 64 (2 ^ 64 - 1 - x).
Proof.
  intros x Hx. unfold v_xori. rewrite art_u_lit by lia. change (bv_wrap 64 (-1)) with (Z.ones 64). f_equal.
  rewrite <- Z.ldiff_ones_l_low; [| lia |].
  - rewrite Z.ldiff_land. rewrite <- Z.sub_land_same_l. rewrite Z.land_comm, Z.land_ones, Z.mod_small by lia. rewrite Z.ones_equiv. lia.
  - destruct (Z.eq_dec x 0) as [->|Hz]; [cbn; lia|]. apply Z.log2_lt_pow2; lia.
Qed.
Lemma art_zb_sltiu : forall x k, 0 <= x < 2 ^ 64 -> 0 <= k < 2 ^ 64 ->
  v_sltiu (Z_to_bv 64 x) k = Z_to_bv 64 (if x <? k then 1 else 0).
Proof.
  intros x k Hx Hk. unfold v_sltiu. rewrite art_u_lit by lia. rewrite bv_wrap_small by (change (bv_modulus 64) with (2^64); lia).
  destruct (x <? k); reflexivity.
Qed.
Lemma art_zb_sltu : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  v_sltu (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (if x <? y then 1 else 0).
Proof.
ltac2:(KReplay.run1 (kr_t_ArtMem ()) [] "p'0h01Hh12H0h22H1h32H2h42Hah57__arithh66__sat0h76__sat1h84__x1h91bi001bh:2Hxh;2Hyh<4__ffh=8__varmaph>5__with?1xh@1yp;1p;2p;3p;4p;7p;6p;8p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9p1000Np4p7210R1g001:R0p4p710R2p8P1p1001Xp4p710p8p1002_p4p710P2p8p1003:p4p710p1003Yp4p710p8p10045p4p710P2p8g004Wj14Tg005<j16Tg005Zj2@Tg0067j20Tg006SR2j23Tg0156j2;Tg006nj1DTg00N7j1BTg00C>j22Tg0082j35Tg00@;j27Tg01Fnj2=Tg008Lj2UTg0094j3TTg009Xj1STg00:8j1OTg00:Xj2NTg00;6j1KTg00;Tj1HTg00<?j2GTg00<bj2:Tg00=Ej3CTg00=hj48Tg00>Sj1ETg00?5j7FTg00?Yj2ATg00@Uj2ITg00AAj3JTg00A`j4?Tg01N>j4LTP0j6MTg01O>j2>Tg00E=j2PTg00EYj7QTg00F=j8RTg00FaR0f0R1'Pp=1f1R3g00G?R4g00G^R5P5g00H>R6P1g00H^FQp=9f3R7P4P5P5P6f2R8P3P1GRp=<g00I>R9%13R:g00I\R;#4R<#6R=%4<#4#4#4#4R<#6R>'@R?,03'3R@g00LWRA1;78RB%D<R<#BRCPAPCP1%6;RD,2<RE12<0RFn0100000020000RGPAP9f4RH/;7PDP0n0100000020000,2<35X9APBPAPAPAP9P1PDP0n0100000020000,2<95CGP117CE17CFn0110000020000b912<7RF12<8RE'=P7P81U=>R7100=%1>100?[[RG%1=RIg00JARJAT=>3UW4R>%1?\J^4IRIP2%1HRJ10H?RHf6RK#1RL10K?'3P8f7RM/0?RNP2f9RO#1RP10O?ROf:RQ#110Q?'3PMf;#1RQf</0?RRg00J]RS#S%OS1N93%K9%H9RSP91G9;R;g00KI1:9==C9<C8,9SR=%E5RTPSP91:90g00L0P;C8,9SR;PTPSP4P5P5P6P;P=FFC<C<1AS6P1P8g00M7RS,7A1I18=5ASdAJ903C?b<b=b>X89RS101?%18108?'3\:[^89R:P1f>P3P8O3b5W3W2P3P1O2n2001000000121000000W1X0LP3P1O2n2001000000121000000b6b7P7PGP>PIP2PJPHf5RH#110H?'3P8P2PPPO13POPMPSP:P1f=PHPKO3b5X3RX2QP3P1O2n2001000000121000000X1NX0LP3P1O2n2001000000121000000b6b7CLEM1>FEPAP9PBPDP0n0100000020000,2<55CeX;@W:X@9W?o"). Qed.

(* [comment removed for export] *)
Section WithSegs.
Variable segs : list Segment.

Definition cell (M : word -> option byte) (a : Z) (n : nat) (v : Z) : Prop :=
  rdn segs M (Z_to_bv 64 a) n = Some (word_to_le_bytes n (Z_to_bv 64 v)).
Definition Wn (n : nat) (M : word -> option byte) (a : Z) (v : Z) : word -> option byte :=
  wbytes M (Z_to_bv 64 a) (word_to_le_bytes n (Z_to_bv 64 v)).
Definition wok (M : word -> option byte) (a : Z) (n : nat) : Prop := store_ok segs M (Z_to_bv 64 a) n = true.
Definition apart (a n b m : Z) : Prop := a + n <= b \/ b + m <= a.

Lemma apart_sym : forall a n b m, apart a n b m -> apart b m a n.
Proof.
ltac2:(KReplay.run1 (kr_t_ArtMem ()) ["WithSegs"] "h04__x1h14__x2h24__x3h34__x4h41ah51bh61mh71nh87__arithh94__ffh:8__varmaph;5__witp;2p;1p;4p;3p;8p;7p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9p1000Np4p7210R1p1001:p4p710R0p8P1p1001Xp4p710p8p1002_p4p710P0p8p1003:p4p710p1003Yp4p710p8p10045p4p710P0p8g00O\j20Tg00E=j21Tg013Sj23Tg009Xj1=Tg00:8j1KTg00:Xj25Tg00bEj1FTg00bcj48Tg00;6j1?Tg00;Tj1>Tg00i[j1<Tg00<?j22Tg004Wj14Tg00jgj3;Tg00=hj4:Tg00>Sj1JTg00F=j8ITg00?Yj2ETg00@;j2CTg00@Uj2BTg0082j3ATg00AAj3@Tg00A`j4DTg01P2j47Tg00EYj7GTg01Pkj7HTf1R0g00G?R1g00G^R2P2g00H>R3f0R4g00H^FGp=6f2R5P1P2P2P3P0P4FHp=9g00I>R6f3R7/05/101004/17'3g00J]R8#=%K8P6P6f4R8,56P5%F6C8P01567C8%?6%>6R9P1P2P2P3P6g00I\R1#<,26R:%41R;#4,265;6g00L0R<1261R1C:,69R=P6126;9;61P<P:C:,69R:599%J2A99:=GI1E93P4P5g00LWR9g00M7R3'C1B45=A93dg00Fa=@60CDb9b:b;X06X16X26X361057/141040/15'31005/171078/10'3[^06^16^26^36P4P8f5P5P7P0O5b8UX66X56X76W4P7P5P0P4C7P5P0P8P7C7[^66^56^76^46eo"). Qed.

Lemma rdn_Wn_other : forall n M a v b m,
  0 <= a -> a + Z.of_nat n < 2 ^ 64 -> 0 <= b -> b + Z.of_nat m < 2 ^ 64 -> apart a (Z.of_nat n) b (Z.of_nat m) ->
  rdn segs (Wn n M a v) (Z_to_bv 64 b) m = rdn segs M (Z_to_bv 64 b) m.
Proof.
  intros n M a v b m Ha Han Hb Hbm Hap. unfold Wn.
  apply rdn_wbytes_out; rewrite ?length_N_to_le_bytes; rewrite ?(art_u_lit a) by lia; rewrite ?(art_u_lit b) by lia; unfold apart in Hap; lia.
Qed.

Lemma cell_Wn_other : forall n M a v b m u,
  0 <= a -> a + Z.of_nat n < 2 ^ 64 -> 0 <= b -> b + Z.of_nat m < 2 ^ 64 -> apart a (Z.of_nat n) b (Z.of_nat m) ->
  cell M b m u -> cell (Wn n M a v) b m u.
Proof.
ltac2:(KReplay.run1 (kr_t_ArtMem ()) ["WithSegs"] "h01Hh12Hah23Hanh33Haph42Hbh53Hbmh61Mh71ah81bh91mh:1nh;1oh<1uh=1vp;1p;2p;4p;3p;;p;6p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9p1000Np4p7210R1g001:R0p4p710R2p8P1p1001Xp4p710p8p1002_p4p710P2p8p1003:p4p710p1003Yp4p710p8p10045p4p710P2p8g004Wj10Tg006nj14Tg00N7j15Tg01QOj12Tg00E=j2DTg00n4j11Tg00O\j27Tg005<j13Tg005Zj2=Tg0067j26Tg01P2j4<Tg01WHj48Tg00:8j1;Tg00C>j2:Tg01V8j49Tg00nTj2CTg01X@j2BTg0082j3ATg01UBj4?Tg01Xbl;>TP0j6@Tg01ViR0g00I\#0R2#0#0R1#0#0#0R3#4R4#5%41#5R1#2[g00I>R5g00Faf4R6'DR7f5R8f7R9#1'7%32%33'=R3'6%16,78/63f8R3f:R2#1f6R:%18C<P2P9P:P8C8%;1R1#2R;p,4segsR<f;R=1:43R>P9C9f0R?1:49,C3,B15A;X;;P?P<f<R<P=P2f9R?C?R;P>P9C9P<P=P2P?P3P9P8P6f3f2f1M;>E@P;P3P9P:C8eW0W3W5X47W2W1X<5X90X85X=5W7W6W:o"). Qed.

Lemma cell_Wn_hit : forall n M a v, 0 <= a -> a + Z.of_nat n < 2 ^ 64 -> cell (Wn n M a v) a n v.
Proof.
  intros n M a v Ha Han. unfold cell, Wn.
  pose proof (rdn_wbytes_hit segs (word_to_le_bytes n (Z_to_bv 64 v)) M (Z_to_bv 64 a)) as H.
  rewrite length_N_to_le_bytes in H. apply H. rewrite art_u_lit by lia. lia.
Qed.

Lemma Wn_grows : forall n M a v, mem_grows M (Wn n M a v).
Proof.
ltac2:(KReplay.run1 (kr_t_ArtMem ()) ["WithSegs"] "h01Mh11ah21nh31vp;1p;2p;3p;4p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9p1000Np4p7210R1p1001:p4p710R0p8P1p1001Xp4p710p8p1002_p4p710P0p8p1003:p4p710p1003Yp4p710p8p10045p4p710P0p8g004Wj10Tg006nj11Tg00N7j12Tg01QOj14Tg00C>j23Tg00nTj28Tg01[`j37Tg01UBj45Tg01\aj26Tg01Vig00I\#0#0#0R0#0#0#0#1R1#2%10#2#4[g00I>R0f3R2f0R3,31'8f2R4f1R5,3137P2P4P5P3C5,64eX30W1W0W2o"). Qed.

Lemma wok_Wn : forall n M a v b m, wok M b m -> wok (Wn n M a v) b m.
Proof.
ltac2:(KReplay.run1 (kr_t_ArtMem ()) ["WithSegs"] "h01Hh11Mh21ah31bh41mh51nh61vp;1p;3p;4p;2p;7p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9p1000Np4p7210R1p1001:p4p710R0p8P1p1001Xp4p710p8p1002_p4p710P0p8p1003:p4p710p1003Yp4p710p8p10045p4p710P0p8g004Wj10Tg006nj11Tg00N7j12Tg01QOj14Tg01]_j33Tg01UBj48Tg00C>j27Tg01^Vj45Tg01_Rj76Tg01ViR0g00I\#0#0#0R1#0#0#0#1R2#2%11#2#4[g00I>R1f4R3f1R4f0R533p,4segsP4f5R6f6R7P6P3f3R8C8R9f2R:,72P7P6P3P8C5P5F6A39:4eW0X40X31X61W2W1W5o"). Qed.

Lemma wok_grows : forall M M' b m, mem_grows M M' -> wok M b m -> wok M' b m.
Proof.
ltac2:(KReplay.run1 (kr_t_ArtMem ()) ["WithSegs"] "h01Gh11Hh21Mh32M'h41bh51mp;1p;2p;3p;7p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9p1000Np4p7210R1p1001:p4p710R0p8P1p1001Xp4p710p8p1002_p4p710P0p8p1003:p4p710p1003Yp4p710p8p10045p4p710P0p8g004Wj10Tg006nj13Tg00N7j12Tg01QOj14Tg01\aj27Tg01]_j31Tg00C>j26Tg01_Rj75Tg00I\#0#0#0R0#0#0#0#3R1#2%30#2#4[R0g00I>g01Vif3R2f2R3'7f4R4f1R5713p,4segsP3f5P41612P5f0F5A1423eW1W0W5W4X30W2o"). Qed.

(* [comment removed for export] *)
Definition wr (M : word -> option byte) (a n : Z) : Prop :=
  forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok segs M (Z_to_bv 64 (a + d)) k = true.
Lemma wr_wok : forall M a n, wr M a n -> forall b k, a <= b -> b + Z.of_nat k <= a + n -> wok M b k.
Proof.
ltac2:(KReplay.run1 (kr_t_ArtMem ()) ["WithSegs"] "h04__x1h14__x2h27__arithh34__ffh48__varmaph55__with64cstrh74__x3h84__x4h91bh:1Hh;2H1h<2H2h=1Mh>1Wh?1ah@1khA1np;1p;3p;2p;4p;6p;7p;8p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9p1000Np4p7210R1p1001:p4p710R0p8P1p1001Xp4p710p8p1002_p4p710P0p8p1003:p4p710g003YR1p4p710p8p10045p4p710P0p8g004Wj12Tg006nj1ATg00N7j1>Tg01QOj1ETg01`Tj3VTg00E=j20Tg00n4j14Tg00O\j21Tg01R1j1=Tg009Xj1FTg00:8j1DTg00:Xj2:Tg00bEj1BTg00bcj4;Tg00;6j1UTg00;Tj1TTg00<?j29Tg00kJj3@Tg00jgj35Tg00=hj4?Tg00?Yj2OTg00@;j2LTg00@Uj2KTg0082j37Tg00AAj3HTg00A`j4GTg00Scj26Tg00C>j2ITg01aJj4JTg00>Sj1MTg00<bj2NTg00i[j1CTP1j6PTg01]_j3QTg00EYj7RTg00F=j8STf1R1g00G?R0g00G^R2P2g00H>R3f0R4g00H^FRp=3g00I>R5P1g00L0P4C?p=8f3R6P0P2P2P3f2R0P1P4GSp=<g00I\R7#2R8#2R9#2R:#2#2#2#AR;#>%A:#>#E[AV014g01Vif4R:/01%41,10f5R</1:'0%=0g00FaR=%40'0g00J]R>#FR?%D>R>P51:50P1%B5R@C;RA%U5RB%T5RCP51957RD1958R8=@5D555g00eGP8C?'31OC3R3P4P0g00LWREg00M7RF'L1K40=7EFdAH5=1CGRGb3b4b5X05X151614,14=751^05^15P4P<f8RHO2b2b6f6RI166I'1=756P5f7RJ16:JRK'1p,4segsf9RL1I;4P:CJ=7EFX95P<PKP6%=6RK%46,0=RFP?P>PAPBPC188D,3C%M2R21N5=A@5D8RA'8,3CC<P3PGb3b4b5X05X1510141610RE,0=[^05^15P4PLPIP:O3b2b6PKPFP?P>P5P51:5:P0P@C;P11:56C;PBPC%C7,95R7955D1959R99558'8,3CP2A55A7/89,3CC<P3PGb3b4b5X05X15X75X8511401116'011E6/0:[^05^15^75^85P4PH%4<PLPIP6O5b2b6O4P:P4EPb:AQJ60eW<W;W@X95W>XA5X?5W=o"). Qed.
Lemma wr_grows : forall M M' a n, mem_grows M M' -> wr M a n -> wr M' a n.
Proof.
ltac2:(KReplay.run1 (kr_t_ArtMem ()) ["WithSegs"] "h01Gh12Hdh22Hkh31Mh42M'h51Wh61ah71dh81kh91np;1p;2p;3p;7p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9p1000Np4p7210R1p1001:p4p710R0p8P1p1001Xp4p710p8p1002_p4p710P0p8p1003:p4p710p1003Yp4p710p8p10045p4p710P0p8g004Wj10Tg006nj15Tg00N7j12Tg01QOj16Tg01\aj2:Tg01`Tj34Tg00E=j23Tg00n4j19Tg00O\j21Tg00C>j28Tg01_Rj77Tg00I\#0#0#0R0#0#0#0#5R1#2%50#2#6[R0g00I>R2f3R3f2R4':f4R5f1R6744g01Vig00Fa/36%96,14f5R7'3p,4segsP4f9f8f7/13,81P7P5P3P4P6f0O4F7W2W1W8X72A4534eW5W0X92W6X40W3o"). Qed.
Lemma wr_Wn : forall n M a v b m, wr M b m -> wr (Wn n M a v) b m.
Proof.
ltac2:(KReplay.run1 (kr_t_ArtMem ()) ["WithSegs"] "h01Mh11ah21bh31mh41nh51vp;1p;3p;4p;6p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9p1000Np4p7210R1p1001:p4p710R0p8P1p1001Xp4p710p8p1002_p4p710P0p8p1003:p4p710p1003Yp4p710p8p10045p4p710P0p8g004Wj10Tg006nj12Tg00N7j11Tg01QOj13Tg01`Tj37Tg01UBj46Tg01^Vj45Tg01bJj64Tg01Vig00I\#0#0#0R0#0#0#0#2#1%20#1#3[g00I>R0f4R1f1R2f0R337f5R4f6R5P4P1f3R6C6f2P2P5P4P1P6C5P3E4UX30X20X50W1W0W4o"). Qed.
Lemma wr_sub : forall M a n a' n', wr M a n -> a <= a' -> a' + n' <= a + n -> wr M a' n'.
Proof.
ltac2:(KReplay.run1 (kr_t_ArtMem ()) ["WithSegs"] "h04__x1h14__x2h24__x3h37__arithh44__ffh58__varmaph65__with74cstrh84__x4h94__x5h:4__x6h;1Hh<2H1h=2H2h>2Hdh?2Hkh@1MhA1WhB1ahC2a'hD1dhE1khF1nhG2n'hH1zp;1p;3p;2p;4p;6p;7p;8p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9p1000Np4p7210R1p1001:p4p710R0p8P1p1001Xp4p710p8p1002_p4p710P0p8p1003:p4p710g003YR1p4p710p8p10045p4p710P0p8g004Wj14Tg006nj1ETg00N7j1ATg01QOj1JTg01`Tj3FTg00E=j21Tg00O\j20Tg00n4j1;Tg01R1j1@Tg009Xj1MTg00:8j1ITg00:Xj27Tg00bcj4<Tg00;6j1[Tg00;Tj1VTg00<?j25Tg00kJj3DTg00i[j1CTg00=hj4BTg00?Yj2UTg00@;j2STg00@Uj2RTg0082j39Tg00AAj3QTg00A`j4PTg00Scj28Tg00C>j2LTg01aJj4KTg00^_j1?Tg00_>j2=Tg00`Pj3>Tg00a9j2NTg00aej3HTg00<bj2OTg00>Sj1GTg00bEj1TTP1j6ZTg00jgj3YTg00EYj7XTg00F=j8WTg00I>R1f1R0f0R23Yp=2P0g00G?R3g00G^R4P4g00H>R5P2g00H^FXp=3P1P0g00L0P2CBp=6f3R6P3P4P4P5f2R3P0P2GWp=:g00I\R7#4R8#4R9#4R:#4#4#4#ER;#A%E:#A#J[f4R:?F6311:31063f5R</0:'1g01Vig00FaR=/10%;0,03f6R>'1%@3%;3,1=g00J]R?#MR@%I?RAP11713P01716C<RB%[1RC%V1RDP11517RE1518RF=D1E%C7R7,51RG'2'2g00eG12FGCB'31UD5R5P2P3g00LWRHg00M7RI'S1R23=9HIdAQ1=0CPRJb4b5b6X01X11X211802/03,021003591^01^11^21P2P<f:RKf<RLO3b3b7f8RM/8K/06,0K10M6591P1f;RNf9RO/8N/0:RP'0p,4segsf=RQ1L;2P:CK=9HIXH1f7RIPPP6%@6RP%;6,1=RHg00fKR;#?RR#?,=11=1R1=1;5>15>1g00fj'N=H?@R@PAPBPCPD1O1=RB/6G,3D%G4R4PD16FE,3DP4AD1EF/2GR?,6B,3DC:C:P5PJb4b5b6X01X11X2111=311301836/0:RB,1=[[^01^11^21P2P>PQPNP:PMO5b3b7PPPHP@PAP1P1171:P3171>C<P0P1171<P6%T1C<C<PCPD1519R9,2G%47,51R7'6,3DP4PD12E7%C8,51R8,2F'6,3DP412?9/68,3DC:C:P5PJb4b5b6X01X11X21X81X91X:11036/1<100>103<'110B</1>[[^01^11^21^81^91^:1P2PKPL%;<P>PQPNP6PIO8b3b7O410O:P2EZb;W?W>WEXD1AFI:6eW=W<WAXG1XC1XF1XB1W@o"). Qed.

(* [comment removed for export] *)
Lemma Wn_outside : forall n M a v (x : word),
  0 <= a -> a + Z.of_nat n < 2 ^ 64 ->
  ~ (a <= bv_unsigned x < a + Z.of_nat n) -> Wn n M a v x = M x.
Proof.
  intros n M a v x Ha Han Hx. unfold Wn.
  destruct (Z_lt_le_dec (bv_unsigned x) a) as [L|G].
  - apply wbytes_below; rewrite ?length_N_to_le_bytes, art_u_lit by lia; lia.
  - apply wbytes_above. rewrite length_N_to_le_bytes, art_u_lit by lia. lia.
Qed.

(* [comment removed for export] *)
Definition Wf (M : word -> option byte) (a : Z) (k : nat) (b : Z) : word -> option byte :=
  wbytes M (Z_to_bv 64 a) (repeat (Z_to_bv 8 b) k).
Lemma Wf_grows : forall M a k b, mem_grows M (Wf M a k b).
Proof.
ltac2:(KReplay.run1 (kr_t_ArtMem ()) ["WithSegs"] "h01Mh11ah21bh31kp;1p;2p;3p;4p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9p1000Np4p7210R1p1001:p4p710R0p8P1p1001Xp4p710p8p1002_p4p710P0p8p1003:p4p710p1003Yp4p710p8p10045p4p710P0p8g004Wj10Tg006nj11Tg00N7j12Tg01QOj14Tg00C>j23Tg01eoj38Tg01[`j37Tg01fNj45Tg01\aj26Tg00I\#0#0#0R0#0#0#0#1R1#2%10R0#2R2#4[g00I>R3g01Vif0R4,30f1R0582f3R2f2R5,3137P2P5P0P4C5,62eX23W3W1W0o"). Qed.
Lemma wok_Wf : forall M a k b c m, wok M c m -> wok (Wf M a k b) c m.
Proof.
ltac2:(KReplay.run1 (kr_t_ArtMem ()) ["WithSegs"] "h01Mh11ah21bh31ch41kh51mp;1p;3p;4p;6p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9p1000Np4p7210R1p1001:p4p710R0p8P1p1001Xp4p710p8p1002_p4p710P0p8p1003:p4p710p1003Yp4p710p8p10045p4p710P0p8g004Wj10Tg006nj12Tg00N7j11Tg01QOj13Tg01]_j37Tg01fNj46Tg01gDj45Tg01h@j64Tg00I\#0#0#0R0#0#0#0#2#1%20#1#3[g00I>R0g01ViR1f5R2f1R3f0R437f6R5P5P2f4R6f3R7C6f2P3P5P2P6P7C5P4E4UX51X30X20W4W1W0o"). Qed.
Lemma wr_Wf : forall M a k b c m, wr M c m -> wr (Wf M a k b) c m.
Proof.
ltac2:(KReplay.run1 (kr_t_ArtMem ()) ["WithSegs"] "h01Mh11ah21bh31ch41kh51mp;1p;3p;4p;6p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9p1000Np4p7210R1p1001:p4p710R0p8P1p1001Xp4p710p8p1002_p4p710P0p8p1003:p4p710p1003Yp4p710p8p10045p4p710P0p8g004Wj10Tg006nj12Tg00N7j11Tg01QOj13Tg01`Tj37Tg01fNj46Tg01gDj45Tg01bJj64Tg00I\#0#0#0R0#0#0#0#2#1%20#1#3[g00I>R0g01Vif5R1f1R2f0R337f6R4P4P1f4R5f3R6C6f2P2P4P1P5P6C5P3E4UX50X30X20W4W1W0o"). Qed.
Lemma rdn_Wf_other : forall M a k b c m,
  0 <= a -> a + Z.of_nat k < 2 ^ 64 -> 0 <= c -> c + Z.of_nat m < 2 ^ 64 -> apart a (Z.of_nat k) c (Z.of_nat m) ->
  rdn segs (Wf M a k b) (Z_to_bv 64 c) m = rdn segs M (Z_to_bv 64 c) m.
Proof.
  intros M a k b c m Ha Hk Hc Hm Hap. unfold Wf.
  apply rdn_wbytes_out; rewrite ?repeat_length; rewrite ?(art_u_lit a) by lia; rewrite ?(art_u_lit c) by lia; unfold apart in Hap; lia.
Qed.
Lemma cell_Wf_other : forall M a k b c m u,
  0 <= a -> a + Z.of_nat k < 2 ^ 64 -> 0 <= c -> c + Z.of_nat m < 2 ^ 64 -> apart a (Z.of_nat k) c (Z.of_nat m) ->
  cell M c m u -> cell (Wf M a k b) c m u.
Proof.
ltac2:(KReplay.run1 (kr_t_ArtMem ()) ["WithSegs"] "h01Hh12Hah23Haph32Hch42Hkh52Hmh61Mh71ah81bh91ch:1kh;1mh<1oh=1up;1p;2p;4p;3p;;p;6p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9p1000Np4p7210R1g001:R0p4p710R2p8P1p1001Xp4p710p8p1002_p4p710P2p8p1003:p4p710p1003Yp4p710p8p10045p4p710P2p8g004Wj10Tg006nj1;Tg00N7j15Tg01QOj12Tg00E=j24Tg00n4j11Tg00O\j27Tg005<j13Tg005Zj2>Tg0067j26Tg01P2j4=Tg01WHj48Tg00:8j1<Tg00C>j2:Tg01V8j49Tg00nTj2DTg01X@j2CTg0082j3BTg01fNj4ATg01i=l;?TP0j6@Tg00I\#0R0#0#0R2#0#0#0R1#;R3#5%;2#5R2#2[g00I>R4g01ViR5g00FaR6f5R7'4f6R8%17R9'7%30%31'>R1'6f4R0,46%10,77/61f9R1f8R6#1P8P9C=f;R9f7R:P8P7C8%<2R2#2R;p,4segsR<f<R=1:36R>P:C9f0R?1:3:,D6,C25B;X<;P?P<P=P9f:R<P1CAR?P>P:C9P=P9P<P1P6P:P7P0f3f2f1M;?E@P?P6P:P8C8eW0W2W5W3W4W1X=4X;5X94X84W:W7W6o"). Qed.
Lemma Wf_outside : forall M a k b (x : word),
  0 <= a -> a + Z.of_nat k < 2 ^ 64 -> ~ (a <= bv_unsigned x < a + Z.of_nat k) -> Wf M a k b x = M x.
Proof.
  intros M a k b x Ha Hk Hx. unfold Wf.
  destruct (Z_lt_le_dec (bv_unsigned x) a) as [L|G].
  - apply wbytes_below; rewrite ?repeat_length, art_u_lit by lia; lia.
  - apply wbytes_above. rewrite repeat_length, art_u_lit by lia. lia.
Qed.
Lemma Wf_inside : forall M a k b i, 0 <= a -> a + Z.of_nat k < 2 ^ 64 -> 0 <= i < Z.of_nat k ->
  Wf M a k b (Z_to_bv 64 (a + i)) = Some (Z_to_bv 8 b).
Proof.
  intros M a k b i Ha Hk Hi. unfold Wf.
  rewrite wbytes_inside; rewrite ?repeat_length, ?art_u_lit by lia; try lia.
  rewrite nth_repeat_lt by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma Wn_eq : forall n M M' a a' v v', M = M' -> a = a' -> v = v' -> Wn n M a v = Wn n M' a' v'.
Proof.
ltac2:(KReplay.run1 (kr_t_ArtMem ()) ["WithSegs"] "h01Mh11ah21vh32M'h42a'h51nh62v'p;1p;3p;4p;2p;6p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9p1000Np4p7210R1g001:R0p4p710R2p8P1p1001Xp4p710p8p1002_p4p710P2p8p1003:p4p710p1003Yp4p710p8p10045p4p710P2p8g004Wj10Tg006nj15Tg00N7j14Tg01QOj16Tg0082j31Tg01UBj42Tg00@;j27TP0j63Tg01Vig00I\#0#0#0R0#0#0#0#5#4%50#4#6[R0g00I>R2f5R1f4R3510f3R49123f2R59124P0f7R6f:R7f0R8P6P1C2P7f8R9f6R:P3C2R;510X00P2P1P7P9P8P1C2=10;X12P2P4P7P9P:P8C2=10;X22f9P6P1P4C2,70P3P8E3P:f1E3P9P5E3UUUX62X22X42W1X30W0W5o"). Qed.
Lemma Wf_eq : forall M M' a a' k k' b b', M = M' -> a = a' -> k = k' -> b = b' -> Wf M a k b = Wf M' a' k' b'.
Proof.
ltac2:(KReplay.run1 (kr_t_ArtMem ()) ["WithSegs"] "h01Mh11ah21bh31kh42M'h52a'h62b'h72k'p;1p;3p;4p;2p;6p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9p1000Np4p7210R1g001:R0p4p710R2p8P1p1001Xp4p710p8p1002_p4p710P2p8p1003:p4p710p1003Yp4p710p8p10045p4p710P2p8g004Wj11Tg006nj15Tg00N7j14Tg01QOj16Tg0082j30Tg01fNj42Tg00@;j27TP0j63Tg00I\#1#1#1R0#1#1#1#5#4%50#4#6[R0g00I>R2g01ViR1f7R3f6R4500f5R59024f4R69015f3R79026P0f:R8f0R9P8f8R:P4C2f;R;f9R<P3P5C2R=500X00P2P:P;P9P:P4C2=00=X12P1P4P;P<P9P4C2=00=X31P2P6P;P<P3P9C2=00=X22P8P:P4P6C2,70P5P9E3P3f1E3P<f2E3P;P7E3UUUUX62X22X71W3X52W1X40W0o"). Qed.

(* [comment removed for export] *)
Lemma cell_rdn8 : forall M a v, cell M a 8 v ->
  rdn segs M (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 v)) /\ bytes_le_to_Z (word_to_le_bytes 8 (Z_to_bv 64 v)) = bv_unsigned (Z_to_bv 64 v).
Proof.
ltac2:(KReplay.run1 (kr_t_ArtMem ()) ["WithSegs"] "h01Hh11Mh21ah31vp;1p;4p;2p;3p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9p1000Np4p7210R1p1001:p4p710R0p8P1p1001Xp4p710p8p1002_p4p710P0p8p1003:p4p710p1003Yp4p710p8p10045p4p710P0p8g004Wj11Tg006nj16Tg00N7j12Tg01QOj14Tg00^_j10Tg01WHj4<Tg00:8j1;Tg00C>j23Tg01V8j49Tg00nTj28Tg01X@j27Tg0082j35Tg00o\j1:Tg00Cdj2?Tg021]j1>Tg017Qj4=Tg00I\#1#1#1R0#1#1#1#6R1#2%60#2R0#4[g00I>R2f2R3f1R4g00fK#0#0#0#0#0#0#0#0R5f0R6C<%;0R0#4p,4segsf31313P5C91314R4,85R5,7035%:51?14552P6%>4C=W0X32W2W1o"). Qed.
Lemma cell_rdn1 : forall M a v, 0 <= v < 256 -> cell M a 1 v -> rdn segs M (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v].
Proof.
ltac2:(KReplay.run1 (kr_t_ArtMem ()) ["WithSegs"] "h01Hh12Hah24__x1h32H0h42H1h52Hvh61Mh77__arithh84__ffh96__sat0h:6__sat1h;8__varmaph<5__with=1ah>1lh?1vp;1p;2p;4p;3p;7p;6p;8p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9p1000Np4p7210R1p1001:p4p710R0p8P1p1001Xp4p710p8p1002_p4p710P0p8p1003:p4p710g003YR1p4p710p8p10045p4p710P0p8g004Wj11Tg006nj1ATg00N7j1;Tg01QOj1<Tg005<j19Tg0067j22Tg006SR0j25Tg00^_j1GTg01WHj4FTg00:8j1:Tg00C>j23Tg00nTj2BTg01V8j4@Tg01X@j2>Tg0082j38Tg009Xj1=Tg00aej3WTg008Lj2VTg005Zj2UTg0094j3TTg00:Xj2NTg00;6j1MTg00;Tj1LTg00<?j2KTg00<bj26Tg00=hj44Tg00>Sj1HTg00=Ej3ITg00?5j7JTg00?Yj2ETg00@;j2DTg00@Uj2CTg00AAj3OTg00A`j4PTg022aj2QTP1j6RTg00E=j2STg00EYj7YTg00F=j8XTg00FaR1f0R2'Sp=0f1R3g00G?R4g00G^R5P5g00H>R6P2g00H^FYp=7f3R7P4P5P5P6f2R8P3P2GXp=?g00I\R9#1R:#1#1R;#1#1#1R<#AR=#;%A;R;#;R>#<[g00I>R?%02%1<#1#9R@,22RA'5P7P8g00fK#GRBP3CF%:>RC13=8,BB%<CRDp,4segsREf5RFf4RG,3=PBC@1>C238X>CP213;8%=>5W>R>%9:R:%9<R<'V121:%0<1U:<R;,21[[%0:RHg00JARIAT:<3UW1%0;\I^1HP0%0G12G@%0F12F;'5P7f6#0f7/2@g00J]RF#=%:F1N?3%M?%L?RFP?1K?9R9g00KIR016?@C4,7F%H5R@PFP?16?1g00L0P9C4,7FRHP@PFP4P5P5P6PHP?P9P016?:=I?=C4,7FFJC?C?1EF6P2P8g00LWRFg00M7R6'D1C28=8F6dAO?13CPb8b;b<X2?%03%08128;'5[\A^2?P2f9P3P8O3b7W4W3P3P2O2n2001000000121000000b9b:,Q8ERPEPG13=7PBC@1>C>58DP2b0W0W5X??W=W6o"). Qed.
Lemma cell_rdn4 : forall M a v, 0 <= v < 2 ^ 32 -> cell M a 4 v ->
  rdn segs M (Z_to_bv 64 a) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 v)) /\ bytes_le_to_Z (word_to_le_bytes 4 (Z_to_bv 64 v)) = bv_unsigned (Z_to_bv 64 v).
Proof.
ltac2:(KReplay.run1 (kr_t_ArtMem ()) ["WithSegs"] "h01Hh12Hvh21Mh31ah41vp;1p;2p;4p;3p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9p1000Np4p7210R1p1001:p4p710R0p8P1p1001Xp4p710p8p1002_p4p710P0p8p1003:p4p710p1003Yp4p710p8p10045p4p710P0p8g004Wj10Tg006nj17Tg00N7j12Tg01QOj14Tg00E=j2DTg005<j13Tg005Zj2<Tg0067j2;Tg006Sj2:Tg00^_j11Tg01WHj48Tg00:8j19Tg00C>j25Tg01V8j4CTg00nTj2BTg01X@j2ATg0082j36Tg00o\j1=Tg00Cdj2>Tg023_j2?Tg017Qj4@Tg00I\#0R0#0#0R1#0#0R2#0#7R3#2%71#2R1#4[g00I>R4g00Faf0R5'D%30%32'<,;5':f3R2f2R0g00fK#1#1#1#1R6f1R7C8%91R1#4p,4segsf41532P6CC1530R2,B6R6,A136%=61>32564P51?07C@W0W1X44W3W2o"). Qed.

End WithSegs.

End ArtMem.
Module ArtStk.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0035.ArtMem.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_ArtStk () := "C47Corelib7Program6Basics4flipC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00C46Stdlib5Lists4List6nth_okC46Stdlib5Lists4List:firstn_nilC47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List=repeat_lengthc59OSSVerify5KrLib7Mh_00356ArtStk4avalC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00356ArtStk4aoffC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K47Corelib7Numbers7BinNums8positive02k59OSSVerify5KrLib7Mh_00356ArtStk6ashape02C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01k59OSSVerify5KrLib7Mh_00356ArtStk6ashape03C1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op201C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01i59OSSVerify5KrLib7Mh_00356ArtStk6ashape00C1?~~~~~~~~~~~~~~~I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01k59OSSVerify5KrLib7Mh_00356ArtStk6ashape01C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltc59OSSVerify5KrLib7Mh_00356ArtStk7env_othC1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib7Mh_00356ArtStk4hull01C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00356ArtStk8hull_rngC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00356ArtStk2hBC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00356ArtStk3hloC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00356ArtStk3hhiC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01i59OSSVerify5KrLib7Mh_00356ArtStk4hull00C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01I47Corelib4Init5Logic2or00I47Corelib4Init5Logic3and00C47Corelib4Init5Peano2ltC56Stdlib6ZArith6BinInt1Z6of_natC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula03K47Corelib4Init9Datatypes3nat02C46Stdlib9micromega;ZifyClasses;rew_iff_revC47Corelib4Init9Datatypes8list_indC47Corelib4Init9Datatypes6lengthC47Corelib5Lists7ListDef3nthC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula08K47Corelib4Init9Datatypes4list02C46Stdlib9micromega;ZifyClasses5mkappc59OSSVerify5KrLib7Mh_00356ArtStk5hull0C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z6inj_ltK47Corelib4Init9Datatypes3nat01K46Stdlib9micromega=RingMicromega3Op205C56Stdlib6ZArith4Znat5Nat2Z8inj_succK46Stdlib9micromega=RingMicromega3Op203K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00c59OSSVerify5KrLib7Mh_00356ArtMem3wokC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00356ArtStk4sstkC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00356ArtMem6wok_WnC1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib7Mh_00356ArtStk6slayer01C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00356ArtMem6wok_WfC1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib7Mh_00356ArtStk6slayer02C1?~~~~~~~~~~~~~~~i59OSSVerify5KrLib7Mh_00356ArtStk6slayer00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00356ArtMem2wrC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00356ArtMem5wr_WnC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00356ArtMem5wr_WfC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00356ArtStk6env_okC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00356ArtStk7stk_chkC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00356ArtMem4cellC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init9Datatypes9andb_propC56Stdlib6ZArith6BinInt1Z6eqb_eqC56Stdlib6ZArith6BinInt1Z6leb_lec59OSSVerify5KrLib7Mh_00356ArtStk8aval_offC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00356ArtStk6lay_okC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00356ArtStk3wljC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3ltbC56Stdlib5Arith8PeanoNat3Nat6ltb_ltc59OSSVerify5KrLib7Mh_00356ArtStk3wlsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00356ArtStk3wlkC1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool8orb_propC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega=RingMicromega5Psatz02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04c59OSSVerify5KrLib7Mh_00356ArtStk;env_oth_nthC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00356ArtMem5apartC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00356ArtStk5wsizeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebc59OSSVerify5KrLib7Mh_00356ArtStk4wstkC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00356ArtMem2WnC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00356ArtMem2WfC1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib7Mh_00356ArtStk5wkind01C1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr07c59OSSVerify5KrLib7Mh_00356ArtMem=cell_Wn_otherC1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib7Mh_00356ArtStk5wkind02C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00356ArtMem=cell_Wf_otherC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00356ArtStk5hbaseC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4andbC46Stdlib5Lists4List7forallbC47Corelib4Init9Datatypes3orbK46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02i59OSSVerify5KrLib7Mh_00356ArtStk6wlayer00C1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00i59OSSVerify5KrLib7Mh_00356ArtStk5wkind00C1?~~~~~~~~~~~~~~~".
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Inductive ashape : Set := Sh_bare | Sh_off (o : Z) | Sh_off2 (o1 o2 : Z).
Definition aval (B : Z) (s : ashape) : Z := match s with Sh_bare => B | Sh_off o => B + o | Sh_off2 o1 o2 => B + o1 + o2 end.
Definition aoff (s : ashape) : Z := match s with Sh_bare => 0 | Sh_off o => o | Sh_off2 o1 o2 => o1 + o2 end.
Lemma aval_off : forall B s, aval B s = B + aoff s.
Proof.
ltac2:(KReplay.run1 (kr_t_ArtStk ()) [] "p'0h04__x1h14__x2h27__arithh34__ffh48__varmaph55__with64__x3h71Bh81oi001oh92o1i012o1h:2o2i022o2h;1si031ap;2p;1p;3p;4p;7p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9p1000Np4p7210R1p1001:p4p710R0p8P1p1001Xp4p710p8p1002_p4p710P0p8p1003:p4p710p1003Yp4p710p8p10045p4p710P0p8g004Wj23Tg005Oj14Tg006Gj20Tg006dj1KTg007Dj1CTg007dj27Tg008Bj1>Tg008`j1<Tg009Kj26Tg009nj2;Tg00:Qj32Tg00;4j2JTg00;Vj2ITg00<0j2BTg00<\j39Tg00=6j3ATg00=Uj4?Tg00>Gj1@Tg00>ej4:Tg00?Cj1=Tg00?hj1DTg00@dj1ETg00AIj2FTg00BEj4GTg00C0j7HTg00CTR0f1R1f0R239p=1P0P1g00D2P2CGp=5P1g00DYg00E8R3P3g00EXR3P2g00F8FHp=8g00FXR4P4f2R4/32%42,04'1P2g00GTR5#KR6%C5R51701%>0R7%<0R8g00H@R9,60R:g00HeR;,;0920:'5'81J83R3P2P4g00ICR<g00IcR='I1B24=9<=dAA0;1C?R=b3b4b5X00102;,12^00P2P4O1b2g00JCR;,31%4;,01'1eP6P5P01704R;P1%@0C:P7%=9,60R<920:R>/5>,88P3P=b3b4b5X00X101021R?/1?^00^10P2P1f4O2b2f3R@%D2RA'3%4A,0@'1eX80P2O1P6P5P0P;P1170@C:P7%E9,60R9920>A20<9920:'5,88P3P=b3b4b5X00X10X6010?41014,02'1^00^10^60P2P1P4f6O3b2f5R41F12R?'3%4?,04'1eX:0X90P1P2O2n011030003001010020101102W;X70o"). Qed.

(* [comment removed for export] *)
Record hull : Set := mkhull { hB : Z; hlo : Z; hhi : Z }.
Definition hull0 : hull := mkhull 0 0 0.
Definition hbase (env : list hull) (j : nat) : Z := hB (nth j env hull0).
Inductive wkind : Set := WKn (n : nat) (v : Z) | WKf (k : nat) (b : Z).
Definition wsize (k : wkind) : nat := match k with WKn n _ => n | WKf k _ => k end.
Record wlayer : Set := mkwl { wlj : nat; wls : ashape; wlk : wkind }.

Fixpoint wstk (env : list hull) (M0 : word -> option byte) (l : list wlayer) : word -> option byte :=
  match l with
  | [] => M0
  | ly :: l' =>
      match wlk ly with
      | WKn n v => Wn n (wstk env M0 l') (aval (hbase env (wlj ly)) (wls ly)) v
      | WKf k b => Wf (wstk env M0 l') (aval (hbase env (wlj ly)) (wls ly)) k b
      end
  end.

(* [comment removed for export] *)
Definition lay_ok (env : list hull) (ob mz : Z) (ly : wlayer) : bool :=
  let h := nth (wlj ly) env hull0 in let o := aoff (wls ly) in let n := Z.of_nat (wsize (wlk ly)) in
  (wlj ly <? length env)%nat && (hlo h <=? o) && (o + n <=? hhi h)
  && (match wlj ly with O => (o + n <=? ob) || (ob + mz <=? o) | S _ => true end).
Definition stk_chk (env : list hull) (sb : ashape) (m : nat) (mz : Z) (l : list wlayer) : bool :=
  (mz =? Z.of_nat m) && (hlo (nth 0 env hull0) <=? aoff sb) && (aoff sb + mz <=? hhi (nth 0 env hull0)) && forallb (lay_ok env (aoff sb) mz) l.

(* [comment removed for export] *)
Definition hull_rng (h : hull) : Prop := 0 <= hB h + hlo h /\ hB h + hhi h < 2 ^ 64.
Fixpoint env_oth (env : list hull) (b mz : Z) : Prop :=
  match env with
  | [] => True
  | h :: env' => (hull_rng h /\ (b + mz <= hB h + hlo h \/ hB h + hhi h <= b)) /\ env_oth env' b mz
  end.
Definition env_ok (env : list hull) (b mz : Z) : Prop :=
  match env with [] => False | h :: env' => hull_rng h /\ env_oth env' b mz end.
Lemma env_ok_intro : forall B lo hi env b mz, 0 <= B + lo -> B + hi < 2 ^ 64 -> env_oth env b mz -> env_ok (mkhull B lo hi :: env) b mz.
Proof.
ltac2:(KReplay.run1 (kr_t_ArtStk ()) [] "h01Bh11bh23envh32hih42loh52mzp;1p;2p;3p;4p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9p1000Np4p7210R1p1001:p4p710R0p8P1p1001Xp4p710p8p1002_p4p710P0p8p1003:p4p710p1003Yp4p710p8p10045p4p710P0p8g007Dj1=Tg006Gj21Tg00K?j22Tg00?Cj10Tg00K[j16Tg00L9j2<Tg00LVj24Tg00M2j33Tg00Mmj3;Tg00Ngj1:Tg00Ocj17Tg00PYj18Tg00QPj19Tg00RGj45Tg00CTR0g00Rb#=g00HeR1f5R2f4R3'1'2f6R4/13g00H@#0R5#6%05#0#0#0#0#6'<R5'4f3R6f2R7533f8f7;;4R4#:A3236%74R6%84'1,21%94,16/45P7f1C5f0C5UUUX50X10W2X30X40W0o"). Qed.
Lemma env_oth_nil : forall b mz, env_oth [] b mz.
Proof.
ltac2:(KReplay.run1 (kr_t_ArtStk ()) [] "h01bh12mzp-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9p1000Np4p7210R1p1001:p4p710R0p8P1p1001Xp4p710p8p1002_p4p710P0p8p1003:p4p710p1003Yp4p710p8p10045p4p710P0p8g00CTR0g00S\X10W0o"). Qed.
Lemma env_oth_cons : forall B lo hi env b mz, 0 <= B + lo -> B + hi < 2 ^ 64 -> (b + mz <= B + lo \/ B + hi <= b) -> env_oth env b mz ->
  env_oth (mkhull B lo hi :: env) b mz.
Proof.
ltac2:(KReplay.run1 (kr_t_ArtStk ()) [] "h01Bh11bh23envh32hih42loh52mzp;1p;2p;3p;4p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9p1000Np4p7210R1p1001:p4p710R0p8P1p1001Xp4p710p8p1002_p4p710P0p8p1003:p4p710p1003Yp4p710p8p10045p4p710P0p8g007Dj1?Tg006Gj20Tg00K?j21Tg00?Cj12Tg00K[j17Tg00L9j2<Tg00LVj26Tg00T8j24Tg00M2j35Tg00Mmj3;Tg00Ngj18Tg00Ocj19Tg00PYj1:Tg00QPj1>Tg00TRj2=Tg00RGj43Tg00CTR0g00Rb#?g00HeR1f5R2f4R3'0R4'1f6R5/03g00H@#2R6#7%26#2#2#2#2#7'<R6'6f3R7f2R8'0f7R9/05'11092/17'4A5237f9f8;;9R9#8R:%99R;%:9'0R<,14%>9,0;R;/12'4R9'=A5523P:P9111<16;6P7P8C3f1C3f0C3UUUUX50X10W2X30X40W0o"). Qed.

Lemma env_oth_nth : forall env b mz j, env_oth env b mz -> (j < length env)%nat ->
  hull_rng (nth j env hull0) /\ (b + mz <= hB (nth j env hull0) + hlo (nth j env hull0) \/ hB (nth j env hull0) + hhi (nth j env hull0) <= b).
Proof.
ltac2:(KReplay.run1 (kr_t_ArtStk ()) [] "p'0h02Hjh14__x1h21jh31bh43envh52mzh61Hh73Hj0h87__arithh94__ffh:4__p1h;8__varmaph<5__with=4__x2h>4cstrh?2H1h@2H2hA2IHhB5cstr0hC1hhD1xi001np;1p;3p;2p;4p;6p;5p;<p;7p;8p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9p1000Np4p7210R1p1001:p4p710R0p8P1p1001Xp4p710p8p1002_p4p710P0p8p1003:p4p710p1003Yp4p710p8p10045p4p710P0p8g007Dj1NTg00M2j3>Tg00TmR0j23Tg00Ngj18Tg006Gj20Tg00Ocj1<Tg00PYj17Tg00K?j25Tg00QPj1;Tg00T8j29Tg00TRR1j2=Tg006dj1QTg00UER2j14Tg00LVR3j2:Tg00;Vj2?Tg00Uej4MTg00VLj1ETg00>Gj1\Tg007dj2KTg00>ej4DTg008Bj1[Tg008`j1ZTg009nj2JTg00@dj1YTg00?Cj1HTg009Kj2FTg00BEj4LTg00W1j1XTg00WSj6WTg00;4j2VTg00<0j2UTg00<\j3TTg00=6j3STg00=Uj4gTg00X7R4j1GTg00K[j1fTg00:Qj3OTg00XVj4eTg00YAj5dTg00Ycj2`Tg00ZCj4_Tg00Z_l<PTg00C0j7^Tg00[Dj8aTg00[hj3bTg00\Hl<cTg00RbR5f0R6'`p=2P5f1R7P6g00\mC_p=Af2R8/07/56p=1g00]fR9g00CTR:P0P2P3g00^ER;f3R<P8P7g00^gR=g00HeR>P6M<Pp=]P7g00DYR?g00E8R@P@g00EXRAP6g00F8F^p=@P:P7g00_FP6CLp=CP<P?P@P@PAP8P7P6Gap=BAb576p=6P9P:P0P2P3P;f5R;f4R3P<P8P7P6M<Pp=RP9P9P:P:P4P2P2P<g00_mP8P7P6M<cp=I%N5R2P5A><87%23,371A8;R4#8103<R0%<4RB%74'0'5%;4=1B3'9'=[[^29^5:^3:RBX42%Q5R4?>87%24,37138=%48RC/:>RDP8PC1?:C1?:>C]P6CMPD%E<%4<,5>p-0RDg00GTRE#QRF%NEREP:P:%\:RGP71K:7CDP7PGCD%[:RH%Z:RIP:1J:>RJg00`Qg00H@RK#Y#H,F:RLCL,@I%X@RMPI1CLJ,@IPMPIP?P@P@PAP<EWCBCB1VIARAP6P8g00ICR@g00IcR?'?1U68=T@?dAS:>7CgR?b9b;b<X1:W:15>61:7>P<[[^1:^:DP61A;4R4#8f7RDf6R@%<4RL%74'031%;4=1LD'9'=%4;RLP7P8O4b8b>b7W0W6X29X5:X3:16;3?>8716@;#2,37P1%8D%<DR1%7D'0,50%;D=113'9'=A>@3<f8/6D,A<R1#8%<1R0%71'091;3%;1=10;'9'=P7f9R0#8%<0R1%70'091@;%;0=11@'9'=A>0D@P9f<RDf;R1'6#2,36f=R;/6DR4,A7RJ#8f:RN%<JRO%7J'0710%;J=1ON'9'=]0P@161N#2,3=P8W0%G6%24'3PDP1PNP7P<%2;R;,37%47RN%4;R1':P7PN1?:NRDP;P11?:1R4ER%G7R=%G;R@'3%fKRO,0N101O':RJP=106OR=XD:R0PNO1P0P7PNPDCIP@P0P1O1P0P;P1P4CIERP6CMPJ%E815>Cf?#2RC#E%4C,5>PFPEP:1K:8P7PGCDPHPI1F:KRH1J:ORG5O:%HK,F:RK=O:G'C,@IPM1CHK,@ICBPAP?b9b;b<X1:X=:107O,:=1:78[^1:^=:P6fA#2#4PLP<O3b8bBb>b7CeO5W0X29P6O1n0110000020011100P3O1W@W?P7P6O2n2001000000121000000W0W6X29X5:X3:XABX42XC5P6DdW4o"). Qed.

(* [comment removed for export] *)
Inductive slayer : Set := SLn (n : nat) (a v : Z) | SLf (a : Z) (k : nat) (b : Z).
Fixpoint sstk (M0 : word -> option byte) (l : list slayer) : word -> option byte :=
  match l with
  | [] => M0
  | SLn n a v :: l' => Wn n (sstk M0 l') a v
  | SLf a k b :: l' => Wf (sstk M0 l') a k b
  end.

Section WithSegs.
Variable segs : list Segment.

Lemma wok_sstk : forall M0 l b m, wok segs M0 b m -> wok segs (sstk M0 l) b m.
Proof.
ltac2:(KReplay.run1 (kr_t_ArtStk ()) ["WithSegs"] "p'0h01lh12IHh21ai001ah31Hh42M0h52a0h61bi011bh72bbh81ki021kh91mh:1ni031nh;1vi041vi051sp;1p;4p;2p;3p;8p;5p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9p1000Np4p7210R1p1001:p4p710R0p8P1p1001Xp4p710p8p1002_p4p710P0p8p1003:p4p710p1003Yp4p710p8p10045p4p710P0p8g00?Cj12Tg00a8j15Tg00aVj14Tg00b9j16Tg007Dj1<Tg00b[j40Tg00cRj21Tg00[hj33Tg00dJj8;Tg00eDj3:Tg00f@j87Tg00g:j38Tg00YAj59Tg00H@#2#2#2R0#2#2#2#5#4%50#4#6[g00h6R0#<R1g00CTR2g00]fR3p,4segsR4f3R5f1R6f0R7C0P0P4f5R8/17P5f2R9C0X01P7P0P4f7/17P8f4R:C0P4f8A3096'1f6P8C0[^01P7P4f</17f:R8f9C0R;P4P:f=R</16R=P5P9f;R>P8P7G;P4A::59=306,1<P>P8C0eW1X01X;2X22X:3P9P6P7O3P4P=P:P5P9P>P8P7G7P4A8:59=306,1<P>P8C0eX1;X01X72X83X22P9P6P7O3n0110500023010310010430100102101X50P5D9W3W9W6W0W4o"). Qed.
Lemma wr_sstk : forall M0 l b m, wr segs M0 b m -> wr segs (sstk M0 l) b m.
Proof.
ltac2:(KReplay.run1 (kr_t_ArtStk ()) ["WithSegs"] "p'0h01lh12IHh21ai001ah31Hh42M0h52a0h61bi011bh72bbh81ki021kh91mh:1ni031nh;1vi041vi051sp;1p;4p;2p;3p;8p;5p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9p1000Np4p7210R1p1001:p4p710R0p8P1p1001Xp4p710p8p1002_p4p710P0p8p1003:p4p710p1003Yp4p710p8p10045p4p710P0p8g00?Cj12Tg00a8j15Tg00aVj14Tg00b9j16Tg007Dj1<Tg00i2j40Tg00cRj21Tg00[hj33Tg00ihj8;Tg00eDj3:Tg00jaj87Tg00g:j38Tg00YAj59Tg00H@#2#2#2R0#2#2#2#5#4%50#4#6[g00h6R0#<R1g00CTR2p,4segsR3f3R4f1R5f0R6C0P0P3f5R7/16P4f2R8C0X01P6P0P3f7/16P7f4R9C0P3f8A3085'1f6P7C0[^01P6g00]fR7P3f</16f:R:f9C0R;P3P9f=R</15R=P4P8f;R>P:P6G;P3A:948=305,1<P>P:C0eW1X01X;2X22W:P8P5P6O3P3P=P9P4P8P>P:P6G7P3A8948=305,1<P>P:C0eX1;X01X72X87X22P8P5P6O3n0110500023010310010430100102101X50P4D9W3X92W6W0W4o"). Qed.

Lemma cell_wstk_other : forall env M0 l b sb m mz u,
  b = aval (hbase env 0) sb -> env_ok env b mz -> stk_chk env sb m mz l = true ->
  cell segs M0 b m u -> cell segs (wstk env M0 l) b m u.
Proof.
ltac2:(KReplay.run1 (kr_t_ArtStk ()) ["WithSegs"] "p'0h06__sat4h14__x1h24__x2h34__x3h44__x4h53Hj0h66__sat3h74cstrh85cstr0h92H0h:2HLh;3Ho2h<3Hsbh=7__arithh>4__ffh?8__varmaph@5__withA4__x5hB5cstr1hC5cstr2hD1ni001nhE1mhF2HChG3HlyhH3Hb1hI3Hb2hJ2HjhK3Ho1hL2APhM2EahN3Eb0hO2EjhP3Ej0hQ2HEhR2HshS4__p1hT4__x6hU1ahV1bi011bhW1li021lhX2HahY3HmzhZ2IHh[2R1h\2R2h]6__sat5h^4__x7h_4__x8h`5cstr3ha1xi031xhb2Ebhc1Hhd2HOhe2M0hf2R3hg2RAhh3Rb1hi3Rb2hj2bbhk3envhl4env'hm2h0hn1jho1ki041khp2lyhq2mzhr2sbhs1uht1vi051vhu1wi061whv1yhw1zi071hi082n0p%0p%1p&0p&1p;1p;2p;3p;5p;6p;4p;<p;>p;7p;8p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9p1000Np4p7210R1g001:R0p4p710R2p8P1p1001Xp4p710p8p1002_p4p710P2p8p1003:p4p710p1003Yp4p710p8p10045p4p710P2p8g007DR2k10KTg00?Cj1XTg00a8k10QTg00aVk10OTg00b9k117Tg004Wj2cTg00kZk304Tg00lTk50lTg00mOj5oTg00UER1j13Tg00nGj2TTg005Oj11Tg006Gj20Tg00QPj19Tg00ndj3mTg00TRR3j2:Tg00oGk20hTg00K?j25Tg00ogk20dTg006dk10<Tg00PYj1BTg00Ngj1wTg00M2k30CTg00Ocj16Tg00K[k10HTg00L9k214Tg010Gk20XTP0k60ETg011Ck40Bk30VTg012=j18Tg0134k20@Tg00TmR0j2OTg013Tk20rTg0147j1HTg00;Vk206Tg014nk105Tg00<\j3Rk10PTg015ek30pTg00T8S00j2zTg00LVR4j2KTg00Uej4jTg016Ak20nTg016dk30mTg00Z_m<02Tg00VLj1=Tg017Ak20kTg017ik30jTg00>Gk10iTg008Bk10gTg008`k10fTg00@dj1yTg00W1k10eTg009Kk20NTg00;4k20cTg00<0k20bTg00=6k30aTg00=Uk40`Tg00X7R5j1ATg018Mj2vTg0196k10_Tg019Tk20^Tg01:5k30;Tg00RGj4}Tg009nk20ITg00XVk416Tg01:^k615Tg01;]j4aTg01<Vj1hTg01=Oj2^Tg01=lk301Tg01>dk40ZTg01?Zk40YTg01@Pk20FTg01AKk30|Tg01Anm>0{Tg01Bok20>Tg01Cjm>0zTg00YAk60yTg01Dkk20WTg00ZCk40DTg01Edk20ATg01FBk30TTg00[hk307Tg00Yck20UTg01F^k20xTg007dk20wTg00>ej4{Tg00:Qk30vTg00BEk408Tg00C0k703Tg00WSk60uTg01G;k70}Tg00[Dj8|Tg01G_k30tTg01HHk211Tg00\Hm<12Tf0R6g00^gR7+0Wp=tg00CTR8f1R9;R6p=>g00ICR:g00IcR;7R6p=7g00RbR<P7P6g00\mR=H0Dp=@f2R>%B9/^6+0Ap=e1^96-0A>p>0Sg01I4R?f3R@@0V>9<0T6p>0R10>9/^6p=F20A96=R:;p=_B0V@>9>0T?6=R:;p=Sf6RAf5RBf4RC<01@P>P9P6Dop=Z%B9/^6p=q1^96=R:;p=DP<P7P6P=H0D#Bp=p10>9/56p=YB07<96p=2f7RDB07<AB@01C@P>P9P6Dop=gg00HeRE%B6,09'5p=I%99,0>/K6p=?10969R8>p=VB07?96p=`20U<6-0@9p=]P<P9P6P=H0Dp=4%H6#1p=;&056#h#3,09p=W1^>900x6p=d%96,^9p>0s&056#h#3p=P20U<6p=G20W>9/c6p=M10BC/5@10>9/56'zp=Lg00]fR=?R96p=r%h6#3p=l10@>/59/z6p>0?%69/06p>0q20686p=NP=P8P0P1P4g00^ERFP7PEP@P>P9P6N<02p>0o%36,5Ep=C&056#hp>0=15E6p=Q20w86p=nP8P8PCP@P>C{P9P6C{p=[20N86p=JB0v896p=<P>g00DYRGg00E8RHPHg00EXRIP8P9g00`QRJP6H08g00F8RKK03p=fP9PGPHPHPIP6J0up>0MP>PGPHPHPIP9P6K0}p>00PBPGPHPHPIPCPGPHPHPIP8P@PJP>H08PKK03P9P6G|p=\B0t896p=Eg01J0-116p=kg00GTRJ@0796p=iP8P>P9P6C{p=UP8P9g00D2P6H08p=sP9PGPHPHPIP6PKK03p>0:P@PGPHPHPIP>P9P6G|p>0L1596,z>p>0]P=P8P0P1P4PFPBPCP@P>P9P6N<02p>0910>9/K6p>0JP=P=P8P8P5P1P1P@g00_mP>P9P6N<12p=uP=P8P6P1P9P>P@PCPBPAPDf8R5N<02p>0\P8P9g00_FP6H08p=xPCPGPHPHPIP@PGPHPHPIP>PKK03P9P6G|p=b%B6,09p=~15C@10>9/56'zp>0[PAPGPHPHPIPBPCP@PGPHPHPIP>P9P6G|G|p>13%36,09p>0GP8PCP@P8P>P9P6C{C{p>101096,5Ep>0~&0K<S01g00H@RG#XS02#XRK#XS03#X#X#XRF$0QS04$0OQ03$0Q$0O$17[S05&0K?S06g00FX%tD/c@,>CB045B>f9R4PBPCP@PDI0l#7p,4segsR0P4PDPBP@Do%3ARL,TBf;RM#@RN%1DRO3e10OB%9N40SRNPMPOPBP4H0RRO;m9%7N%7O':P3%3DS07,TAf<RO#@RN%15RP3e%9N9FPA'_POPPPAf:RPCSP0f=RNPOPMPPP5PAFZP6%34,T5f>RQ#@RR%1PRS3e%9R9FS5'_f?RS%1MP4PNCS%3M,TPf@RR#@RT%1ORU3eRV%9T9FUPRU;m9%7V%7U':P3%3O,TMfARU#@RV%1NRT'q'_10TM%9V'DP0fBRVPUPRPSPNPMFZP6%3QS08,TNfCRT#@%1S'q'_%1R/0QfDRW#@#9'D%3RS09,TSRXfERY#@%1U'qRZ;m9%7X%7Z':P3%3US0:,TR#7fFRZ#p%1V'DP0fGRXPZPYPWPVPRFZP6%3T,TV#7fIR[#p%1Y'DP31T96#71>>9[R\1>961T>9#7R][1>@>\]20h96P9n2001000000120000000XE8XD8P\^E8^D8P6PY%3ZR\P>O31>Y\P31D9615>9[R\15961D>9R][15@>\]20d96P9n2001000000120000000XE8XD8S0;P\^E8^D8S0<P6fMR\#pR]%1[R^P@O315]^Q0;Q0<P6fKR^#1/0[R]fOR_#@#9R`PPO315]`P2P<fNR2%t6/c\'>fLR`:049_%p>%1_R]'5fPRa#1Rb%@@#97Y2PCfQRc#1P_fSRdCSP0PBfURefTRfPdPcP_FZ]:]I]H]Q]NPa&0<<Rg#t/c`,>\B04g2^%@gRh#B%12'5%9h9Y]\PgPbP2fRRbCSg01J\P0PgPePfPdPcP_FZP@n010000000W:WIWHWQWNQ011296#t/ca,>c12>9@04b_12@>#p%1b'5%1d12C@#@#97Yc12BC%1fPbfVRgCSP3%wAB0CBgdP0PDPAfYR]fXRhfWRiPePdGgP@%w5P3%64Rj/I4Q02$0HRk&0HFRF+14Rl9?j4fZRj>0C4iP0PMPPf]Rmf\S0=f[RnP]PiGg[P6%6M/IM%6O??OlB0COmjP812QNRo#t/cmRp%6Sf^Rq#1Rr5V6XV8%6QRs00Xm%@o#6/cm%1m,0sRs'>e1>psePqPOJ0E1>qsP?Q0612RSf_Rs#1PmP6CSP012URRpfcRoP9faRtPsPmFZ]:WW12SQPrQ0=&0<?CSPhW:Q06Ppf`Rp#1PqP6CSP012VURrfdRuP9fbRvPpPqFZ]:Pr%1tPs1`>9CS12TVRr%1vRwPpP@H0BRxPrPwPpP>H0RRw;m6%7x%7w':P312WTRw%1oRxPtPCH0B#7PwPxPtP@CSP0PYPWfgRx1`BCfeRwPoPtGgP612ZY%1wPoPAH0B#712XZffRr#1PuPACSPAP6O1P0fHS0>PXfjRyPDfhRzPrPuGg%84R{Q0>,2[R|']14{|R|%;4R}3e1W}4R~%9|40SR|P=P:P{%1zR{AF{r}5d~P;n0110300020010108R~;m>%7|%7~':P3%8PR~fJS0?/2[R|']14~|R|%;PR{3e1W{PR}00s|'_P=P:P~fiR~#1R|AF|x{5d}P;n0110300020010108#7P0P^Q0?fmS0?1`MPfkS0@P~PxGgP6%8OR}12`^R`']14}`R`%;OR}3e%PO%9`5F}'_P=P:%8N%;NR}/WNflR`#1R|AF|y}3dP;n0110300020010108#7%8QR|122\R}']14|}R}%;QR|3eR{%PQ%9}5F|R|;m9%7{%7|':P3%8SR|12_2R{']14|{R{%;SR|'q'_1W|S%9{'DP0PaP_frS0A1`RSfpS0BfnS0CP`GgP6%8UR{12caR|']14{|%;U'q'_%;V/WV%8V12bc'4#9'D%8TRV12dbR|']R{14V|%;T'qR|;m9%7{%7|':P3%8WR|12fdR{']#714|{#B%;W'DP0PePffwS0D1`YWfuS0EfsS0FfqS0GGgP6%8Z12ge']#7%8X12ig'4#B%;X'DP320@96#71O>9[RW1O9620@>9#7R{[1O@>\{20r96P9n2001000000120000000XE=XD=PW^E=^D=P6%8[RW12]h#GR{P>O31OW{Q0;Q0<P6%8^12nj'4#BR{%;^RWP@O315{WQ0;Q0<P6%;\/W\RW%8\Q0=,2m'4#9R\PPO315W\%82R\12qmRW'4#6R{%H2R|+0XAMW\|%1|7V{R{eP{P8%8_S0H12sqS0I'4S0J#6S0K%H_S0L#1'0%8aS0M12psS0N'4R{#6R|/I{S0OA?|{lS0PP6%PaS0Qp+01AS0RQ0Rf~#3S0SP6EL':':Xw8Q0HP=206=6Q0M/r6P=%8bS0T/r612ovS0U#G,O912uoRb,4>#B%HfS0V#1R|'5%;eS0W/WeR{12wuS0X,4@#9'5P=P:PC%HgRu#1RW/WgS0Yp+01FS0Z#1R\p+01DS0[=F\W3dP;n0110300020010108#712xrS0\%HiS0]7MBQ0\,4B#6Q0]#1R\3V12zxS0^,4ARV#6R}/IVA?}Vl%HhS0_#1RV,0}S0`&05hS0a#lR}p+01IS0bQ0bp+01GS0c#3S0dQ0`EL':':]M]<];]K]J]OP9%8c=R=712vtS0`#G,O7Q0U#p%HdS0e#1'5%PfS0f%@b#95Y|p+01ES0g#1R|p+01CS0hQ0W5F|5d{#712rwS0i#t/cuQ0i#@#6;VW%6xRW/IxA?WxlRu10W\Rw%PiS0jp+01HR{Q0Z#3S0k,0{S0l/5wH0?Rw':PnPuPwPjP8Q0c#1Rw,0W20qzVRWP}P6P6Q0dPWELXV8Q0j=F\wRWQ0g=Fw\Rw<0p9%7W%7w'zQ0010V}%1{R}'DQ0Z,0}/DV%6~R}%;]S00'0Rw%P]S0dQ0b#1S0m,0}R}P}%3{S0nPwELP6Q00Q0d'0Q0m'DQ0;Q0<P6%;nRw%PnS0o'0R}p+01KS0p#1S0qP9O3Q0q,5}Q0@,2`S0r#GR},O7%3}R],KES0s2068ERWP}P]%N]H0oP4CjS0tQ0s%8mR]=R=7%3]S0u=R8ES0vP=P8&0P=S0wP1&0P8S0x%39%36'>1r9620n9640mXv=Xa=S0yP]Q0uQ0u#NP7PEPWN<02PMCjS0zQ0vp+01MS0{#=S0|Q0{#CS0}%8sS0~#=S10Q0~#CS11&0=pRW#=S12%CWS13Q0GQ0B'2#GRW#=S14%CWS1520kkFS161KEkS17%QF1KElS18[S19[S1:%QkRWg01K9R1B0jkF9UWXS1;%Ql\1S1<^XWS1=P6P>O1S1>Q1<P>P5O1S1?Q19P6PCO1S1@Q18p-0S1A&0<JRW&0KJS1B%nCRJP>&0i8R1P9%n@S1CD[&0g8S1D&0f8RFPFQ02#JR}%yGS1E#JS1F'<S1G%JKRK&0eHRH20N8GRu/<}S1HQ1F'<S1I1<uKS1J5fF20MFA600FE\20cFIRIP6P>206:;20b6>#7dB0a8E9H0`R|b>b?b@X18X28X38X48WSQ1A109>S1K/5@Q1KP@109CPBH0?[^18^28^38^48]SP6fx#6S1Kp+01XS1L#1S1M'0S1Np+01W#3S1OQ1K%;zS1P'0S1Q3YQ1M%PzS1RQ1PQ1KPOO6b=b0b0b6b6b0bCbBb8b7bPb5bRb9WRP6O1Q0mQ0c'0Q00'DQ0;Q0<P6Q0qQ0b'0S0<PwP9O3Q0</5wQ0tQ0sQ0zQ0vQ0|Q0}Q10Q11Q12Q13Q14Q15Q16Q1:Q1;Q1=Q1>Q1<Q1?Q19Q1@Q18Q1A%A7S1@#AS19,v8S1?&0_G-0^8S15Q1@,v8S1@60;81v87S14'E'E#k/iWQ1BQ1CP>%nBS13?UB1P9AUJB1D[Q1DPFPFQ02#yS02#X#JS12,<KS11P}PHPFQ12Q02#JS10's-0:FS0}PH20MFDQ1JQ10'<Q1H5fF600FH0LE\PIP|b>b?b@X18X28X38X48XA8WSQ1A10>CR7/591>BC107B10>@S1J60]D[[^18^28^38^48^A8]SP6Q1QQ1RQ1N3Yp+01VQ1OQ1MQ1PQ1KPOp+01@S1KO8b=b0b0b6b6b0bCbBb8b7bPb5bRb9WRP6O1n200100000021100011000b<P{PhJ0EC}C}Q0\#@R7#6S1P/I7Q1P??7lQ1P/0\R\Q0jP{Q0l/5\H0?':':eWMW<W;WKWJWO%8dS0l%A6'r%A9%Gb'O%A>Q0X'4#BQ0W'5Q0Y%A@Q0i'4#9'5AR:;;Q0^%ABR\Q0_3MQ0^,4\#6;VVPzp+01JRVQ0cPAPn%GzS0_,OAQ0_#3R\,KLPAPL%NLS0YQ0_P\%N\S0WJ09%AAS1PQ0_#AS1M'O&0HGRG10\G60JLS1OQ1P106GS1RXa8R7PLO1P7PAPLQ0YCuQ1MP7P\O1P7Q0_P\Q0WCuJ09PCCjQ1O%8jS1O%ADS0W'rQ1O#3R\Q07;VGS0_Q0wQ0xQ0yQ1OP\%N\Q0WP7Q07O1P7PDQ07Q07#NCuN90\PACjQ0_%=5%C5Q0p#=Q0p#3S0_#Q%=]Q0u#Q&0=qR\#=%C\Q0C#GR\#=%C\Q16Q1:Q1;Q1=PWQ1B%n>S0u?U91Q1DPFPF20I8GR\,<u1<}\'xPH1xu}-0:FDbPIP|b>b?b@X18X28Q1R109G'K1K9>[^18^28P6Q0A#G#3Q09P4O3b=b0b]b`bCbBb8b7bPb5H16J1514AzR\#wPVQ0c%6\S0A/~\Q0A%9\PVEL':P314D~R\#wQ0pP{%6\S0A/~\Q0A%9\Q0pEL145yR\#6S0A/I\Q0A??\lQ0A/0wR\Q0op+01LS0oQ0o%3VP\EL':':P6Q0@,44#wP314P`R\#6S0A/I\Q0A??\lp+01OS0AQ0oQ0?,4MR\#6S1R/~\Q1R%9\Q0AELQ0C,4OR\#6S1R/I\S07Q1R??\lQ1R%HsS0W#1'0S1R/Wsp+01PR\P\p+01NS1M#3S0YQ1RI0[':':[P6Q07foS1R,4NS1Q#6Q1Q;?lp+01RS1QQ0AQ0B,4QRQ#6S1N/~QQ1N%9QQ1QELQ0G,4SRQ#6S1N/IQQ1N??QlS1AQ1N%;v'0RQ/Wvp+01SS1NQ1Np+01QRv#3S0|PQI0[RQ':P>Q1APQP9%ASS1AQ0G#GS0G#AS0v'O%3SRQQ0G#3S0z/0G80JGS0sQ1AP7PQO1P7PSPQ%NQCuQ0vP7Q0zO1P7Q0GQ0zQ0z#NCuJ09PNCjQ0s%8oRo%ARRN'r%3oRQQ09;VGRGQ0wQ0xQ0yPoPQ%NQPNP7Q09O1P7PRQ09Q09#NCuN90\PSCjPG%=UQ0:#Qp+01TRU#=%CU%8rRr#=%Cr&0=xRx#=%CxQ0D#GRx#=%CxQ16Q1:Q1;Q1=Q19#ARx#ARr#A,v8RU1v8rS19Q1@'E'E#k1v8xRxQ15Q1?60;8RrQ14'E'E,EU#k/iW'iQ1B%nD9U1CP>%nAS0D?U51P9P1PB%n5P@P1D[D[Q1DPFQ11Q1E#XRU#X#JRG,<u5fF%yU#JRS,<u=fFK600FPHPFQ1G=fFSPHPFPFPGP}PHPFQ0}PHQ1I=fFKQ10,<KQ1H5fF600FH0LE\K13PIP|b>b?b@X18X28X38X48XA8XT8X^8X_8P@PB106AP6PDP@ELQ1J/55155@1>5D10CBR7PAPDPDP5P7EL[[[[^18^28^38^48^A8^T8^^8^_8P6f{,4[R[#9%B[p+01ZR5p+01[RN#3p+01]%P`%;`%6[PPPYPZQ0[O<b=b0b]b`bCbBb8b7bPb5C}C}WfW\W[P9P6O2n2001000000121000000W9P9P6O2n2001000000121000000bUQ1P12~z'4Rz#6RY/IzA?YzlQ00,0YRYQ0dPVPVQ0nPYEL':':eWMW<W;WKWJWOXn=P6O1n0110000020111100P6PDPBP@PTP>O6bObDQ0IQ0HQ0L3MRDP6J0EQ0KQ0J'IQ0KQ0J;?lPD%P_Q1Kf}R_#3Ca':':RDePDP3Q0OQ0PQ0NQ0M%Ha3MQ0QQ0RQ0SCa':P0PtPpQ0[1`cap+01BRcQ1KP_GgP6Q0TQ0`'4R_#6/I_Q0lQ0U'4R_#6??_lQ0UQ0lQ0e3M%PdQ0[%3cCa':P3%8fR3/4bRd#6??dlQ0V9Mb3Q0fQ0gQ0h#3CaP0Q0XP{1`efQ0ZQ0[PcFZP6%8gQ0i'4Rg#6??glQ0\%8iQ0]3MQ0jP{Q0kCaQ0ag01KUR{P{%;j%l6Q1O12y~'4#93YP=P:%8n%h9-0GwQ0qQ0</^w3dP;n0110300020010108#7Q0rQ0=#8Q0=#H3M%l>Q0{Q0_CaP0P{Q05P@P9Q1RQ0C'2R{Q1Q<01qRwQ0~Q0W5M{R{P6H0ZPwP{P9P6H0Yn0110300022010010520104101Q1MQ0oPVDo]L]<];P6%;mRm20F96#lQ0?/2`,4]#9R]3YP=P:%8qS0W%;qRq20F>9#h+0GQ1M#1R`Q0o=F`qRV3dP;n0110300020010108#7P{20F@>#lP\Q0YCaP0PCQ0BQ1R'2RwQ1N<01sRs%8pRn%Hp5MwR~P@PvQ0AQ0{%GwRw,On%3nRj%3wRg'KRfPnPj%NjPwPg%NgJ09PZCjRZPf%=\Rg%C\Rw%=ARj%QLRL%=oRo%QQRQftQ0F'2#GRn#=Re%CnRnQ16Q1:Q1;Q1=Q1>Q1<Q17P@P6PCO2WUR3Q17Q18]URbQ1@Q14'ERd,Er,ExRr#k/iWQ1BP1PCQ0u?UCJP9P1PCQ1CPCP1I10D[Q1DPFPF20I8EREQ1E#yR_#X#JRaQ12'<PHPFPFQ02#y#JRt,<a,suPHPFPFQ12PtPHAfFEuS12E\DbE\PIP|b>b?b@X18X28X38X4820~@910C@Rt,>915@CRD%Q@S02[[[^18^28^38^48P6%8yRYfzRzfy'2RP'4R[#6S1E%HyRy#1S14%B[AMPYyRyPXP^P2O7b=b0b6b6b0bCbBR2b8b7b5PZPfPgPwPjPLPoPQPePnQ16Q1:Q1;Q1=Q1>Q1<P3PbQ1?/EdRd,Ex#k/iWQ1BQ1C9U1BP>Q139U1BP9P1PBPJPBP1D[D[Q1DPFPF1<aS20I8kQ0460|8Rk'xPHPFPF1<aG,suPHPFPF1<G}PSPHQ1H/xk-0:FRSE\DbDbPIP|b>b?b@X18X28X38X48XA81KtlAV9B@15tB10@CRt/Kl[[[^18^28^38^48^A8P6Q1E%9[Q14Q08PyPTP^POO8b=b0b6b6b0bCbBROb8b7b5PZPfPgPwPjPLPoPQPePnQ16Q1:Q1;Q1=Q1>Q1<P3PbQ15>0;8x/Ed#k/iWQ1BAUJ@1PCP1P9Q0uD[Q1DPFPFQ1FQ03#JRd'<,suPHPFPFPKPdPHPFPFPEQ1F/<KPHQ12E\E\DbPIP|b>b?b@X18X28X38X48AV69@%QtQ02[\D[^18^28^38^48P6%15R5%Bz%6zRDPNQ0@fvQ0CO7b=b0b6b6b0bCbBRtb8b7b5PZPfPgPwPjPLPoPQPePnQ16Q1:Q1;Q1=Q1>Q1<P3PbQ19/Er#k/iWQ1BQ0D?U@1P>PJP9Q139U1AD[Q1DPFPF1<Kd,suPHPFPF%J_R_,<d%JURUPHPFPF1s_}PHPFPF1<KU/xkPHPSDbDbE\DbPIP|b>b?b@X18X28X38X48XA8XT8AV6>BAYABC1>A@B0JBAl1K7l[[[[^18^28^38^48^A8^T8P6P5Q1L%9zPDp+01Y#3PNQ0@Q0EPcQ0?O:b=b0b6b6b0bCbBRcb8b7b5P6PiN>0{P0PCPsP~P@H0ZPvQ0AQ0{DoeWLW<W;Xt8XD=P9P6O220>96#l=Ym]P=P:Q0W20>>9#h-0Gq?d`VP;n0110300020010108#7P{20>@>#lP\Q0YCaP0PsP~PCP@PvQ0AQ0{PZPf%=BR\%CBRB%=vR{Q0|#QR;P2b8b7b5PZPfP\PBP{P;POb8b7b5PZPfP\PBP{P;Ptb8b7b5PZPfP\PBP{P;Pcb8b7b5P6PiN>0zP0PsP~PCP@H0YPvQ0AQ0{DoeWLW<W;Xj8Xo=P9P6O2n0110600022110010521104101PMP^P9O3buP0Q0^Q0p1`hiQ0bQ0cQ0gFZeWLW\P9P6O2n2001000000121000000W9W[P9P6O2n2001000000121000000bgbMb;b9bKb9bJb9WKWJP9P6O2n2001000000121000000bGW;WGP9P6O2n2001000000121000000bGW<WGP9P6O2n2001000000121000000bGbZW:WGP9P6O2n2001000000121000000b:W:WZWWXp?PpP4J0ybbWdWiWhP9P6O2n2001000000121000000W9P9P6O2n2001000000121000000W:WIWHWQWNWlXm<P9P6O2n10110200020021107102Q0>PXP>P6PRO5bIb9bHb9bYb9WHWYP9P6O2n2001000000121000000bFWIWFP9P6O2n2001000000121000000bFW:WFP9P6O2n2001000000121000000bFWcWFWQWNXs8Xq8XE=WrXV8WWWeWko"). Qed.
End WithSegs.

End ArtStk.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC.
Module As0StepLib.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StepTac OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.WalkTac.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Section FPX. Context {fx : PropExec.FPState}.

Lemma step_fence : forall segs regs pc mem rom w a b c d e,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Fence a b c d e, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) = MachineOk (mkst regs (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w a b c d e Hfetch Hecall Hdecode.
  step_pipeline Hfetch Hecall Hdecode.
  rewrite ?b_npc4; reflexivity.
Qed.

Lemma step_fencei : forall segs regs pc mem rom w a b c,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (FenceI a b c, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) = MachineOk (mkst regs (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w a b c Hfetch Hecall Hdecode.
  step_pipeline Hfetch Hecall Hdecode.
  rewrite ?b_npc4; reflexivity.
Qed.

Lemma bytes_le_to_Z_4 : forall v : word, (bv_unsigned v < 2 ^ 32)%Z ->
  bytes_le_to_Z (word_to_le_bytes 4 v) = bv_unsigned v.
Proof.
  intros v Hv. rewrite bytes_le_N. change (2 ^ (8 * Z.of_nat 4))%Z with (2^32)%Z.
  apply Z.mod_small. pose proof (u64_range v). lia.
Qed.

End FPX.

(* [comment removed for export] *)
Ltac stepfence F D :=
  chain_step; [reflexivity | eapply step_fence; [exact F | reflexivity | exact D] | step_simpl].

(* [comment removed for export] *)
Ltac rwH :=
  repeat match goal with
         | H : getr ?rg ?i = _ |- context [getr ?rg ?i] => rewrite !H
         end.

(* [comment removed for export] *)
Ltac addr_lit lit :=
  match goal with |- rdn _ _ ?ad _ = _ =>
    replace ad with lit by (gres; rwH; imm_norm; apply bv_eq; vm_compute; reflexivity) end.
Ltac mlb F D lit HYP :=
  chain_step; [reflexivity | eapply step_lb; [exact F | reflexivity | exact D | addr_lit lit; exact HYP] | step_simpl; vnorm].
Ltac mlbu F D lit HYP :=
  chain_step; [reflexivity | eapply step_lbu; [exact F | reflexivity | exact D | addr_lit lit; exact HYP] | step_simpl; vnorm].
Ltac mlw F D lit HYP :=
  chain_step; [reflexivity | eapply step_lw with (bs := word_to_le_bytes 4 _); [exact F | reflexivity | exact D | addr_lit lit; exact HYP | apply bytes_le_to_Z_4; first [lia | rewrite u_Z2bv by lia; lia | vm_compute; first [reflexivity | lia] ] ] | step_simpl; vnorm].
Ltac mld F D lit HYP :=
  chain_step; [reflexivity | eapply step_ld with (bs := word_to_le_bytes 8 _); [exact F | reflexivity | exact D | addr_lit lit; exact HYP | exact (bytes_le_to_Z_8 _) ] | step_simpl; vnorm].

End As0StepLib.
Module ArtRunsMem.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StepTac OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.WalkTac OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056.MemSplit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0035.ArtMem OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0035.ArtRuns.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma art_le_bytes_zero : forall n, (n <= 8)%nat -> word_to_le_bytes n (Z_to_bv 64 0) = repeat (Z_to_bv 8 0) n.
Proof. intros n Hn. do 9 (destruct n as [|n]; [vm_compute; reflexivity|]). exfalso. lia. Qed.

Lemma art_store_ok_ext : forall segs n (m1 m2 : word -> option byte) (a : word),
  bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
  (forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat n -> m1 x = m2 x) ->
  store_ok segs m1 a n = store_ok segs m2 a n.
Proof.
  intros segs n. induction n as [|n IH]; intros m1 m2 a Hnw Hext; [reflexivity|].
  cbn [store_ok]. unfold wview. rewrite (Hext a) by (pose proof (u64_range a); lia).
  destruct n as [|n']; [reflexivity|].
  assert (Hu1 : bv_unsigned (a + 1) = bv_unsigned a + 1) by (apply u_add1; rewrite !Nat2Z.inj_succ in Hnw; lia).
  rewrite (IH m1 m2 (a + 1)%bv) by (rewrite Hu1; first [rewrite !Nat2Z.inj_succ in *; lia | intros x Hx; apply Hext; rewrite !Nat2Z.inj_succ in *; lia]).
  reflexivity.
Qed.

Section WithSegs.
Variable segs : list Segment.
#[local] Abbreviation cell := (cell segs).
#[local] Abbreviation wr := (wr segs).
#[local] Abbreviation wok := (wok segs).

(* [comment removed for export] *)
Lemma art_cell_agree : forall (M M' : word -> option byte) a (n : nat) v,
  (forall x : word, a <= bv_unsigned x < a + Z.of_nat n -> M' x = M x) -> 0 <= a -> a + Z.of_nat n < 2 ^ 64 ->
  cell M a n v -> cell M' a n v.
Proof.
  intros M M' a n v AG Ha Hn C. unfold ArtMem.cell in *. rewrite <- C.
  apply rdn_ext. rewrite art_u_lit by lia. lia.
  intros x Hx. rewrite art_u_lit in Hx by lia. apply AG. lia.
Qed.

(* [comment removed for export] *)
Lemma art_wr_of_defined : forall (M : word -> option byte) a n, 0 <= a -> a + n < 2 ^ 64 ->
  (forall x : word, a <= bv_unsigned x < a + n -> M x <> None) -> wr M a n.
Proof.
  intros M a n Ha Hn D d k Hd Hk. apply store_ok_of_all.
  - rewrite art_u_lit by lia. lia.
  - intros x Hx. rewrite art_u_lit in Hx by lia. unfold wview. destruct (M x) eqn:E; [discriminate|]. exfalso. apply (D x); [lia|exact E].
Qed.

(* [comment removed for export] *)
Lemma art_wr_of_wview : forall (M : word -> option byte) a n, 0 <= a -> a + n < 2 ^ 64 ->
  (forall x : word, a <= bv_unsigned x < a + n -> wview segs M x <> None) -> wr M a n.
Proof.
  intros M a n Ha Hn D d k Hd Hk. apply store_ok_of_all.
  - rewrite art_u_lit by lia. lia.
  - intros x Hx. rewrite art_u_lit in Hx by lia. apply D. lia.
Qed.
Lemma art_wr_wview : forall (M : word -> option byte) a n, 0 <= a -> a + n < 2 ^ 64 -> wr M a n ->
  forall x : word, a <= bv_unsigned x < a + n -> wview segs M x <> None.
Proof.
  intros M a n Ha Hn W x Hx.
  pose proof (W (bv_unsigned x - a) 1%nat ltac:(lia) ltac:(cbn; lia)) as OK.
  replace (a + (bv_unsigned x - a)) with (bv_unsigned x) in OK by lia. rewrite Z_to_bv_bv_unsigned in OK.
  apply (store_ok_all segs M 1 x); [pose proof (u64_range x); cbn; lia | exact OK | cbn; lia].
Qed.
Lemma wr_join : forall (M : word -> option byte) a n m, 0 <= a -> 0 <= n -> 0 <= m -> a + n + m < 2 ^ 64 ->
  wr M a n -> wr M (a + n) m -> wr M a (n + m).
Proof.
  intros M a n m Ha Hn Hm Hb W1 W2. apply art_wr_of_wview; [lia|lia|]. intros x Hx.
  destruct (Z_lt_le_dec (bv_unsigned x) (a + n)) as [L|G].
  - apply (art_wr_wview M a n); [lia|lia|exact W1|lia].
  - apply (art_wr_wview M (a + n) m); [lia|lia|exact W2|lia].
Qed.

(* [comment removed for export] *)
Lemma art_zfill_grows : forall M r len, mem_grows M (art_zfill M r len).
Proof. intros M r len x Hx. unfold art_zfill. destruct ((r <=? bv_unsigned x) && (bv_unsigned x <? r + len)); [discriminate|exact Hx]. Qed.
Lemma wr_zfill : forall M r len, 0 <= r -> r + len < 2 ^ 64 -> wr (art_zfill M r len) r len.
Proof. intros M r len Hr Hl. apply art_wr_of_defined; [lia|lia|]. intros x Hx. rewrite art_zfill_in by lia. discriminate. Qed.
Lemma wr_zfill_other : forall M r len a n, wr M a n -> wr (art_zfill M r len) a n.
Proof. intros. eapply wr_grows; [apply art_zfill_grows|assumption]. Qed.
Lemma wok_zfill_other : forall M r len a n, wok M a n -> wok (art_zfill M r len) a n.
Proof. intros. eapply wok_grows; [apply art_zfill_grows|assumption]. Qed.
Lemma cell_zfill_other : forall M r len a n v, 0 <= a -> a + Z.of_nat n < 2 ^ 64 -> apart r len a (Z.of_nat n) ->
  cell M a n v -> cell (art_zfill M r len) a n v.
Proof. intros M r len a n v Ha Hn A C. eapply art_cell_agree; [|exact Ha|exact Hn|exact C]. intros x Hx. apply art_zfill_out. unfold apart in A. lia. Qed.
Lemma cell_zfill_zero : forall M r len a n, (n <= 8)%nat -> 0 <= a -> a + Z.of_nat n < 2 ^ 64 -> r <= a -> a + Z.of_nat n <= r + len ->
  cell (art_zfill M r len) a n 0.
Proof.
  intros M r len a n Hn8 Ha Hn Hlo Hhi. unfold ArtMem.cell. rewrite art_le_bytes_zero by exact Hn8.
  apply rdn_const. rewrite art_u_lit by lia. lia.
  intros x Hx. rewrite art_u_lit in Hx by lia. apply art_zfill_in. lia.
Qed.

(* [comment removed for export] *)
Lemma art_reveal_grows : forall M lo hi, mem_grows M (art_reveal M lo hi).
Proof. intros M lo hi x Hx. unfold art_reveal. destruct ((lo <=? bv_unsigned x) && (bv_unsigned x <? hi)); [|exact Hx]. destruct (M x); [discriminate|contradiction]. Qed.
Lemma wr_reveal : forall M lo hi, 0 <= lo -> hi < 2 ^ 64 -> wr (art_reveal M lo hi) lo (hi - lo).
Proof. intros M lo hi Hlo Hhi. apply art_wr_of_defined; [lia|lia|]. intros x Hx. apply art_reveal_defined. lia. Qed.
Lemma wr_reveal_other : forall M lo hi a n, wr M a n -> wr (art_reveal M lo hi) a n.
Proof. intros. eapply wr_grows; [apply art_reveal_grows|assumption]. Qed.
(* [comment removed for export] *)
Lemma cell_reveal_other : forall M lo hi a n v, 0 <= a -> a + Z.of_nat n < 2 ^ 64 -> apart lo (hi - lo) a (Z.of_nat n) ->
  cell M a n v -> cell (art_reveal M lo hi) a n v.
Proof. intros M lo hi a n v Ha Hn A C. eapply art_cell_agree; [|exact Ha|exact Hn|exact C]. intros x Hx. apply art_reveal_out. unfold apart in A. lia. Qed.

(* [comment removed for export] *)
Lemma cell_unmap_other : forall M r len a n v, 0 <= a -> a + Z.of_nat n < 2 ^ 64 -> apart r len a (Z.of_nat n) ->
  cell M a n v -> cell (art_unmap M r len) a n v.
Proof. intros M r len a n v Ha Hn A C. eapply art_cell_agree; [|exact Ha|exact Hn|exact C]. intros x Hx. apply art_unmap_out. unfold apart in A. lia. Qed.
Lemma wr_unmap_other : forall M r len a n, 0 <= a -> a + n < 2 ^ 64 -> apart r len a n -> wr M a n -> wr (art_unmap M r len) a n.
Proof.
  intros M r len a n Ha Hn A W d k Hd Hk. pose proof (W d k Hd Hk) as OK.
  destruct (Nat.eq_dec k 0) as [->|NZ]; [reflexivity|].
  rewrite (art_store_ok_ext segs k (art_unmap M r len) M); [exact OK| |]; [rewrite art_u_lit by lia; lia|].
  intros x Hx. rewrite art_u_lit in Hx by lia. apply art_unmap_out. unfold apart in A. lia.
Qed.

End WithSegs.

End ArtRunsMem.
From Stdlib Require ZArith NArith List Lia Bool. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout State Run.
Module AsanStartLoops.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_AsanStartLoops () := "C47Corelib7Program6Basics4flipC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00C46Stdlib5Lists4List6nth_okC46Stdlib5Lists4List:firstn_nilC47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List=repeat_lengthC56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1N02C45stdpp9bitvector;definitions7bv_wrapI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z9mod_smallC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions@Z_to_bv_unsignedK46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I45stdpp9bitvector;definitions2bv00C56Stdlib6ZArith6BinInt1Z3addc59OSSVerify5KrLib7Mh_0035>AsanStartLoops5u_litC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6v_addiC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0035>AsanStartLoops:v_addi_litC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4btgtC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC49OSSVerify5KrLib8PropExec4c_eqC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notK47Corelib7Numbers7BinNums8positive01C47Corelib4Init5Logic7f_equalC56Stdlib6ZArith6BinInt1Z6moduloC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega5Tauto8GFormula03K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic5False00C47Corelib4Init3Nat3addK45stdpp9bitvector;definitions2bv01C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0035>AsanStartLoops8env_postC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC46Stdlib9micromega;ZifyClasses;rew_iff_revC49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC49OSSVerify5KrLib8PropExec6regupdC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbI47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC45stdpp9bitvector;definitions9bv_signedC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C56Stdlib6ZArith6BinInt1Z7add_0_rK46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing5PExpr05C59OSSVerify5KrLib7Mh_00387SeqExec?bytes_le_to_Z_8C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7step_ldC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec9step_addiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387SeqExec9getr_zeroC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions5bv_eqC47Corelib4Init5Logic9False_indC49OSSVerify5KrLib8PropExec9getr_sameC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec:getr_otherC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec;step_bne_ftC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib7Mh_00306CatSim6msteps01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib7Mh_00306CatSim6msteps02C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00C59OSSVerify5KrLib7Mh_00385Hoare:regs_agreeC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02K47Corelib4Init5Logic2or01K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C47Corelib4Init5Peano2ltK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05C49OSSVerify5KrLib8PropExec<c_eq_0_falseC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec;step_bne_tkC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses5mkrelc59OSSVerify5KrLib7Mh_0035>AsanStartLoops8btgt_litC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes7nat_indC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses3injI47Corelib4Init9Datatypes3nat00C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addc59OSSVerify5KrLib7Mh_0035>AsanStartLoops:signed12_0C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01C56Stdlib6ZArith4Znat5Nat2Z6inj_ltC56Stdlib6ZArith4Znat5Nat2Z8inj_succC46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib7Numbers7BinNums1N00I47Corelib7Numbers7BinNums8positive00c59OSSVerify5KrLib7Mh_0035>AsanStartLoops:signed12_8C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02c59OSSVerify5KrLib7Mh_0035>AsanStartLoops;signed13_m8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk>mem_grows_reflC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0035>AsanStartLoops7cellrelC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387CatExec6wbytesC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC59OSSVerify5KrLib7Mh_00387CatExecDlength_N_to_le_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387CatExec<wbytes_belowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387CatExec<wbytes_aboveC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk<wbytes_growsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk?mem_grows_transC1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C59OSSVerify5KrLib7Mh_00387CatExec7byte_atC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses9and_morphC49OSSVerify5KrLib8PropExec7rdn_extC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula06C56Stdlib6ZArith4Znat5Nat2Z6inj_leC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC59OSSVerify5KrLib7Mh_00387StoreOk=store_ok_monoC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec8u8_rangeC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List8app_nth1C46Stdlib5Lists4List<length_skipnC47Corelib5Lists7ListDef5skipnC47Corelib4Init3Nat3subC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specK46Stdlib9micromega7EnvRing5PExpr04c59OSSVerify5KrLib7Mh_0035>AsanStartLoops7pn_postC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0035>AsanStartLoops:cellrel_rdC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec8step_lbuC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0035>AsanStartLoops8c_eq_litC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec;step_beq_ftC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387CatExec;byte_at_lenC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthC46Stdlib5Lists4List9nth_skipnC56Stdlib5Arith8PeanoNat3Nat7add_0_rC47Corelib4Init9Datatypes3appC59OSSVerify5KrLib7Mh_00387CatExec>nth_lt_byte_atC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC46Stdlib5Lists4List6nth_InC46Stdlib5Lists4List;skipn_skipnc59OSSVerify5KrLib7Mh_0035>AsanStartLoops6byte_uC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepc59OSSVerify5KrLib7Mh_0035>AsanStartLoops>cellrel_wbytesC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec;step_beq_tkC1?~~~~~~~~~~~~~~~C35stdpp7tactics<f_equal_helpc59OSSVerify5KrLib7Mh_0035>AsanStartLoops:cellrel_stC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387SeqExec:step_sd_atC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes8list_indC56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxc59OSSVerify5KrLib7Mh_0035>AsanStartLoops;signed12_m1C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00c59OSSVerify5KrLib7Mh_0035>AsanStartLoops:signed12_1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0035>AsanStartLoops<signed13_m12C1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPX_1. Context {fx : PropExec.FPState}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma u_lit : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. lia. Qed.

Lemma v_addi_lit : forall a k, 0 <= a < 2 ^ 64 -> v_addi (Z_to_bv 64 a) k = Z_to_bv 64 (a + k).
Proof. intros a k Ha. unfold v_addi. rewrite u_lit by lia. reflexivity. Qed.

Lemma btgt_lit : forall a k, 0 <= a < 2 ^ 64 -> btgt (Z_to_bv 64 a) k = Z_to_bv 64 (a + k).
Proof. intros a k Ha. unfold btgt. apply v_addi_lit. exact Ha. Qed.

Lemma c_eq_lit : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
  c_eq (Z_to_bv 64 a) (Z_to_bv 64 b) = Z.eqb a b.
Proof. intros a b Ha Hb. unfold c_eq, bv_eqb. rewrite !u_lit by lia. reflexivity. Qed.

Lemma reg_neq : forall a b : Z, 0 <= a < 32 -> 0 <= b < 32 -> a <> b -> (Z_to_bv 5 a : reg) <> Z_to_bv 5 b.
Proof.
  intros a b Ha Hb Hne Heq. apply (f_equal bv_unsigned) in Heq.
  rewrite !Z_to_bv_unsigned in Heq. unfold bv_wrap in Heq. change (bv_modulus 5) with 32 in Heq.
  rewrite !Z.mod_small in Heq by lia. lia.
Qed.
End FPX_1.


(* [comment removed for export] *)
Ltac rif :=
  repeat match goal with
  | |- context [if bv_eqb ?a ?b then ?u else ?v] =>
      lazymatch a with
      | @BV _ _ _ =>
          lazymatch b with
          | @BV _ _ _ =>
              let c := eval vm_compute in (bv_eqb a b) in
              lazymatch c with
              | true => change (if bv_eqb a b then u else v) with u
              | false => change (if bv_eqb a b then u else v) with v
              end
          end
      end
  end.

(* [comment removed for export] *)
Ltac pc_is v :=
  lazymatch goal with
  | |- msteps _ (mkst _ (Z_to_bv 64 ?q) _ _) _ => first [constr_eq q v | replace q with v by lia]
  end.
Section FPX_2. Context {fx : PropExec.FPState}.


(* [comment removed for export] *)
Lemma signed12_0 : bv_signed (0 : bv 12) = 0.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanStartLoops ()) ["FPX_2"] "p;2p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9p1000Np4p7210R1p1001:p4p710R0p8P1p1001Xp4p710p8p1002_p4p710P0p8p1003:p4p710p1003Yp4p710p8p10045p4p710P0p8g00A;j20Tg00HWg00I5'0o"). Qed.
Lemma signed12_1 : bv_signed (1 : bv 12) = 1.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanStartLoops ()) ["FPX_2"] "p;1p;2p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9p1000Np4p7210R1p1001:p4p710R0p8P1p1001Xp4p710p8p1002_p4p710P0p8p1003:p4p710p1003Yp4p710p8p10045p4p710P0p8g005Xj11Tg00A;j20Tg00HWg00IS#1'0o"). Qed.
Lemma signed12_8 : bv_signed (8 : bv 12) = 8.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanStartLoops ()) ["FPX_2"] "p;1p;2p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9p1000Np4p7210R1p1001:p4p710R0p8P1p1001Xp4p710p8p1002_p4p710P0p8p1003:p4p710p1003Yp4p710p8p10045p4p710P0p8g0053j10Tg005Xj12Tg00A;j21Tg00HWg00IS#0#0#0#2'1o"). Qed.
Lemma signed12_m1 : bv_signed (4095 : bv 12) = -1.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanStartLoops ()) ["FPX_2"] "p;1p;2p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9p1000Np4p7210R1p1001:p4p710R0p8P1p1001Xp4p710p8p1002_p4p710P0p8p1003:p4p710p1003Yp4p710p8p10045p4p710P0p8g00V6j11Tg00A;j20Tg00HWg00IS#1'0o"). Qed.
Lemma signed13_m8 : bv_signed (8184 : bv 13) = -8.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanStartLoops ()) ["FPX_2"] "p;1p;2p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9p1000Np4p7210R1p1001:p4p710R0p8P1p1001Xp4p710p8p1002_p4p710P0p8p1003:p4p710p1003Yp4p710p8p10045p4p710P0p8g0053j10Tg00V6j12Tg00A;j21Tg00HWg00IS#0#0#0#2'1o"). Qed.
Lemma signed13_m12 : bv_signed (8180 : bv 13) = -12.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanStartLoops ()) ["FPX_2"] "p;1p;2p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9p1000Np4p7210R1p1001:p4p710R0p8P1p1001Xp4p710p8p1002_p4p710P0p8p1003:p4p710p1003Yp4p710p8p10045p4p710P0p8g00Scj13Tg0053j10Tg00V6j12Tg00A;j21Tg00HWg00IS#3#0#0#2'1o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section EnvLoop.
  Variable SEGS : list Segment.
  Variable x : Z.
  Variables w1 w2 w3 : bv 32.
  Hypothesis Hx : 0 <= x /\ x + 12 < 2 ^ 64.
  Hypothesis F1 : fetch_word SEGS (Z_to_bv 64 x) = Some w1.
  Hypothesis F2 : fetch_word SEGS (Z_to_bv 64 (x + 4)) = Some w2.
  Hypothesis F3 : fetch_word SEGS (Z_to_bv 64 (x + 8)) = Some w3.
  Hypothesis E1 : is_ecall w1 = false.
  Hypothesis E2 : is_ecall w2 = false.
  Hypothesis E3 : is_ecall w3 = false.
  Hypothesis D1 : decode_any w1 = Some (Load SZ8 true 10 9 0, 4%Z).
  Hypothesis D2 : decode_any w2 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
  Hypothesis D3 : decode_any w3 = Some (Branch BC_NE 10 0 8184, 4%Z).

  Variable M : word -> option byte.
  Variable rom : word -> option byte.
  (* [comment removed for export] *)
  Variable e : Z.
  Variable envc : nat.
  Variable ptr : nat -> word.
  Hypothesis He : 0 <= e /\ e + 8 * Z.of_nat envc + 16 < 2 ^ 64.
  Hypothesis Rk : forall k, (k < envc)%nat ->
    rdn SEGS M (Z_to_bv 64 (e + 8 * Z.of_nat k)) 8 = Some (word_to_le_bytes 8 (ptr k))
    /\ bv_unsigned (ptr k) <> 0.
  Hypothesis Rn : rdn SEGS M (Z_to_bv 64 (e + 8 * Z.of_nat envc)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).

  Definition env_post (regs regs' : bvmap 5 word) : Prop :=
    getr regs' 9 = Z_to_bv 64 (e + 8 * Z.of_nat envc + 8)
    /\ getr regs' 10 = Z_to_bv 64 0
    /\ regs_agree (fun r => r = 9%bv \/ r = 10%bv) regs regs'.

  Lemma env_loop : forall n k regs,
    (k + n = envc)%nat ->
    getr regs 9 = Z_to_bv 64 (e + 8 * Z.of_nat k) ->
    exists regs',
      msteps SEGS (mkst regs (Z_to_bv 64 x) M rom) (mkst regs' (Z_to_bv 64 (x + 12)) M rom)
      /\ env_post regs regs'.
  Proof.
    induction n as [|n IH]; intros k regs Hkn H9.
    - (* last iteration: reads the NULL *)
      assert (k = envc) by lia. subst k.
      eexists. split.
      + eapply mst_step; [reflexivity| |].
        { eapply (step_ld SEGS regs _ M rom w1 10 9 0 _ (Z_to_bv 64 0) F1 E1 D1).
          - rewrite H9, signed12_0, v_addi_lit by lia. rewrite Z.add_0_r. exact Rn.
          - apply bytes_le_to_Z_8. }
        rif. rewrite v_addi_lit by lia. pc_is (x + 4).
        eapply mst_step; [reflexivity| |].
        { eapply (step_addi SEGS _ _ M rom w2 9 9 8 F2 E2 D2). }
        rif. rewrite v_addi_lit by lia. pc_is (x + 8). rewrite signed12_8.
        rewrite getr_other by reg_neq_tac. rewrite H9, v_addi_lit by lia.
        eapply mst_step; [reflexivity| |].
        { eapply (step_bne_ft SEGS _ _ M rom w3 10 0 8184 F3 E3 D3).
          rewrite getr_other by reg_neq_tac. rewrite getr_same by reg_neq_tac.
          rewrite getr_zero. reflexivity. }
        rewrite v_addi_lit by lia. pc_is (x + 12). apply mst_refl.
      + split; [|split].
        * rewrite getr_same by reg_neq_tac. reflexivity.
        * rewrite getr_other by reg_neq_tac. rewrite getr_same by reg_neq_tac. reflexivity.
        * intros r Hr. rewrite !getr_other; [reflexivity| |]; intros ->; apply Hr; auto.
    - assert (Hk : (k < envc)%nat) by lia.
      destruct (Rk k Hk) as [Rd Hnz].
      destruct (IH (S k) (regupd (regupd regs 10 (ptr k)) 9 (Z_to_bv 64 (e + 8 * Z.of_nat (S k)))) ltac:(lia)) as [regs' [Hms Hpost]].
      { rewrite getr_same by reg_neq_tac. reflexivity. }
      exists regs'. split.
      + eapply mst_step; [reflexivity| |].
        { eapply (step_ld SEGS regs _ M rom w1 10 9 0 _ (ptr k) F1 E1 D1).
          - rewrite H9, signed12_0, v_addi_lit by lia. rewrite Z.add_0_r. exact Rd.
          - apply bytes_le_to_Z_8. }
        rif. rewrite v_addi_lit by lia. pc_is (x + 4).
        eapply mst_step; [reflexivity| |].
        { eapply (step_addi SEGS _ _ M rom w2 9 9 8 F2 E2 D2). }
        rif. rewrite v_addi_lit by lia. pc_is (x + 8). rewrite signed12_8.
        rewrite getr_other by reg_neq_tac. rewrite H9, v_addi_lit by lia.
        eapply mst_step; [reflexivity| |].
        { eapply (step_bne_tk SEGS _ _ M rom w3 10 0 8184 F3 E3 D3).
          rewrite getr_other by reg_neq_tac. rewrite getr_same by reg_neq_tac.
          rewrite getr_zero. apply c_eq_0_false. exact Hnz. }
        rewrite signed13_m8, btgt_lit by lia. pc_is x.
        replace (e + 8 * Z.of_nat k + 8) with (e + 8 * Z.of_nat (S k)) by lia.
        exact Hms.
      + destruct Hpost as (P9 & P10 & Pag). split; [exact P9|]. split; [exact P10|].
        intros r Hr. rewrite (Pag r Hr). rewrite !getr_other; [reflexivity| |]; intros ->; apply Hr; auto.
  Qed.
End EnvLoop.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section PnLoop.
  Variable SEGS : list Segment.
  Variable x : Z.            (* [comment removed for export] *)
  Variables w0 w1 w2 w3 w4 : bv 32.
  Hypothesis Hx : 8 <= x /\ x + 12 < 2 ^ 64.
  Hypothesis F0 : fetch_word SEGS (Z_to_bv 64 (x - 8)) = Some w0.
  Hypothesis F1 : fetch_word SEGS (Z_to_bv 64 (x - 4)) = Some w1.
  Hypothesis F2 : fetch_word SEGS (Z_to_bv 64 x) = Some w2.
  Hypothesis F3 : fetch_word SEGS (Z_to_bv 64 (x + 4)) = Some w3.
  Hypothesis F4 : fetch_word SEGS (Z_to_bv 64 (x + 8)) = Some w4.
  Hypothesis E0 : is_ecall w0 = false.
  Hypothesis E1 : is_ecall w1 = false.
  Hypothesis E2 : is_ecall w2 = false.
  Hypothesis E3 : is_ecall w3 = false.
  Hypothesis E4 : is_ecall w4 = false.
  Hypothesis D0 : decode_any w0 = Some (Store SZ8 10 11 0, 4%Z).
  Hypothesis D1 : decode_any w1 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
  Hypothesis D2 : decode_any w2 = Some (Load SZ1 false 13 11 4095, 4%Z).
  Hypothesis D3 : decode_any w3 = Some (Branch BC_EQ 13 12 8180, 4%Z).
  Hypothesis D4 : decode_any w4 = Some (Branch BC_NE 13 0 8180, 4%Z).

  Variable M0 : word -> option byte.
  Variable rom : word -> option byte.
  (* [comment removed for export] *)
  Variable p pn : Z.
  Variable s : list byte.
  Hypothesis Hp : 0 <= p /\ p + 8 <= 2 ^ 64.
  Hypothesis Hpn : 0 <= pn /\ pn + Z.of_nat (length s) + 2 < 2 ^ 64.
  Hypothesis Hapart : p + 8 <= pn \/ pn + Z.of_nat (length s) + 1 <= p.
  Hypothesis Hnz : ~ In (Z_to_bv 8 0) s.
  Hypothesis Hrd : forall j, (j <= length s)%nat ->
    rdn SEGS M0 (Z_to_bv 64 (pn + Z.of_nat j)) 1 = Some [byte_at s j].
  Hypothesis Hst : store_ok SEGS M0 (Z_to_bv 64 p) 8 = true.

  (* [comment removed for export] *)
  Definition cellrel (M : word -> option byte) : Prop :=
    (forall a : word, bv_unsigned a < p \/ p + 8 <= bv_unsigned a -> M a = M0 a) /\ mem_grows M0 M.

  Lemma cellrel_refl : cellrel M0.
  Proof. split; [intros; reflexivity | apply mem_grows_refl]. Qed.

  Lemma cellrel_wbytes : forall M (v : word), cellrel M -> cellrel (wbytes M (Z_to_bv 64 p) (word_to_le_bytes 8 v)).
  Proof.
    intros M v [H1 H2]. split.
    - intros a Ha. rewrite <- (H1 a Ha).
      destruct Ha as [Ha|Ha].
      + apply wbytes_below; rewrite ?length_N_to_le_bytes, u_lit by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
      + apply wbytes_above. rewrite length_N_to_le_bytes, u_lit by lia. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
    - eapply mem_grows_trans; [exact H2 | apply wbytes_grows].
  Qed.

  Lemma cellrel_rd : forall M j, cellrel M -> (j <= length s)%nat ->
    rdn SEGS M (Z_to_bv 64 (pn + Z.of_nat j)) 1 = Some [byte_at s j].
  Proof.
    intros M j [H1 _] Hj. rewrite <- (Hrd j Hj). apply rdn_ext.
    - rewrite u_lit by lia. change (Z.of_nat 1) with 1. lia.
    - intros y Hy. rewrite u_lit in Hy by lia. change (Z.of_nat 1) with 1 in Hy. apply H1. lia.
  Qed.

  Lemma cellrel_st : forall M, cellrel M -> store_ok SEGS M (Z_to_bv 64 p) 8 = true.
  Proof. intros M [_ H2]. eapply store_ok_mono; [exact H2 | exact Hst]. Qed.

  Definition pn_post (regs regs' : bvmap 5 word) : Prop :=
    getr regs' 11 = Z_to_bv 64 (pn + Z.of_nat (length s) + 1)
    /\ getr regs' 13 = Z_to_bv 64 0
    /\ regs_agree (fun r => r = 11%bv \/ r = 13%bv) regs regs'.

  Lemma byte_u : forall b : byte, 0 <= bv_unsigned b < 256.
  Proof. intros b. pose proof (u8_range b). lia. Qed.

  Lemma pn_loop : forall l2 j regs M,
    skipn j s = l2 -> (j <= length s)%nat ->
    getr regs 10 = Z_to_bv 64 p ->
    getr regs 11 = Z_to_bv 64 (pn + Z.of_nat j + 1) ->
    getr regs 12 = Z_to_bv 64 47 ->
    cellrel M ->
    exists regs' M',
      msteps SEGS (mkst regs (Z_to_bv 64 x) M rom) (mkst regs' (Z_to_bv 64 (x + 12)) M' rom)
      /\ pn_post regs regs' /\ cellrel M'.
  Proof.
    induction l2 as [|b l2 IH]; intros j regs M Hskip Hj H10 H11 H12 HM.
    - (* end of string: the NUL *)
      assert (Hjl : j = length s).
      { pose proof (f_equal (@length byte) Hskip) as HL. rewrite length_skipn in HL. cbn in HL. lia. }
      subst j.
      exists (regupd regs 13 (Z_to_bv 64 (bv_unsigned (byte_at s (length s))))), M. split; [|split; [|exact HM]].
      + eapply mst_step; [reflexivity| |].
        { eapply (step_lbu SEGS regs _ M rom w2 13 11 4095 (byte_at s (length s)) F2 E2 D2).
          rewrite H11, signed12_m1, v_addi_lit by lia.
          replace (pn + Z.of_nat (length s) + 1 + -1) with (pn + Z.of_nat (length s)) by lia.
          apply cellrel_rd; [exact HM | lia]. }
        rif. rewrite v_addi_lit by lia. pc_is (x + 4).
        rewrite byte_at_len. change (bv_unsigned (Z_to_bv 8 0)) with 0.
        eapply mst_step; [reflexivity| |].
        { eapply (step_beq_ft SEGS _ _ M rom w3 13 12 8180 F3 E3 D3).
          rewrite getr_same by reg_neq_tac. rewrite getr_other by reg_neq_tac.
          rewrite H12. rewrite c_eq_lit by lia. reflexivity. }
        rewrite v_addi_lit by lia. pc_is (x + 8).
        eapply mst_step; [reflexivity| |].
        { eapply (step_bne_ft SEGS _ _ M rom w4 13 0 8180 F4 E4 D4).
          rewrite getr_same by reg_neq_tac. rewrite getr_zero. rewrite c_eq_lit by lia. reflexivity. }
        rewrite v_addi_lit by lia. pc_is (x + 12). apply mst_refl.
      + split; [|split].
        * rewrite getr_other by reg_neq_tac. exact H11.
        * rewrite getr_same by reg_neq_tac. rewrite byte_at_len. reflexivity.
        * intros r Hr. rewrite getr_other; [reflexivity|]. intros ->. apply Hr. auto.
    - assert (Hjlt : (j < length s)%nat).
      { pose proof (f_equal (@length byte) Hskip) as HL. rewrite length_skipn in HL. cbn in HL. lia. }
      assert (Hb : byte_at s j = b).
      { unfold byte_at. rewrite app_nth1 by lia. rewrite <- (Nat.add_0_r j), <- nth_skipn, Hskip. reflexivity. }
      assert (Hbnz : bv_unsigned b <> 0).
      { intros Hb0. apply Hnz. rewrite <- Hb in Hb0. rewrite nth_lt_byte_at in Hb0 by lia.
        replace (Z_to_bv 8 0) with (nth j s (Z_to_bv 8 0)); [apply nth_In; lia|].
        apply bv_eq. rewrite Hb0. reflexivity. }
      assert (Hskip' : skipn (S j) s = l2).
      { replace (S j) with (1 + j)%nat by lia. rewrite <- skipn_skipn, Hskip. reflexivity. }
      pose proof (byte_u b) as Hbu.
      (* the lbu *)
      set (regs1 := regupd regs 13 (Z_to_bv 64 (bv_unsigned b))).
      assert (S1 : RiscvSemantics.step SEGS (mkst regs (Z_to_bv 64 x) M rom) = MachineOk (mkst regs1 (Z_to_bv 64 (x + 4)) M rom)).
      { erewrite (step_lbu SEGS regs _ M rom w2 13 11 4095 b F2 E2 D2).
        - rif. rewrite v_addi_lit by lia. reflexivity.
        - rewrite H11, signed12_m1, v_addi_lit by lia.
          replace (pn + Z.of_nat j + 1 + -1) with (pn + Z.of_nat j) by lia. rewrite <- Hb.
          apply cellrel_rd; [exact HM | lia]. }
      assert (G13 : getr regs1 13 = Z_to_bv 64 (bv_unsigned b)) by (unfold regs1; rewrite getr_same by reg_neq_tac; reflexivity).
      assert (G10 : getr regs1 10 = Z_to_bv 64 p) by (unfold regs1; rewrite getr_other by reg_neq_tac; exact H10).
      assert (G11 : getr regs1 11 = Z_to_bv 64 (pn + Z.of_nat j + 1)) by (unfold regs1; rewrite getr_other by reg_neq_tac; exact H11).
      assert (G12 : getr regs1 12 = Z_to_bv 64 47) by (unfold regs1; rewrite getr_other by reg_neq_tac; exact H12).
      destruct (Z.eqb (bv_unsigned b) 47) eqn:Eb.
      + (* a '/': record the position after it *)
        set (M1 := wbytes M (Z_to_bv 64 p) (word_to_le_bytes 8 (Z_to_bv 64 (pn + Z.of_nat j + 1)))).
        set (regs2 := regupd regs1 11 (Z_to_bv 64 (pn + Z.of_nat (S j) + 1))).
        assert (HM1 : cellrel M1) by (unfold M1; apply cellrel_wbytes; exact HM).
        destruct (IH (S j) regs2 M1 Hskip' ltac:(lia)) as (regs' & M' & Hms & Hpost & HM').
        { unfold regs2. rewrite getr_other by reg_neq_tac. exact G10. }
        { unfold regs2. rewrite getr_same by reg_neq_tac. reflexivity. }
        { unfold regs2. rewrite getr_other by reg_neq_tac. exact G12. }
        { exact HM1. }
        exists regs', M'. split; [|split; [|exact HM']].
        * eapply mst_step; [reflexivity | exact S1 |].
          eapply mst_step; [reflexivity| |].
          { eapply (step_beq_tk SEGS _ _ M rom w3 13 12 8180 F3 E3 D3).
            rewrite G13, G12. rewrite c_eq_lit by lia. exact Eb. }
          rewrite signed13_m12, btgt_lit by lia. pc_is (x - 8).
          eapply mst_step; [reflexivity| |].
          { eapply (step_sd_at SEGS regs1 _ M rom w0 10 11 0 (Z_to_bv 64 p) _ F0 E0 D0).
            - rewrite G10, signed12_0, v_addi_lit by lia. f_equal. lia.
            - exact G11.
            - apply cellrel_st. exact HM. }
          fold M1. rewrite v_addi_lit by lia. pc_is (x - 4).
          eapply mst_step; [reflexivity| |].
          { eapply (step_addi SEGS regs1 _ M1 rom w1 11 11 1 F1 E1 D1). }
          rif. rewrite G11, signed12_1, !v_addi_lit by lia. pc_is x.
          replace (pn + Z.of_nat j + 1 + 1) with (pn + Z.of_nat (S j) + 1) by lia.
          exact Hms.
        * destruct Hpost as (P11 & P13 & Pag). split; [exact P11|]. split; [exact P13|].
          intros r Hr. rewrite (Pag r Hr). unfold regs2, regs1.
          rewrite !getr_other; [reflexivity| |]; intros ->; apply Hr; auto.
      + (* not a '/', not NUL: next byte *)
        set (regs2 := regupd regs1 11 (Z_to_bv 64 (pn + Z.of_nat (S j) + 1))).
        destruct (IH (S j) regs2 M Hskip' ltac:(lia)) as (regs' & M' & Hms & Hpost & HM').
        { unfold regs2. rewrite getr_other by reg_neq_tac. exact G10. }
        { unfold regs2. rewrite getr_same by reg_neq_tac. reflexivity. }
        { unfold regs2. rewrite getr_other by reg_neq_tac. exact G12. }
        { exact HM. }
        exists regs', M'. split; [|split; [|exact HM']].
        * eapply mst_step; [reflexivity | exact S1 |].
          eapply mst_step; [reflexivity| |].
          { eapply (step_beq_ft SEGS _ _ M rom w3 13 12 8180 F3 E3 D3).
            rewrite G13, G12. rewrite c_eq_lit by lia. exact Eb. }
          rewrite v_addi_lit by lia. pc_is (x + 8).
          eapply mst_step; [reflexivity| |].
          { eapply (step_bne_tk SEGS _ _ M rom w4 13 0 8180 F4 E4 D4).
            rewrite G13, getr_zero. apply c_eq_0_false. rewrite u_lit by lia. exact Hbnz. }
          rewrite signed13_m12, btgt_lit by lia. pc_is (x - 4).
          eapply mst_step; [reflexivity| |].
          { eapply (step_addi SEGS regs1 _ M rom w1 11 11 1 F1 E1 D1). }
          rif. rewrite G11, signed12_1, !v_addi_lit by lia. pc_is x.
          replace (pn + Z.of_nat j + 1 + 1) with (pn + Z.of_nat (S j) + 1) by lia.
          exact Hms.
        * destruct Hpost as (P11 & P13 & Pag). split; [exact P11|]. split; [exact P13|].
          intros r Hr. rewrite (Pag r Hr). unfold regs2, regs1.
          rewrite !getr_other; [reflexivity| |]; intros ->; apply Hr; auto.
  Qed.
End PnLoop.

End FPX_2.

End AsanStartLoops.
