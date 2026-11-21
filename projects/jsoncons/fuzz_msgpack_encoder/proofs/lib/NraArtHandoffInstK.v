(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: changed E_AND, E_BK, E_KB and 11 more; added Hlau, abrt, apc and 15 more; removed art_lazy_chk_0, art_lazy_chk_1, art_lits_chk_0 and 5 more; taken in part from projects/jsoncons/fuzz_bigint/proofs/lib/As0ArtHandoffInstK.v, 61 lines within its lines 21-240. *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Na0HandoffInstK.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3SoundK AxSymRun3K AsanPlanSoundK. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0117. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require NraArtHandoffK. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0107. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043.AgentLib OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.AxSymExec3K OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3SoundK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymRun3K OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.AsanPlanCoreK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.AsanPlanK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AsanPlanSoundK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132.AsanInitK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0117.Na0DefsK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0117.Na0PlanImagesK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132.HandoffBridgeK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132.HandoffLedgerK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132.HandoffBInvK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132.HandoffCellsK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132.HandoffRolesK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0117.Na0HandoffK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0117.Na0ArtCellsK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.NraArtHandoffK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0107.Na0HSK_0 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0107.Na0HSK_1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0107.Na0MainTableK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Na0HandoffInstK.Na0HandoffInstK.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0035. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0109. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0145. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0145. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0035.ArtRuns OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0109.ArtBridge OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0145.NarInv OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0145.NarFsInv. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Na0CertK_202.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0003. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0003.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Ltac2 kr_t_NraArtHandoffInstK () := "c49OSSVerify5KrLibBNraArtHandoffInstK7geo_chkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0132=HandoffRolesK4roleC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK7am_baseC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K8expr_eqbC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib>NraArtHandoffK2bKC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4andbC49OSSVerify5KrLib>NraArtHandoffK4topEC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib>NraArtHandoffK4botEC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K4expr02C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02K69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6kentry06C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK:kentry_eqbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK2knC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K;lin_nowrapRC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes9andb_propI47Corelib4Init5Logic3and00I47Corelib4Init5Logic2eq00C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK;expr_eqb_eqC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C46Stdlib5Lists4List7existsbI47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6kentry00C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib>NraArtHandoffK8I_KSPACEC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLibBNraArtHandoffInstK4E_KBC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLibBNraArtHandoffInstK4E_BKC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLibBNraArtHandoffInstK5E_TOPC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLibBNraArtHandoffInstK5E_BOTC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03c49OSSVerify5KrLibBNraArtHandoffInstK5E_ANDC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLibBNraArtHandoffInstK3E_RC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLibBNraArtHandoffInstK4E_PGC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5e_sp0C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K4expr00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0132=HandoffRolesK5rbaseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK2uEC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z6moduloK47Corelib7Numbers7BinNums1N02C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6edenotC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedK47Corelib4Init5Logic2eq01C59OSSVerify5KrLib7Mh_01329AsanInitK5SINV0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01329AsanInitK5argH0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0132>HandoffBridgeK6hb_linC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0132>HandoffBridgeK2LZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0132>HandoffBridgeK2VZC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z7add_0_rC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums1Z03C59OSSVerify5KrLib7Mh_0132>HandoffBridgeK9hb_knb_InC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC59OSSVerify5KrLib>AsanPlanSoundK4APSK2MrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK9kentry_okC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K2evC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem7mul_divC4ELinuxProcessSemantics5Riscv3Sem5alu64C56Stdlib6ZArith6BinInt1Z3powC59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK7u_add64C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landC59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK7u_and64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK7u_mul64C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC59OSSVerify5KrLib7Mh_00438AgentLib7u64_litC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z9land_onesK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z9mod_smallC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega7EnvRing3Pol01C56Stdlib6ZArith6BinInt1Z<eq_decidableI47Corelib4Init5Logic2or00K46Stdlib9micromega5Tauto8GFormula06C47Corelib4Init5Logic6eq_indC59OSSVerify5KrLib7Mh_0132>HandoffBridgeK5hb_knC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega=RingMicromega5Psatz06K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr03I47Corelib7Numbers7BinNums1Z00C59OSSVerify5KrLib7Mh_01178Na0DefsK6ASEGS0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01178Na0DefsK5ASAN0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01329AsanInitK5LIMITC1?~~~~~~~~~~~~~~~C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op201c49OSSVerify5KrLibBNraArtHandoffInstK7geo_synC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01178Na0DefsK4APH0C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5mulop01K4ELinuxProcessSemantics5Riscv5Instr5aluop0:I47Corelib4Init5Logic4True00K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init5Logic5False00C56Stdlib6ZArith6BinInt1Z3subK46Stdlib9micromega7EnvRing5PExpr04C59OSSVerify5KrLib7Mh_0132>HandoffBridgeK7hbi_sp0C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExecMbuild_stack_bytes_within_spanC1?~~~~~~~~~~~~~~~I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics?LinuxProcessSem;StackLayoutAbuild_stack_bytesC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC4ELinuxProcessSemantics?LinuxProcessSem3Run@entry_stack_spanC59OSSVerify5KrLib7Mh_01329AsanInitK6bsb_geC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC59OSSVerify5KrLib7Mh_01078Na0HSK_04HS_0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01078Na0HSK_14HS_1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0117<Na0ArtCellsK<art_lits_chkC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib>NraArtHandoffK;art_sym_chkC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib>NraArtHandoffK<art_lazy_chkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv4KMAXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv6LENMAXC1?~~~~~~~~~~~~~~~C47Corelib4Init5Peano2ltC4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib?Na0HandoffInstK?Na0HandoffInstK3HSAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0117;Na0HandoffK7as0_chkC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses7rew_iffC4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC4ELinuxProcessSemantics?LinuxProcessSem5State7vm_mapsC4ELinuxProcessSemantics?LinuxProcessSem3RunAsegments_reservedC4ELinuxProcessSemantics?LinuxProcessSem5State;vm_noaccessC49OSSVerify5KrLib>NraArtHandoffK9as0_BASExC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib>NraArtHandoffK6as0_rnC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib>NraArtHandoffK7as0_A0xC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6vml_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?Na0HandoffInstK?Na0HandoffInstK;HSA_numbersC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK7a_totszC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK7a_eagerC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK8a_abytesC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLibBNraArtHandoffInstK7geo_spbC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLibBNraArtHandoffInstK7geo_stkC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLibBNraArtHandoffInstK8geo_sp16C1?~~~~~~~~~~~~~~~c49OSSVerify5KrLibBNraArtHandoffInstK7geo_spaC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symI47Corelib4Init9Datatypes4prod00C47Corelib4Init3Nat3addK47Corelib4Init9Datatypes4prod01C49OSSVerify5KrLib>NraArtHandoffK?as0_art_handoffC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib>AsanPlanSoundK4APSK5cs_ok00C1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelC59OSSVerify5KrLib7Mh_01456NarInvBart_handoff_targetC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK6a_mapsC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z8inj_succC56Stdlib6ZArith4Znat5Nat2Z6inj_ltI59OSSVerify5KrLib7Mh_01458NarFsInv7art_fsg00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01458NarFsInv9art_fsinvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01458NarFsInv8art_fsg0C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib>NraArtHandoffK3K0DC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv4KCNTC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00769AsanPlanK3APK4amap00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K3env00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C59OSSVerify5KrLib?Na0HandoffInstK?Na0HandoffInstK9as0_chk_0C1?~~~~~~~~~~~~~~~c49OSSVerify5KrLibBNraArtHandoffInstK>art_lits_chk_0C1?~~~~~~~~~~~~~~~c49OSSVerify5KrLibBNraArtHandoffInstK=art_sym_chk_0C1?~~~~~~~~~~~~~~~c49OSSVerify5KrLibBNraArtHandoffInstK9geo_chk_0C1?~~~~~~~~~~~~~~~c49OSSVerify5KrLibBNraArtHandoffInstK>art_lazy_chk_0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?Na0HandoffInstK?Na0HandoffInstK9as0_chk_1C1?~~~~~~~~~~~~~~~c49OSSVerify5KrLibBNraArtHandoffInstK>art_lits_chk_1C1?~~~~~~~~~~~~~~~c49OSSVerify5KrLibBNraArtHandoffInstK=art_sym_chk_1C1?~~~~~~~~~~~~~~~c49OSSVerify5KrLibBNraArtHandoffInstK9geo_chk_1C1?~~~~~~~~~~~~~~~c49OSSVerify5KrLibBNraArtHandoffInstK>art_lazy_chk_1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00238AsanCeil>bottomup_floorC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00238AsanCeil=alloc_ceilingC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0117>Na0PlanImagesK<asan0_res_eqC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLibBNraArtHandoffInstK8inst_budC1?~~~~~~~~~~~~~~~". Local Ltac lia := L5FastLiaT.plia2.
Import ListNotations.
Import AxSymExec3K.AX2K AxSymExec3SoundK.AX2SK AsanPlanK.APK AsanPlanSoundK.APSK. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition E_KB : expr := EMd M_MUL (ELit 4096) (EVar 228).
Definition E_BK : expr := EAlu ALU_ADD (EMd M_MUL (ELit 4096) (EVar 228)) (EMd M_MUL (ELit (-4096)) (EVar 229)).
Definition E_AND : expr := EAlu ALU_ADD (EMd M_MUL (ELit (-4096)) (EVar 229)) (EAlu ALU_AND (EMd M_MUL (ELit 4096) (EVar 228)) (ELit 65535)).
Definition E_PG : expr := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 4096) (EVar 10)).
Definition E_TOP : expr := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EAlu ALU_ADD (EMd M_MUL (ELit 4096) (EVar 10)) (EMd M_MUL (ELit 4096) (EVar 382))).
Definition E_BOT : expr := eaddz E_TOP (-8388608).
Definition E_R : expr := EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 16) (EVar 6)) (EMd M_MUL (ELit (-4096)) (EVar 382))) (ELit 3935).

(* [comment removed for export] *)
Definition geo_chk (cs : acs) : bool :=
  let k := kn cs in
  (expr_eqb (am_base (role cs I_KSPACE)) E_KB && expr_eqb (bK cs) E_BK && expr_eqb (topE cs) E_TOP && expr_eqb (botE cs) E_BOT
   && existsb (kentry_eqb (KRange (EVar 229) 0 15)) k && existsb (kentry_eqb (KRange E_AND 0 0)) k
   && existsb (kentry_eqb (KRange (EVar 228) 4295491576 34326181871)) k
   && existsb (kentry_eqb (KRange (EVar 382) 0 1)) k && existsb (kentry_eqb (KRange (EVar 6) 0 255)) k
   && existsb (kentry_eqb (KRange E_R 0 4095)) k
   && existsb (kentry_eqb (KRange E_PG 140735340871680 140737488351232)) k
   && lin_nowrapR k E_KB && lin_nowrapR k E_BK && lin_nowrapR k E_TOP && lin_nowrapR k E_BOT && lin_nowrapR k E_PG && lin_nowrapR k E_R
   && lin_nowrapR k e_sp0)%bool.

Section Geo.
  Variable sp brk0 : word.
  Variable rdraw : EntryDraw.
  Variable argv envp : list (list byte).
  Variables uid hw : word.
  Variable fs : Fs.Fs.
  (* [comment removed for export] *)
  Variable mbase : word.
  Variable stdin : InputStream.
  Variable gid : word.
  Variable groups : list word.
  Variable net : NetQueue.
  Variables nofile sigmask : word.
  Variable abrt : bool.
  Variable ur : InputStream.
  Variable kb : KernelBuild.
  Variable execfn : list byte.
  Variable sdf : bool.   (* the SIGPIPE disposition at exec, free at LPS 727298f3 *)
  Variable apc : N.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  #[local] Notation SINV := (SINV0 APH0 sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf apc).
  #[local] Notation argH := (argH0 sp rdraw argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf).
  #[local] Notation CSOK := (cs_ok ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs).

  Variable cs : acs.
  Hypothesis GCHK : geo_chk cs = true.
  Variables (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
  Hypothesis HC : CSOK E cs R FULL model.

  (* [comment removed for export] *)
  Ltac LINEQ e H :=
    let Hn := fresh in
    assert (Hn : lin_nowrapR (kn cs) e = true)
      by (let G := fresh in pose proof GCHK as G; unfold geo_chk in G; repeat (let X := fresh in apply andb_prop in G as [G X]); assumption);
    pose proof (hb_lin ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model e HC Hn) as H; clear Hn;
    unfold LZ in H;
    match type of H with context [lin_of ?x] => let l := eval vm_compute in (lin_of x) in change (lin_of x) with l in H end;
    cbv [AX2SK.lden AX2SK.tden fst snd AX2SK.uE] in H; cbn [edenot] in H;
    repeat match type of H with context [bv_unsigned (ev E ?n)] => change (bv_unsigned (ev E n)) with (VZ E n) in H end;
    rewrite ?Z.add_0_r in H.
  Ltac RANGE K H :=
    let Hi := fresh in
    assert (Hi : In K (kn cs))
      by (apply hb_knb_In; let G := fresh in pose proof GCHK as G; unfold geo_chk in G; repeat (let X := fresh in apply andb_prop in G as [G X]); assumption);
    pose proof (hb_kn ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model K HC Hi) as H; clear Hi; cbn [kentry_ok] in H.

  #[using="GCHK"] Lemma geo_syn : am_base (role cs I_KSPACE) = E_KB /\ bK cs = E_BK /\ topE cs = E_TOP /\ botE cs = E_BOT.
  Proof.
    pose proof GCHK as G. unfold geo_chk in G. repeat (let X := fresh in apply andb_prop in G as [G X]).
    repeat split; apply expr_eqb_eq; assumption.
  Qed.

  #[using="sp brk0 rdraw argv envp uid hw fs GCHK R FULL model HC"] Lemma geo_spb : rbase E cs I_KSPACE < uE E (bK cs) + 0x10000 <= rbase E cs I_KSPACE + 65536 /\ (uE E (bK cs) + 0x10000) mod 65536 = 0.
  Proof.
    destruct geo_syn as (S1 & S2 & _ & _). unfold rbase. rewrite S1, S2. unfold uE.
    (* [comment removed for export] *)
    remember (bv_unsigned (edenot E E_KB)) as kbz eqn:Ekbz. remember (bv_unsigned (edenot E E_BK)) as bk eqn:Ebk.
    LINEQ E_KB L1. rewrite <- Ekbz in L1. LINEQ E_BK L2. rewrite <- Ebk in L2.
    RANGE (KRange (EVar 229) 0 15) R1. RANGE (KRange (EVar 228) 4295491576 34326181871) R2. RANGE (KRange E_AND 0 0) R3.
    cbn [edenot] in R1, R2. change (bv_unsigned (ev E 229)) with (VZ E 229) in R1. change (bv_unsigned (ev E 228)) with (VZ E 228) in R2.
    (* [comment removed for export] *)
    unfold E_AND in R3. cbn [edenot] in R3. rewrite u_add64, u_and64, !u_mul64 in R3.
    rewrite (u64_lit 65535), (u64_lit 4096) in R3 by lia.
    replace (bv_unsigned (Z_to_bv 64 (-4096))) with 18446744073709547520 in R3 by (vm_compute; reflexivity).
    change (bv_unsigned (ev E 229)) with (VZ E 229) in R3. change (bv_unsigned (ev E 228)) with (VZ E 228) in R3.
    change 65535 with (Z.ones 16) in R3. rewrite Z.land_ones in R3 by lia. change (2 ^ 16) with 65536 in R3.
    rewrite (Z.mod_small (4096 * VZ E 228) (2 ^ 64)) in R3 by lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    assert (HA : (4096 * VZ E 228) mod 65536 = 4096 * VZ E 229) by lia.
    subst kbz bk. rewrite L1, L2. split; [|]; lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  Qed.

  #[using="sp brk0 rdraw argv envp uid hw fs GCHK R FULL model HC"] Lemma geo_stk : uE E (topE cs) = uE E (botE cs) + 8388608 /\ uE E (botE cs) mod 4096 = 0
                  /\ uE E e_sp0 - 8388608 <= uE E (botE cs) + 4096 /\ uE E (botE cs) <= uE E e_sp0 - 8388608 + 4096 /\ uE E (topE cs) <= 2 ^ 47.
  Proof.
    destruct geo_syn as (_ & _ & S3 & S4). rewrite S3, S4. unfold uE.
    remember (bv_unsigned (edenot E E_TOP)) as top eqn:Et. remember (bv_unsigned (edenot E E_BOT)) as bot eqn:Eb.
    remember (bv_unsigned (edenot E e_sp0)) as s0 eqn:Es. remember (bv_unsigned (edenot E E_PG)) as pg eqn:Ep.
    remember (bv_unsigned (edenot E E_R)) as rr eqn:Er.
    LINEQ E_TOP L1. rewrite <- Et in L1. LINEQ E_BOT L2. rewrite <- Eb in L2. LINEQ e_sp0 L3. rewrite <- Es in L3.
    LINEQ E_PG L4. rewrite <- Ep in L4. LINEQ E_R L5. rewrite <- Er in L5.
    RANGE (KRange (EVar 382) 0 1) R1. RANGE (KRange (EVar 6) 0 255) R2. RANGE (KRange E_R 0 4095) R3. RANGE (KRange E_PG 140735340871680 140737488351232) R4.
    cbn [edenot] in R1, R2. change (bv_unsigned (ev E 382)) with (VZ E 382) in R1. change (bv_unsigned (ev E 6)) with (VZ E 6) in R2.
    rewrite <- Er in R3. rewrite <- Ep in R4.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    repeat split; lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  Qed.
  (* [comment removed for export] *)
  #[using="sp brk0 rdraw argv envp uid hw fs cs GCHK R FULL model HC"] Lemma geo_spa : uE E e_sp0 mod 16 = 0.
  Proof.
    unfold uE. remember (bv_unsigned (edenot E e_sp0)) as s0 eqn:Es. LINEQ e_sp0 L3. rewrite <- Es in L3.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  Qed.
  (* [comment removed for export] *)
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  (* [comment removed for export] *)
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw)
    (AsanInitK.inp argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf).
  #[using="sp brk0 rdraw argv envp uid hw fs Hsp Hva cs GCHK R FULL model HC Hve Hfit Hlau"] Lemma geo_sp16 : uE E e_sp0 + 16 <= 2 ^ 47.
  Proof.
    unfold uE. remember (bv_unsigned (edenot E e_sp0)) as s0 eqn:Es. LINEQ e_sp0 L3. rewrite <- Es in L3.
    (* [comment removed for export] *)
    pose proof (hbi_sp0 ASEGS0 ASAN0 APH0 sp rdraw brk0 mbase argv envp uid hw fs stdin gid groups net nofile sigmask abrt ur kb execfn sdf apc Hsp Hva Hve Hfit Hlau E cs R FULL model HC) as U0.
    (* [comment removed for export] *)
    unfold entry_stack_fits, entry_stack_span, sp_window_hi in Hfit.
    pose proof (total_arg_bytes_nonneg argv). pose proof (total_arg_bytes_nonneg envp).
    pose proof (Nat2Z.is_nonneg (length argv)). pose proof (Nat2Z.is_nonneg (length envp)).
    lia.
  Qed.
End Geo.

(* [comment removed for export] *)
Lemma geo_chk_HSA : forall r h, (h < 2)%nat -> geo_chk (HSA r h) = true.
Proof. intros r [|[|h]] H; [| |lia]; unfold HSA; destruct (Z.eqb r 1); vm_compute; reflexivity. Qed.
Lemma art_lits_chk_HSA : forall r h, (h < 2)%nat -> art_lits_chk (HSA r h) = true.
Proof. intros r [|[|h]] H; [| |lia]; unfold HSA; destruct (Z.eqb r 1); vm_compute; reflexivity. Qed.
Lemma art_sym_chk_HSA : forall r h, (h < 2)%nat -> art_sym_chk (HSA r h) = true.
Proof. intros r [|[|h]] H; [| |lia]; unfold HSA; destruct (Z.eqb r 1); vm_compute; reflexivity. Qed.
Lemma art_lazy_chk_HSA : forall r h, (h < 2)%nat -> art_lazy_chk (HSA r h) = true.
Proof. intros r [|[|h]] H; [| |lia]; unfold HSA; destruct (Z.eqb r 1); vm_compute; reflexivity. Qed.

Section Inst.
  Variable sp brk0 : word.
  Variable rdraw : EntryDraw.
  Variable argv envp : list (list byte).
  Variables uid hw : word.
  Variable fs : Fs.Fs.
  (* [comment removed for export] *)
  Variable mbase : word.
  Variable stdin : InputStream.
  Variable gid : word.
  Variable groups : list word.
  Variable net : NetQueue.
  Variables nofile sigmask : word.
  Variable abrt : bool.
  Variable ur : InputStream.
  Variable kb : KernelBuild.
  Variable execfn : list byte.
  Variable sdf : bool.   (* the SIGPIPE disposition at exec, free at LPS 727298f3 *)
  Variable apc : N.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  (* [comment removed for export] *)
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw)
    (AsanInitK.inp argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf).
  #[local] Notation SINV := (SINV0 APH0 sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf apc).
  #[local] Notation argH := (argH0 sp rdraw argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf).
  #[local] Notation CSOK := (cs_ok ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs).

  (* [comment removed for export] *)
  Variable BUDGET : Z.
  Hypothesis BUD_ge : 2 ^ 36 + 2 ^ 20 + NarInv.PRIMCAP <= BUDGET.      (* [comment removed for export] *)
  Hypothesis BUD_hi : BUDGET <= 2 ^ 39 - 2 ^ 35.
  (* [comment removed for export] *)
  Let FSH : art_fsinv_handoff := art_fsinv_handoff_proved.

  #[using="BUD_ge"] Lemma inst_bud : 0 <= BUDGET /\ 0 <= NarInv.KMAX /\ 0 <= NarInv.LENMAX < 2 ^ 62.
Proof.
ltac2:(KReplay.run1 (kr_t_NraArtHandoffInstK ()) ["Inst"] "h02Hah14__x1h27__arithh34__ffh46__sat0h56__sat1h67__sat10h77__sat11h87__sat12h97__sat13h:7__sat14h;7__sat15h<6__sat2h=6__sat3h>6__sat4h?6__sat5h@6__sat6hA6__sat7hB6__sat8hC6__sat9hD8__varmaphE5__witp;1p;2p;3p;4p;8p;7g00<hj14Tg009Bj12Tg008]j11Tg00e`j25Tg00a\j27Tg00fdj36Tg00gHj1LTg00ghj1HTg01?ij2FTg00hfj1ETg00iDj1WTg00ioj2?Tg00R2j1;Tg01C]j3CTg01@Gj3VTg011Sj2UTg0126j1QTg01;[j4DTg01@jj8PTg00k5j2OTg00T>j2NTg00kWj2KTg00?Tj3ITg00lCj3JTg00lbj4GTg00Q5j2@Tg00YNj2MTg012Xj2=Tg00fHj2BTg00?9j29Tg00jRj3RTg01<Fj7STg01<jj7TTg00I?R0f0R1'Bp=31=01p=0%41#4p=8g01D@R2f1R3;R1p=:P2P3g01J7P1CDp=>P3g01GQR4g01H0R5P5g01HPR6P1g01IWFSp=<f2R7P4P5P5P6P3P1FTp=Ag00I]R8#4R9#2R:%49R;#1R<#1#1#2R='5%3:R>%0=17:=R?#3[[%0:R@g01OnRAA6:=3UW0%0?\A^0@%8<R<#2R?,5:%0?17:?R=#3[\>A6:?3VAX0@%0=\A^0@%18#1#1R?#1#4RB#2RC,5:%0C17:CRD#3[\>A6:C3VAX0@%0D\A^0@%4;R;#1#1#2RC,5:%0C17:CRE#3[\>A6:C3VAX0@%0E\A^0@%4;R;#4RE#2RC,5:%0C17:CRF#3[\>A6:C3VAX0@%0F\A^0@%19#8R9#2RC,5:%0C17:CRG#3[\>A6:C3VAX0@%0G\A^0@%2;RC,5:%0C17:CRH#3[\>A6:C3VAX0@%0H\A^0@%4?R?#2RC,5:%0C17:CRI#3[\>A6:C3VAX0@%0I\A^0@g01J^R@#L%H@1F23%E2%W2R@P4P5P5P61?2:R:%;<':%;9,::5C21?2C%;E,::5V25C21U28R8'>,<@%Q51?20R5/>8,<@%8E#8#8#8#2RE,?2,>5,<@%;?,::%;;,::5C2R;,>5,<@P2P;g01I0%;B,::CD,<@5A@5A@5A@GP1O@6P1P7g00AlR@g00BLR6'N1K17=I@6dAJ203CGb3bDbEX121@=G1MCF'@/=1%03%0E1@IHRI#01BID'9'9'9[^12P1p,6BUDGETR1p,6BUD_geO2b2b4b5b<b=b>b?b@bAbBbCb6b7b8b9b:b;%01g01^b,=0g01_ZR1,=01B1D'9'9'9eo"). Qed.

    #[using="Hsp Hva Hve Hfit BUD_ge BUD_hi FSH Hlau"] Theorem as0_art_handoff_h : forall r h, (h < 2)%nat -> forall E R FULL model, CSOK E (HSA r h) R FULL model ->
    art_handoff_target art_fsg (vm_maps (m_vmmaps model)) (vm_reserved (m_vmmaps model)) (vm_noaccess (m_vmmaps model))
    (as0_BASEx (HSA r h) E) BUDGET art_fsinv (as0_rn E (HSA r h)) art_fsg0 K0D NarInv.KCNT (2 ^ 36) (as0_A0x (HSA r h) E) FULL (vml_of model).
    Proof.
    intros r h Hh E R FULL model HC.
    assert (CH : as0_chk (HSA r h) = true /\ art_lits_chk (HSA r h) = true /\ art_sym_chk (HSA r h) = true /\ geo_chk (HSA r h) = true /\ art_lazy_chk (HSA r h) = true).
    { exact (conj (as0_chk_HSA r h Hh) (conj (art_lits_chk_HSA r h Hh) (conj (art_sym_chk_HSA r h Hh) (conj (geo_chk_HSA r h Hh) (art_lazy_chk_HSA r h Hh))))). }
    destruct CH as (C0 & CL & CS & CG & CZ).
    destruct (HSA_numbers r h Hh) as (N1 & N2 & N3 & N4).
    pose proof (geo_spb sp brk0 rdraw argv envp uid hw fs mbase stdin gid groups net nofile sigmask abrt ur kb execfn sdf apc (HSA r h) CG E R FULL model HC) as GS.
    pose proof (geo_stk sp brk0 rdraw argv envp uid hw fs mbase stdin gid groups net nofile sigmask abrt ur kb execfn sdf apc (HSA r h) CG E R FULL model HC) as GT.
    pose proof (geo_sp16 sp brk0 rdraw argv envp uid hw fs mbase stdin gid groups net nofile sigmask abrt ur kb execfn sdf apc Hsp Hva (HSA r h) CG E R FULL model HC Hve Hfit Hlau) as G16.
    pose proof (geo_spa sp brk0 rdraw argv envp uid hw fs mbase stdin gid groups net nofile sigmask abrt ur kb execfn sdf apc (HSA r h) CG E R FULL model HC) as GA.
    assert (BL : a_eager (HSA r h) + a_abytes (HSA r h) + 2 ^ 34 + BUDGET <= Mh_0132.AsanInitK.LIMIT) by (unfold Mh_0132.AsanInitK.LIMIT, target_alloc_limit; lia).
    assert (GP : Mh_0023.AsanCeil.bottomup_floor + Mh_0145.NarInv.LENMAX + (a_totsz (HSA r h) + BUDGET)
    + (Z.of_nat (length (segments_reserved ASEGS0) + n_resx ASAN0 + length (a_maps (HSA r h))) + Mh_0145.NarInv.KMAX) * (Mh_0145.NarInv.LENMAX + 4095) <= Mh_0023.AsanCeil.alloc_ceiling).
    { rewrite N4, asan0_res_eq. change (n_resx ASAN0) with 2%nat. cbn [length Nat.add]. change (Z.of_nat 23) with 23.
    unfold Mh_0145.NarInv.KMAX, Mh_0145.NarInv.LENMAX, Mh_0023.AsanCeil.bottomup_floor, Mh_0023.AsanCeil.alloc_ceiling. lia. }
    eapply (as0_art_handoff sp brk0 rdraw argv envp uid hw fs mbase stdin gid groups net nofile sigmask abrt ur kb execfn sdf apc Hsp Hva (HSA r h)); try eassumption; first [exact inst_bud | exact FSH].
    Qed.
End Inst.
