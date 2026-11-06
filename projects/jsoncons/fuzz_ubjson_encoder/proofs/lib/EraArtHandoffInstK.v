(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PropExec AgentLib AxSymExec3K AxSymExec3SoundK AxSymRun3K
  AsanPlanCoreK AsanPlanK AsanPlanSoundK AsanInitK Ea0DefsK Ea0PlanImagesK HandoffBridgeK HandoffLedgerK HandoffBInvK HandoffCellsK HandoffRolesK
  Ea0HandoffK Ea0ArtCellsK EraArtHandoffK Ea0HSK_0 Ea0HSK_1 Ea0MainTableK Ea0HandoffInstK.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import HeapIface HeapIfaceA HeapIfaceAEx ArtRuns ArtBridge EarInv EarFsInv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_EraArtHandoffInstK () := "c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3libBEraArtHandoffInstK7geo_chkC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=HandoffRolesK4roleC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9AsanPlanK3APK7am_baseC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;AxSymExec3K4AX2K8expr_eqbC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>EraArtHandoffK2bKC13~~~C47Corelib4Init9Datatypes4andbC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>EraArtHandoffK4topEC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>EraArtHandoffK4botEC13~~~K47Corelib4Init9Datatypes3nat02K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;AxSymExec3K4AX2K4expr02C13~~~K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;AxSymExec3K4AX2K6kentry06C13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9AsanPlanK3APK:kentry_eqbC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9AsanPlanK3APK2knC13~~~K47Corelib7Numbers7BinNums8positive02C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;AxSymExec3K4AX2K;lin_nowrapRC13~~~C47Corelib4Init9Datatypes9andb_propI47Corelib4Init5Logic3and00I47Corelib4Init5Logic2eq00C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@AxSymExec3SoundK5AX2SK;expr_eqb_eqC13~~~K47Corelib4Init5Logic3and01C46Stdlib5Lists4List7existsbI47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;AxSymExec3K4AX2K6kentry00C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>EraArtHandoffK8I_KSPACEC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3libBEraArtHandoffInstK4E_KBC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3libBEraArtHandoffInstK4E_BKC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3libBEraArtHandoffInstK5E_TOPC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3libBEraArtHandoffInstK5E_BOTC13~~~K47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3libBEraArtHandoffInstK5E_ANDC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3libBEraArtHandoffInstK3E_RC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3libBEraArtHandoffInstK4E_PGC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9AsanPlanK3APK5e_sp0C13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;AxSymExec3K4AX2K4expr00C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=HandoffRolesK5rbaseC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>AsanPlanSoundK4APSK2uEC13~~~C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z6moduloK47Corelib7Numbers7BinNums1N02C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;AxSymExec3K4AX2K6edenotC13~~~C45stdpp9bitvector;definitions;bv_unsignedK47Corelib4Init5Logic2eq01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9AsanInitK5SINV0C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9AsanInitK5argH0C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>HandoffBridgeK6hb_linC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>HandoffBridgeK2LZC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>HandoffBridgeK2VZC13~~~C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z7add_0_rC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums1Z03C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>HandoffBridgeK9hb_knb_InC13~~~C46Stdlib5Lists4List2InC89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>AsanPlanSoundK4APSK2MrC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@AxSymExec3SoundK5AX2SK9kentry_okC13~~~C45stdpp9bitvector;definitions7Z_to_bvC89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;AxSymExec3K4AX2K2evC13~~~C4ELinuxProcessSemantics5Riscv3Sem7mul_divC4ELinuxProcessSemantics5Riscv3Sem5alu64C56Stdlib6ZArith6BinInt1Z3powC89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@AxSymExec3SoundK5AX2SK7u_add64C13~~~C56Stdlib6ZArith6BinInt1Z4landC89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@AxSymExec3SoundK5AX2SK7u_and64C13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@AxSymExec3SoundK5AX2SK7u_mul64C13~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AgentLib7u64_litC13~~~C56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z9land_onesK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z9mod_smallC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega7EnvRing3Pol01C56Stdlib6ZArith6BinInt1Z<eq_decidableI47Corelib4Init5Logic2or00K46Stdlib9micromega5Tauto8GFormula06C47Corelib4Init5Logic6eq_indC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>HandoffBridgeK5hb_knC13~~~K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega=RingMicromega5Psatz06K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr03I47Corelib7Numbers7BinNums1Z00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8Ea0DefsK6ASEGS0C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8Ea0DefsK5ASAN0C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9AsanInitK5LIMITC13~~~C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op201c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3libBEraArtHandoffInstK7geo_synC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8Ea0DefsK4APH0C13~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5mulop01K4ELinuxProcessSemantics5Riscv5Instr5aluop0:I47Corelib4Init5Logic4True00K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init5Logic5False00C56Stdlib6ZArith6BinInt1Z3subK46Stdlib9micromega7EnvRing5PExpr04C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>HandoffBridgeK7hbi_sp0C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExecMbuild_stack_bytes_within_spanC13~~~I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics?LinuxProcessSem;StackLayoutAbuild_stack_bytesC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC4ELinuxProcessSemantics?LinuxProcessSem3Run@entry_stack_spanC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9AsanInitK6bsb_geC13~~~C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8Ea0HSK_04HS_0C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8Ea0HSK_14HS_1C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Ea0ArtCellsK<art_lits_chkC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>EraArtHandoffK;art_sym_chkC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>EraArtHandoffK<art_lazy_chkC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6EarInv4KMAXC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6EarInv6LENMAXC13~~~C47Corelib4Init5Peano2ltC4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes6option00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Ea0HandoffInstK3HSAC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Ea0HandoffK7as0_chkC13~~~C46Stdlib9micromega;ZifyClasses7rew_iffC4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC4ELinuxProcessSemantics?LinuxProcessSem5State7vm_mapsC4ELinuxProcessSemantics?LinuxProcessSem3RunAsegments_reservedC4ELinuxProcessSemantics?LinuxProcessSem5State;vm_noaccessC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>EraArtHandoffK9as0_BASExC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>EraArtHandoffK6as0_rnC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>EraArtHandoffK7as0_A0xC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA6vml_ofC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Ea0HandoffInstK;HSA_numbersC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9AsanPlanK3APK7a_totszC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9AsanPlanK3APK7a_eagerC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9AsanPlanK3APK8a_abytesC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3libBEraArtHandoffInstK7geo_spbC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3libBEraArtHandoffInstK7geo_stkC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3libBEraArtHandoffInstK8geo_sp16C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3libBEraArtHandoffInstK7geo_spaC13~~~C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symI47Corelib4Init9Datatypes4prod00C47Corelib4Init3Nat3addK47Corelib4Init9Datatypes4prod01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>EraArtHandoffK?as0_art_handoffC13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>AsanPlanSoundK4APSK5cs_ok00C13~~~C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6EarInvBart_handoff_targetC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9AsanPlanK3APK6a_mapsC13~~~I47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z8inj_succC56Stdlib6ZArith4Znat5Nat2Z6inj_ltI79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8EarFsInv7art_fsg00C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8EarFsInv9art_fsinvC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8EarFsInv8art_fsg0C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>EraArtHandoffK3K0DC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6EarInv4KCNTC13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9AsanPlanK3APK4amap00C13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;AxSymExec3K4AX2K3env00C13~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Ea0HandoffInstK9as0_chk_0C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3libBEraArtHandoffInstK>art_lits_chk_0C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3libBEraArtHandoffInstK=art_sym_chk_0C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3libBEraArtHandoffInstK9geo_chk_0C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3libBEraArtHandoffInstK>art_lazy_chk_0C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Ea0HandoffInstK9as0_chk_1C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3libBEraArtHandoffInstK>art_lits_chk_1C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3libBEraArtHandoffInstK=art_sym_chk_1C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3libBEraArtHandoffInstK9geo_chk_1C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3libBEraArtHandoffInstK>art_lazy_chk_1C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanCeil>bottomup_floorC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanCeil=alloc_ceilingC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>Ea0PlanImagesK<asan0_res_eqC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3libBEraArtHandoffInstK8inst_budC13~~~". Local Ltac lia := L5FastLiaT.plia2.
Import ListNotations.
Import AxSymExec3K.AX2K AxSymExec3SoundK.AX2SK AsanPlanK.APK AsanPlanSoundK.APSK.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition E_KB : expr := EMd M_MUL (ELit 4096) (EVar 224).
Definition E_BK : expr := EAlu ALU_ADD (EMd M_MUL (ELit 4096) (EVar 224)) (EMd M_MUL (ELit (-4096)) (EVar 225)).
Definition E_AND : expr := EAlu ALU_ADD (EMd M_MUL (ELit (-4096)) (EVar 225)) (EAlu ALU_AND (EMd M_MUL (ELit 4096) (EVar 224)) (ELit 65535)).
Definition E_PG : expr := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 4096) (EVar 10)).
Definition E_TOP : expr := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EAlu ALU_ADD (EMd M_MUL (ELit 4096) (EVar 10)) (EMd M_MUL (ELit 4096) (EVar 376))).
Definition E_BOT : expr := eaddz E_TOP (-8388608).
Definition E_R : expr := EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 16) (EVar 6)) (EMd M_MUL (ELit (-4096)) (EVar 376))) (ELit 3935).

(* [comment removed for export] *)
Definition geo_chk (cs : acs) : bool :=
  let k := kn cs in
  (expr_eqb (am_base (role cs I_KSPACE)) E_KB && expr_eqb (bK cs) E_BK && expr_eqb (topE cs) E_TOP && expr_eqb (botE cs) E_BOT
   && existsb (kentry_eqb (KRange (EVar 225) 0 15)) k && existsb (kentry_eqb (KRange E_AND 0 0)) k
   && existsb (kentry_eqb (KRange (EVar 224) 4295491576 34326181871)) k
   && existsb (kentry_eqb (KRange (EVar 376) 0 1)) k && existsb (kentry_eqb (KRange (EVar 6) 0 255)) k
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
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  #[local] Notation SINV := (SINV0 APH0 sp rdraw brk0 argv envp uid hw).
  #[local] Notation argH := (argH0 APH0 sp rdraw argv envp uid hw).
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
ltac2:(KReplay.run1 (kr_t_EraArtHandoffInstK ()) ["Geo"] "h01Gh11Hh22H0h32H1h43H10h53H11h63H12h73H13h83H14h93H15h:2H2h;2H3h<2H4h=2H5h>2H6h?2H7h@2H8hA2H9p;1p;2p;3p;4g0000j1STg001Ej2OTg002Rj1LTg003bj2DTg0056j1RTg006Bj26Tg006`j1NTg007nj1MTg009<j10Tg009[j1CTg00:mj14Tg00;Rj18Tg00<0j3;Tg00=Dj1<Tg00>Wj1QTg00?bj13Tg00@Gj29Tg00A^j35Tg00BAR0j22Tg00B\j3@Tg00C6j3ATg00DSj4GTg00Dnj3PTg00EJf0R1g00Ej3@p=1%01#0p=E%01#0#0#0p=I%01#0#0#0#0#0#0#0p=K%01#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=H%01#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=7%41#4p=Bg00FJf1R2;P1p=:%31#3#3#3p=F%31#3#3#3#3#3#3#3p=?%41#4#4#4#4#4#4#4p==%31#3p=J%41#4#4#4p=>p,4GCHKp,2csR3#S#1g00G^,O3#LR4g00I0R5'DR6%R3R7g00JBR8'DR9'6R:%N3R;g00KTR<'DR='6R>%M3R?g00LgR@'DRA'6RBg00N:#E#IRC#E#K#H#7#7#7#7#7#7RD#0RE#Cg00NYRFg00O7RG#4#BRH#83;#<%Q3R3':RI'6RJg00O\?;FF#</:3RK'6RL%CD%3G#F#?#=#=#3#J#8%>HRH#4RD#3#4#>#=#3#B#>#3#>#83;#</:3RM'6RN%0E#E#I#H#7#7#7#7#C%8G7;F#</:3RG'6RE%CC%8H7;F#</:3RH'6RCg00PoRO%4D#BRD#87;F#</:3RF'6RPg00R@RQ%>DRD#3#J#F#?#?#?#8%4D#B#=#=#F#?#83;#</:3RD'6RR1935RS'6RT1938RU'6RV193<RW'6RX193@RY'6RZ193QRQ'6R[193ORO'6R\g00SR,93R3;51%1\R\%13R3'2P0P\P3g00T`R]?@45R^A@]78R_A@];<R`A@]?@R]'2Ra'2Rb'2RcP1A5[O2%1[R[%1ORO'2P0P[POPcP1A5ZQ2%1ZRZ%1QRQ'2P0PZPQPcP1A5XY2%1XRX%1YRY'2P0PXPYPcP1A5VW2%1VRV%1WRW'2P0PVPWPcP1A5TU2%1TRT%1URU'2P0PTPUPcP1A5RS2%1RRR%1SRS'2P0PRPSPcP1A5PD2%1PRP%1DRD'2P0PPPDPcP1A5CF2%1CRC%1FRF'2P0PCPFPcP1A5EH2%1ERE%1HRH'2P0PEPHPcP1A5NG2%1NRN%1GRG'2P0PNPGPcP1A5LM2%1LRL%1MRM'2P0PLPMPcP1A5JK2%1JRJ%1KRK'2P0PJPKPcP1A5BI2%1BRB%1IRI'2P0PBPIPcP1A5>A2%1>R>%1ARA'2P0P>PAPcP1A5:=2%1:R:%1=R='2P0P:P=PcP1A5692%16R6%19R9'2P0P6P9PcP1P^PbAA452P_PaAA781P`P]f59A;<f:9A?@CGCGCGX99X06P2P1O2n2001000000120000000b0X8=X0:P2P1O2n2001000000120000000b0X7AX0>P2P1O2n2001000000121000000b0X6IX0BP2P1O2n2011000000121000000b0X5KX0JP2P1O2n2101000000121000000b0X4MX0LP2P1O2n2111000000121000000b0XAGX0NP2P1O2n2111000000121000000b0X@HX0EP2P1O2n2101000000121000000b0X?FX0CP2P1O2n2101000000121000000b0X>DX0PP2P1O2n2101000000121000000b0X=SX0RP2P1O2n2101000000121000000b0X<UX0TP2P1O2n2101000000121000000b0X;WX0VP2P1O2n2101000000121000000b0X:YX0XP2P1O2n2101000000121000000b0X3QX0ZP2P1O2n2101000000121000000b0X2OX0[P2P1O2n2101000000121000000b0X13X0\P2P1O2n2101000000121000000b0b0o"). Qed.

  #[using="sp brk0 rdraw argv envp uid hw fs GCHK R FULL model HC"] Lemma geo_spb : rbase E cs I_KSPACE < uE E (bK cs) + 0x10000 <= rbase E cs I_KSPACE + 65536 /\ (uE E (bK cs) + 0x10000) mod 65536 = 0.
  Proof.
    destruct geo_syn as (S1 & S2 & _ & _). unfold rbase. rewrite S1, S2. unfold uE.
    remember (bv_unsigned (edenot E E_KB)) as kb eqn:Ekb. remember (bv_unsigned (edenot E E_BK)) as bk eqn:Ebk.
    LINEQ E_KB L1. rewrite <- Ekb in L1. LINEQ E_BK L2. rewrite <- Ebk in L2.
    RANGE (KRange (EVar 225) 0 15) R1. RANGE (KRange (EVar 224) 4295491576 34326181871) R2. RANGE (KRange E_AND 0 0) R3.
    cbn [edenot] in R1, R2. change (bv_unsigned (ev E 225)) with (VZ E 225) in R1. change (bv_unsigned (ev E 224)) with (VZ E 224) in R2.
    (* [comment removed for export] *)
    unfold E_AND in R3. cbn [edenot] in R3. rewrite u_add64, u_and64, !u_mul64 in R3.
    rewrite (u64_lit 65535), (u64_lit 4096) in R3 by lia.
    replace (bv_unsigned (Z_to_bv 64 (-4096))) with 18446744073709547520 in R3 by (vm_compute; reflexivity).
    change (bv_unsigned (ev E 225)) with (VZ E 225) in R3. change (bv_unsigned (ev E 224)) with (VZ E 224) in R3.
    change 65535 with (Z.ones 16) in R3. rewrite Z.land_ones in R3 by lia. change (2 ^ 16) with 65536 in R3.
    rewrite (Z.mod_small (4096 * VZ E 224) (2 ^ 64)) in R3 by lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    assert (HA : (4096 * VZ E 224) mod 65536 = 4096 * VZ E 225) by lia.
    subst kb bk. rewrite L1, L2. split; [|]; lia.
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
    RANGE (KRange (EVar 376) 0 1) R1. RANGE (KRange (EVar 6) 0 255) R2. RANGE (KRange E_R 0 4095) R3. RANGE (KRange E_PG 140735340871680 140737488351232) R4.
    cbn [edenot] in R1, R2. change (bv_unsigned (ev E 376)) with (VZ E 376) in R1. change (bv_unsigned (ev E 6)) with (VZ E 6) in R2.
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
  #[using="sp brk0 rdraw argv envp uid hw fs Hsp Hva cs GCHK R FULL model HC Hve Hfit"] Lemma geo_sp16 : uE E e_sp0 + 16 <= 2 ^ 47.
  Proof.
    unfold uE. remember (bv_unsigned (edenot E e_sp0)) as s0 eqn:Es. LINEQ e_sp0 L3. rewrite <- Es in L3.
    pose proof (hbi_sp0 ASEGS0 ASAN0 APH0 sp rdraw brk0 argv envp uid hw fs Hsp Hva Hve Hfit E cs R FULL model HC) as U0.
    pose proof (build_stack_bytes_within_span APH0 sp argv envp uid hw rdraw) as SPAN.
    destruct (bsb_ge APH0 sp rdraw argv envp uid hw) as [GE _].
    unfold entry_stack_fits, sp_window_hi in Hfit. lia.
  Qed.
End Geo.

(* [comment removed for export] *)
Lemma geo_chk_0 : geo_chk HS_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_EraArtHandoffInstK ()) [] "p;2p;1p;3g00[hj22Tg0000j11Tg00B\j30Tg00EJR0g00EjR1'2g01g?#1=001do"). Qed.
Lemma geo_chk_1 : geo_chk HS_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_EraArtHandoffInstK ()) [] "p;2p;1p;3g00[hj22Tg0000j11Tg00B\j30Tg00EJR0g00EjR1'2g01hG#1=001do"). Qed.
Lemma art_lits_chk_0 : art_lits_chk HS_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_EraArtHandoffInstK ()) [] "p;2p;1p;3g00[hj22Tg01iOj11Tg00B\j30Tg00EJR0g00EjR1'2g01g?#1=001do"). Qed.
Lemma art_lits_chk_1 : art_lits_chk HS_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_EraArtHandoffInstK ()) [] "p;2p;1p;3g00[hj22Tg01iOj11Tg00B\j30Tg00EJR0g00EjR1'2g01hG#1=001do"). Qed.
Lemma art_sym_chk_0 : art_sym_chk HS_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_EraArtHandoffInstK ()) [] "p;2p;1p;3g00[hj22Tg01jcj11Tg00B\j30Tg00EJR0g00EjR1'2g01g?#1=001do"). Qed.
Lemma art_sym_chk_1 : art_sym_chk HS_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_EraArtHandoffInstK ()) [] "p;2p;1p;3g00[hj22Tg01jcj11Tg00B\j30Tg00EJR0g00EjR1'2g01hG#1=001do"). Qed.
Lemma art_lazy_chk_0 : art_lazy_chk HS_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_EraArtHandoffInstK ()) [] "p;2p;1p;3g00[hj22Tg01l8j11Tg00B\j30Tg00EJR0g00EjR1'2g01g?#1=001do"). Qed.
Lemma art_lazy_chk_1 : art_lazy_chk HS_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_EraArtHandoffInstK ()) [] "p;2p;1p;3g00[hj22Tg01l8j11Tg00B\j30Tg00EJR0g00EjR1'2g01hG#1=001do"). Qed.

Section Inst.
  Variable sp brk0 : word.
  Variable rdraw : EntryDraw.
  Variable argv envp : list (list byte).
  Variables uid hw : word.
  Variable fs : Fs.Fs.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  #[local] Notation SINV := (SINV0 APH0 sp rdraw brk0 argv envp uid hw).
  #[local] Notation argH := (argH0 APH0 sp rdraw argv envp uid hw).
  #[local] Notation CSOK := (cs_ok ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs).

  (* [comment removed for export] *)
  Variable BUDGET : Z.
  Hypothesis BUD_ge : 2 ^ 37 + 2 ^ 20 + EarInv.PRIMCAP <= BUDGET.      (* [comment removed for export] *)
  Hypothesis BUD_hi : BUDGET <= 2 ^ 39 - 2 ^ 35.
  (* [comment removed for export] *)
  Let FSH : art_fsinv_handoff := art_fsinv_handoff_proved.

  #[using="BUD_ge"] Lemma inst_bud : 0 <= BUDGET /\ 0 <= EarInv.KMAX /\ 0 <= EarInv.LENMAX < 2 ^ 62.
Proof.
ltac2:(KReplay.run1 (kr_t_EraArtHandoffInstK ()) ["Inst"] "h02Hah14__x1h27__arithh34__ffh46__sat0h56__sat1h67__sat10h77__sat11h87__sat12h97__sat13h:7__sat14h;7__sat15h<6__sat2h=6__sat3h>6__sat4h?6__sat5h@6__sat6hA6__sat7hB6__sat8hC6__sat9hD8__varmaphE5__witp;1p;2p;3p;4p;8p;7g00?bj13Tg00;Rj11Tg00:mj12Tg010Zj26Tg00kTj27Tg011^j35Tg012Bj1LTg012bj1HTg01K?j2FTg013`j1ETg014>j1WTg014ij2?Tg00YNj1:Tg01O3j3CTg01K]j3VTg01<[j2UTg01=>j1QTg01G1j4DTg01L@j8PTg015oj2OTg00[hj2NTg016Qj2KTg00B\j3ITg017=j3JTg017\j4GTg00XQj2@Tg00b>j2MTg01=`j2=Tg011Bj2BTg00BAj28Tg015Lj3RTg01G\j7STg01H@j7TTg00NYR0f0R1'Bp=41=01p=0%31#3p=;g01OVR2f1R3;R1p=9P2P3g01V7P1CDp=>P3g01SQR4g01T0R5P5g01TPR6P1g01UWFSp=<f2R7P4P5P5P6P3P1FTp=Ag00O7R8#3R9#1R:%39R;#2R<#3#2R=#1R>'6%4:R?%0>17:>R@#4[[%0:RAg01\RRBA5:>3UW0%0@\B^0A%2<#2#1R<,6:%0<17:<R>#4[\?A5:<3VBX0A%0>\B^0A%28#2#2R>#2R<#3RC#1RD,6:%0D17:DRE#4[\?A5:D3VBX0A%0E\B^0A%3;R;#2#2#1RD,6:%0D17:DRF#4[\?A5:D3VBX0A%0F\B^0A%3;R;#3RF#1RD,6:%0D17:DRG#4[\?A5:D3VBX0A%0G\B^0A%29#;R9#1RD,6:%0D17:DRH#4[\?A5:D3VBX0A%0H\B^0A%1<RD,6:%0D17:DRI#4[\?A5:D3VBX0A%0I\B^0A%1;RD,6:%0D17:DRJ#4[\?A5:D3VBX0A%0J\B^0Ag01V^RA#L%HA1F23%E2%W2RAP4P5P5P61?2:R:%:='9%:9,9:5C2%3>#1R>,?2%:F,9:5V25C21U28R8'>,<A%Q51?20R5/>8,<A%;F#;#;#;#1RF,?2,>5,<A%:<,9:%:;,9:5C2R;,>5,<AP2P;g01U0%:C,9:CD,<A5AA5AA5AAGP1OA6P1P7g00EJRAg00EjR6'N1K17=IA6dAJ203CGb3bDbEX121@@H1M>G'@/=1%03%0F1@IJRJ#01BJE'8'8'8[^12P1p,6BUDGETR1p,6BUD_geO2b2b4b5b<b=b>b?b@bAbBbCb6b7b8b9b:b;%01g01mN,=0g01nTR1,=01B1E'8'8'8eo"). Qed.

  #[using="Hsp Hva Hve Hfit BUD_ge BUD_hi FSH"] Theorem as0_art_handoff_h : forall h, (h < 2)%nat -> forall E R FULL model, CSOK E (HSA h) R FULL model ->
    art_handoff_target art_fsg (vm_maps (m_vmmaps model)) (segments_reserved ASEGS0) (vm_noaccess (m_vmmaps model))
      (as0_BASEx (HSA h) E) BUDGET art_fsinv (as0_rn E (HSA h)) art_fsg0 K0D EarInv.KCNT (2 ^ 37) (as0_A0x (HSA h) E) FULL (vml_of model).
Proof.
ltac2:(KReplay.run1 (kr_t_EraArtHandoffInstK ()) ["Inst"] "p'0h02Hah12HCh22Hhh34__x1h41Hh54__x2h63Hh0h77__arithh84__ffh98__varmaph:5__with;4cstrh<2N0h=4__p1h>7__sat17h?7__sat18h@7__sat19hA7__sat20hB7__sat21hC7__sat22hD7__sat23hE7__sat24hF7__sat25hG7__sat26hH7__sat27hI7__sat28hJ7__sat29hK7__sat30hL4__x3hM5cstr0hN1hhO1ni001nhP1xhQ2BLhR2C0hS2CGhT2CHhU2CLhV2CShW2CZhX1EhY4FULLhZ3G16h[2GAh\2GPh]2GSh^2GTh_2N1h`2N2ha2N3hb2N4hc1Rhd6__sat0he6__sat1hf6__sat2hg6__sat3hh7__sat31hi7__sat32hj7__sat33hk7__sat34hl6__sat4hm6__sat5hn6__sat6ho6__sat7hp1ahq1lhr5modelhs1yp%0p&0p;1p;2p;8p;7p;4p;3p;6p;?p;Cp;Op;;p;<g009<R0j1ATg01o\R1j2OTg00?bj10Tg00:mj15Tg00YNj1NTg01aik109Tg0204k20WTg020`k10QTg00\Bk80OTg00]Lk70NTg021Bj11Tg022Pj1gTg01iOj1\Tg00BAR2j29Tg00DSj4KTg01d2R3j17Tg00;Rj14Tg011BR4j2_Tg00XQj23Tg023^j4iTg01fZj1hTg010Zj2ITg00kTj2JTg011^j3GTg012Bk101Tg012bk10@Tg013Bk10dTg01K?j2}Tg01MMk400Tg013`k10]Tg014>k10\Tg014ik20:Tg01<[j2|Tg01=>k10[Tg01G1k408Tg01Mkk60YTg015ok20XTg00[hk207Tg016Qk20VTg017=k30TTg017\k40STg01jcj1oTg024Ej1XTg025<j1UTg0262k10RTg0270j1WTg027jj2YTg029=j2ZTg02:Mj2VTg02;^j1]Tg02<jk20PTg02>@j1aTg02?Pj1TTg02@`j1ETg01=`j28Tg02B1m?0MTg00V2k30LTg0056k10KTg00W@j2dTg00Xnj2xTg02CFm?0ITg006`k10HTg007nk10GTg00B\j36k103Tg01^7k204Tg02D[mC0ETg02F1m?0DTg02GFk20CTg02Gik30JTg01:Zj2vTg01J6j3zTg01;Ck202Tg01J_j3^Tg015Lj3lTg01^Tk30BTg02HFk20ATg01cRj2nTg02Hfj2pTg00b>j2bTg00hNj2LTg02I=j4rTg01K]k30fTg00c<k60?Tg02I]mO0eTg02K6m;0cTg0000k10>Tg01l8k10;Tg02LLm<0bTg02M1m<0=Tg01G\k70<Tg01O3k30_Tg01L@k80^Tg02MVm?0`Tg02Njk10aTg01P4R5g01Q>g01RGR6f7R7f6R8f5R9f4R:f3R;f2R<f1R=f0R>N;0cp=fg00EJR?&0>=g00EjR@36&0;>=6?@'9p=C%o==6?@/9>p=eA6?<@A6?=@/9>'9p=c%g>=6?@p=u%\>=6?@p=t%o>=6?@p=s&0>>=6?@p=q&0;>=6?@p=m13<=/3>p=jg01OVRA007>p=Qg02P9RBPBPAPAP0P3P3P;g02PXP<P=P>N<0bp>06PBPAP1P3P4g02Q<P9P:P;P<P=P>N<0=p=~g00NYR4/8>p=21_4>p=DP<g01SQR1g01T0R0P0g01TPRCPAP=g01V7P>H08g01UWRDK0<p=M20:A>p==B0_A=>p=<P=P1P0P0PCP>PDK0<p>0ZP;P1P0P0PCP<P=P>L0^p=[A6?>@p>0U%A>#Ap=Pg02Q^P>P=P<P;P:g02RkP9g02T8g02UDg02VQP8P7f8RDf9REN?0`p=S%0>#0p=;%0>#0#0#0#0#0#0#0p=k%0>#5p=`%5>#5p=:%5>#0p=?%0>#0#0#0#0#0#0#0#0#0#0#4p=H%0>#0#0#0#0#0#0#4p={%0>#5#0#5p=Rg02WW&0a>'np=@A6B=>p=B18<=/9>p=>%0>#0#0#0p=yA6A>4p=w19=>,9<p>0F13<=/8>p=FPBPAP>P3P=P<P;P:P9P8P7PDN<0=p>05g00N:R3#ARF#ARG,O>RHg02Xfg00O7RI#0RJ#5RK#N%0JRL#0RM#0RN#0RO#0RP#NRQ$09RR+0W%NM$09$0Q\Rg02Z7g01YFRSp,2spRTp,5rdrawRUp,4brk0RVp,4argvRWp,4envpRXp,3uidRYp,2hwRZL0OR[PSPTPUPWPXPYPZK0NRSp,2fsR\P;%19P<P=P>GfPBP[PSP\P8%1=P9P:P;Gf%1<R]#g%\]1C]],e]3c]1^2HP81O3GP[PSP\P9%13P:P;P<Gfg01g?RH#u%tHR]%sHR^%qHR_%mHRH'9R`'9Ra'9g02ZmP]Pag02\AP^P`g02]]P_PHg02_8g02`OCKCKCKCKW1W2PB%A>RH/OGP[PSP\PD%A=R_#1P7P8P9Gf%A<R`#1R^#g%\^1C^^,e^3c]1]2P>1OFGP[PSP\P7%1FP8P9P:Gfg01hGR^#u%t^Ra%s^R]%q^Rb%m^R^'9Rc'9Rd'9g02akPaPdg02c?P]Pcg02d[PbP^g02f6g02gMCKCKCKCKW1W2%AH/OGP[PSP\PE%A_#1PDP7P8Gf%A`R_/OG%7<RS%4IR[;j[%4JRH'_R^P_13>[XPAR_P_PSO1RbO1P_P`PbP_P<PS%QSH06H06PGPH%QHS00E~P=CiP^%h;%7;#2%5LRL#0R^#5#4RS,IHS01%DHR_%2S1JHSRb#D[[S02%2HR`g01\RRcAGHS=UW0S03%2b\c^0`S04%5LRL#5RS#4R],IHS05%2]1JH]Rd#D[\_S06AGH]=VcX0`S07%2d\c^0`S08%5MRM#5R]#4Ra,IHS09%2a1JHaRe#D[\_S0:AGHa=VcX0`Ra%2e\c^0`Rf%0KRg#0Rh#4Ri,IHRj%2i1JHiRk#D[\_RlAGHi=VcX0`Ri%2k\c^0`Rkp-0Rmg01V^Rn$01Ro&0@nS0;PA&0dAS0<P=1}A=H00&0]AS0=&0\ARp20:A4%5IRq,|ARr5Mp&0[0RsPpPA%=[Rt,<r/<tg01U0%=HRtH08-0ZpPsPpP1P0P0PCP;J0YC[C[20XpCS0>P>P<207?@20V><$0UdB0TA4=H0SS0?b8b9b:X3AW=%2>Aj=[[/_HP;[[^3A^=mP>f=Rm#P#1R[#g%\[1C[[,e[3c%7mPEf:R[O4b7bdbebfbgblbmbnbob;b6W1W2XNBP>O1n0110000020011100XOBP>O1n0110000020011100P9P>O2%18R4#g%\41C44,e43cP2%17R4#u%\4%o41C443c%X;R4#U&0R5R5%W4%1DR4/Y8p,6BUDGETR@1Z84Pb1V48P:%];M:SP>%1E#u%1[RE#\%oE1CEE3cP2f;RE#1R4#t1C44,e4%X7R4#UP5%W4f<R4#1R8/Y[P@1Z[8Pb1V8[PD%]7M:SP>%1m#tf>Rm#1R71C77'eP2f?R7#1RD#s1CDD%XERD#UP5%WDf@RD#1R8/YmP@1Zm8Pb1V8mP4%]EM:SP>fAS0@#1#sfBRE#1R4/C4P2fCS0A#1R4#q%m4%X7R4#UP5%W4fDR4#1R8/YEP@1ZE8Pb1V8EPD%]7M:SP>fER8#1#qfFRE#1#mfGR[00PE%1[RE#a%5P#;#k#`#;#:#;#?#:#;#?#HR?%TE%5qRq#:RC#5R0#0#;#k#{R1%EE%`^#R#?#?#?#;#?#HR^%@E%AGRE#P#P#P#P#P#P#PRu'B3>3>3>P2fHRv#1Rw#a/8?%Tw%Ew%@w/Bu7>^7>1%X4Rw#UP5%WwfIRw#1Rx/Y[P@1Z[xPb1Vx[P8%]4M:SP>fJ#1#a/8?fKR4#1R8#T%E8%@8/Bu7>^7>1P2fLR8#1Rx#T/81%Ex%@x/Bu7>^%XvRx#UP5%WxfMRx#1R[/Y4P@1Z4[Pb1V[4Pw%]vM:SP>fNRw#1#T/81fOR[#1R4#E%@4/Bu7>^P2fPR2#1R4#E/8^%@4/Bu%X8R4#UP5%W4fQR4#1Ry/Y[P@1Z[yPb1Vy[Px%]8M:SP>fRRx#1#E/8^fSRy#1#@/BuPTPVPUPWPXPYPZP\fTRb#1RzPmPxP4P2P[PwN?0Mg00G^:0LxzRw&0Kz,dx%;P#yRP#0Rz#;Rm#0R{#4R|'3R}'_13w|,8}'91x}|#w'9PTPVPUPWPXPYPZP\fUR}#1RwP7PyPxP4P2P[N?0I&0Hw,dyR[&0Gw,dyRw%0{#;#yR{#4R7'356A%4PRP,xw#wg00SRR~,dy0047R713wP137P%5K#:#4RK,JHR7,8[5>w3>40FPTPVPUPWPXPYPZP\p,3HspS0Bp,3HvaS0CfVS0D#1PDPbPyPxP4P2p,3Hvep,4HfitNC0E1db~%4NRD;F7PTPVPUPWPXPYPZP\fWS0E#1Q0@P}PbPyPxP4N?0D1d}~/xD#wfXR~#1R4#@Rx/Bu%7xRy%4MRw56AR[&03BS0@&03AS0F%7=%7>56A1B=>20C=>40JXsBXPBS0GPxPy%QyPuPw%QwS0HN905P:CiP[fYR[/OG%7[Ry/_HRxP[Py%QyPGPHQ00E~P~CiPxfZRx#1Ry#@RP#h%7P#2f[RP#h%7P#2Q01Q02Q03Q04Q05Q06Q07Q081IHKS0I%2K%D7[\_S0JAGHK=VcX0`S0K%27\c^0`S0LQ09Q0:PaPf%4OR7,IHS0M%271JH7RK#D[\_S0NAGH7=VcX0`S0O%2K\c^0`S0P%0MRM#4RK,IHS0Q%2K1JHKR7#D[\_S0RAGHK=VcX0`S0S%27\c^0`S0TPjPlPiPk1vAE1vAG1vAF1vA35zA5zAR35zAg01\nRF+02=^noQ0;PA1}A<S0UP=1}A;H00Q0=Pp1|AJRJ%=^5MpPsPp1|AIRI%=15MpPsPp%NS9lAt%N]9lAt60BAR]9MprPs1<IJRE%NM9lAt'</<r%0{#k#{R{#=5MpC[C[C[Q0>Q0?b8b9b:X3AX5AXLA18=^18=1204deRe,8:Aj;:7?F9{[[[^3A^5A^LAP>P@fk#1R{#E%T{PvP8p,6BUD_hiS0VO6b7b>b?b@bAbBbCbDbEbFbGbHbIbJbKbMb;b6b<%T4%E4;j7?F@6R6eP6PBPug02hig01nTR6'3R7%ay/3@'3R420ARRR{/n5Rd/p>#7g01mNR1'3%:0#:#:R0#4R^,36Rr'bg02j;RM3FXOB&0@{RKPRPR1LQ|%?O#H,LQCrPRPR%0h#?#H,LQ%yq#?#H,LQCrPRPR%0L#`#;#H,LQ%4m,LQCrPRPR%`S#;#H,LQ%5gRg#`RS#5#:#;#H,LQCr&01{5^{5^{5^{5^{RQ1n{>/pu#7/31/br=F4MXqK%1[RK#@R4/Bu%74RR=6AwRmQ0@Q0FQ0GP4PR%QRPuPwQ0HN905P9CiPm1OxG%7xRm/_HRwPxPm%QmPGPHQ00E~P[CiPw%1P#@RP#h%7P#2f\RP#h%7P#2Q01Q02Q03Q04Q05Q06Q07Q08Q0IQ0JQ0KQ0LQ09Q0:PaPfQ0MQ0NQ0OQ0PQ0QQ0RQ0SQ0TPjPlPiPk%4CRk,IH%2k1JHkRi#D[\_AGHk=VcX0`%2i\c^0`1IHD%2D1JHDRk#D[\_AGHD=VcX0`%2k\c^0`2023F=^noQ0;PAQ0UP=Q0<H00Q0=Pp%=?9MpIPsPpAMpJ]Ps%`S#R#R#R#R#R#R#?#HRS#=%NC9lAt%NN9lAt'<Rt'</<E%4gRg#=%4zRz#='<%=^,<t60fA'<%:0#?#:#:#:#:#k#k#{R0#=5MpC[C[Q0>Q0?b8b9b:X3AX5A18>?18<e13ikRk13<;5jS13gz13k^'b;F0[[^3A^5AP>P@fp#1#aP}Q0VO4b7b>b?b@bAbBbCbDbEbFbGbHbIbJbKbhbibjbkbMb;b6b<%aK/3@,37R713g1/br;FMe1n{Q/pu#7/31/br=F7MeP5g02kLJ0?P4P9J0?1pd4#7/31/br=F7MPTPVPUPWPXPYPZP\Q0BQ0CPyP2P8PvP~Q0EQ0DP}PbP9P:P;P<P@P6g02lbP=p,6BUD_geP>Q0Ap,3FSHNO0eb\bQb[bZb^b]WbWaP=P>O2n2001000000121000000W4W`P=P>O2n2001000000121000000W4W_P=P>O2n2001000000121000000bpWWWSP=P>O2n2001000000121000000W4WVP=P>O2n2001000000121000000W4WUP=P>O2n2001000000121000000W4WRP=P>O2n2001000000121000000bTW1WrWYWcWXW2XNBo"). Qed.
End Inst.
