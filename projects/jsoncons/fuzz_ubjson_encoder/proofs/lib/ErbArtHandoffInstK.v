(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PropExec AgentLib AxSymExec3K AxSymExec3SoundK AxSymRun3K
  AsanPlanCoreK AsanPlanK AsanPlanSoundK AsanInitK Eb0DefsK Eb0PlanImagesK HandoffBridgeK HandoffLedgerK HandoffBInvK HandoffCellsK HandoffRolesK
  Eb0HandoffK Eb0ArtCellsK ErbArtHandoffK Eb0HSK_0 Eb0HSK_1 Eb0MainTableK Eb0HandoffInstK.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import HeapIface HeapIfaceA HeapIfaceAEx ArtRuns ArtBridge EbrInv EbrFsInv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_ErbArtHandoffInstK () := "c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3libBErbArtHandoffInstK7geo_chkC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=HandoffRolesK4roleC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9AsanPlanK3APK7am_baseC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;AxSymExec3K4AX2K8expr_eqbC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>ErbArtHandoffK2bKC13~~~C47Corelib4Init9Datatypes4andbC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>ErbArtHandoffK4topEC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>ErbArtHandoffK4botEC13~~~K47Corelib4Init9Datatypes3nat02K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;AxSymExec3K4AX2K4expr02C13~~~K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;AxSymExec3K4AX2K6kentry06C13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9AsanPlanK3APK:kentry_eqbC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9AsanPlanK3APK2knC13~~~K47Corelib7Numbers7BinNums8positive02C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;AxSymExec3K4AX2K;lin_nowrapRC13~~~C47Corelib4Init9Datatypes9andb_propI47Corelib4Init5Logic3and00I47Corelib4Init5Logic2eq00C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@AxSymExec3SoundK5AX2SK;expr_eqb_eqC13~~~K47Corelib4Init5Logic3and01C46Stdlib5Lists4List7existsbI47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;AxSymExec3K4AX2K6kentry00C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>ErbArtHandoffK8I_KSPACEC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3libBErbArtHandoffInstK4E_KBC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3libBErbArtHandoffInstK4E_BKC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3libBErbArtHandoffInstK5E_TOPC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3libBErbArtHandoffInstK5E_BOTC13~~~K47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3libBErbArtHandoffInstK5E_ANDC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3libBErbArtHandoffInstK3E_RC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3libBErbArtHandoffInstK4E_PGC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9AsanPlanK3APK5e_sp0C13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;AxSymExec3K4AX2K4expr00C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=HandoffRolesK5rbaseC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>AsanPlanSoundK4APSK2uEC13~~~C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z6moduloK47Corelib7Numbers7BinNums1N02C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;AxSymExec3K4AX2K6edenotC13~~~C45stdpp9bitvector;definitions;bv_unsignedK47Corelib4Init5Logic2eq01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9AsanInitK5SINV0C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9AsanInitK5argH0C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>HandoffBridgeK6hb_linC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>HandoffBridgeK2LZC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>HandoffBridgeK2VZC13~~~C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z7add_0_rC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums1Z03C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>HandoffBridgeK9hb_knb_InC13~~~C46Stdlib5Lists4List2InC89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>AsanPlanSoundK4APSK2MrC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@AxSymExec3SoundK5AX2SK9kentry_okC13~~~C45stdpp9bitvector;definitions7Z_to_bvC89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;AxSymExec3K4AX2K2evC13~~~C4ELinuxProcessSemantics5Riscv3Sem7mul_divC4ELinuxProcessSemantics5Riscv3Sem5alu64C56Stdlib6ZArith6BinInt1Z3powC89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@AxSymExec3SoundK5AX2SK7u_add64C13~~~C56Stdlib6ZArith6BinInt1Z4landC89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@AxSymExec3SoundK5AX2SK7u_and64C13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@AxSymExec3SoundK5AX2SK7u_mul64C13~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AgentLib7u64_litC13~~~C56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z9land_onesK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z9mod_smallC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega7EnvRing3Pol01C56Stdlib6ZArith6BinInt1Z<eq_decidableI47Corelib4Init5Logic2or00K46Stdlib9micromega5Tauto8GFormula06C47Corelib4Init5Logic6eq_indC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>HandoffBridgeK5hb_knC13~~~K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega=RingMicromega5Psatz06K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr03I47Corelib7Numbers7BinNums1Z00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8Eb0DefsK6ASEGS0C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8Eb0DefsK5ASAN0C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9AsanInitK5LIMITC13~~~C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op201c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3libBErbArtHandoffInstK7geo_synC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8Eb0DefsK4APH0C13~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5mulop01K4ELinuxProcessSemantics5Riscv5Instr5aluop0:I47Corelib4Init5Logic4True00K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init5Logic5False00C56Stdlib6ZArith6BinInt1Z3subK46Stdlib9micromega7EnvRing5PExpr04C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>HandoffBridgeK7hbi_sp0C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExecMbuild_stack_bytes_within_spanC13~~~I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics?LinuxProcessSem;StackLayoutAbuild_stack_bytesC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC4ELinuxProcessSemantics?LinuxProcessSem3Run@entry_stack_spanC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9AsanInitK6bsb_geC13~~~C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8Eb0HSK_04HS_0C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8Eb0HSK_14HS_1C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eb0ArtCellsK<art_lits_chkC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>ErbArtHandoffK;art_sym_chkC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>ErbArtHandoffK<art_lazy_chkC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6EbrInv4KMAXC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6EbrInv6LENMAXC13~~~C47Corelib4Init5Peano2ltC4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes6option00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Eb0HandoffInstK3HSAC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Eb0HandoffK7as0_chkC13~~~C46Stdlib9micromega;ZifyClasses7rew_iffC4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC4ELinuxProcessSemantics?LinuxProcessSem5State7vm_mapsC4ELinuxProcessSemantics?LinuxProcessSem3RunAsegments_reservedC4ELinuxProcessSemantics?LinuxProcessSem5State;vm_noaccessC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>ErbArtHandoffK9as0_BASExC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>ErbArtHandoffK6as0_rnC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>ErbArtHandoffK7as0_A0xC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA6vml_ofC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Eb0HandoffInstK;HSA_numbersC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9AsanPlanK3APK7a_totszC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9AsanPlanK3APK7a_eagerC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9AsanPlanK3APK8a_abytesC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3libBErbArtHandoffInstK7geo_spbC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3libBErbArtHandoffInstK7geo_stkC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3libBErbArtHandoffInstK8geo_sp16C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3libBErbArtHandoffInstK7geo_spaC13~~~C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symI47Corelib4Init9Datatypes4prod00C47Corelib4Init3Nat3addK47Corelib4Init9Datatypes4prod01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>ErbArtHandoffK?as0_art_handoffC13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>AsanPlanSoundK4APSK5cs_ok00C13~~~C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6EbrInvBart_handoff_targetC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9AsanPlanK3APK6a_mapsC13~~~I47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z8inj_succC56Stdlib6ZArith4Znat5Nat2Z6inj_ltI79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8EbrFsInv7art_fsg00C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8EbrFsInv9art_fsinvC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8EbrFsInv8art_fsg0C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>ErbArtHandoffK3K0DC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6EbrInv4KCNTC13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9AsanPlanK3APK4amap00C13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;AxSymExec3K4AX2K3env00C13~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Eb0HandoffInstK9as0_chk_0C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3libBErbArtHandoffInstK>art_lits_chk_0C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3libBErbArtHandoffInstK=art_sym_chk_0C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3libBErbArtHandoffInstK9geo_chk_0C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3libBErbArtHandoffInstK>art_lazy_chk_0C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Eb0HandoffInstK9as0_chk_1C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3libBErbArtHandoffInstK>art_lits_chk_1C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3libBErbArtHandoffInstK=art_sym_chk_1C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3libBErbArtHandoffInstK9geo_chk_1C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3libBErbArtHandoffInstK>art_lazy_chk_1C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanCeil>bottomup_floorC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanCeil=alloc_ceilingC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>Eb0PlanImagesK<asan0_res_eqC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3libBErbArtHandoffInstK8inst_budC13~~~". Local Ltac lia := L5FastLiaT.plia2.
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
ltac2:(KReplay.run1 (kr_t_ErbArtHandoffInstK ()) ["Geo"] "h01Gh11Hh22H0h32H1h43H10h53H11h63H12h73H13h83H14h93H15h:2H2h;2H3h<2H4h=2H5h>2H6h?2H7h@2H8hA2H9p;1p;2p;3p;4g0000j1STg001Ej2OTg002Rj1LTg003bj2DTg0056j1RTg006Bj26Tg006`j1NTg007nj1MTg009<j10Tg009[j1CTg00:mj14Tg00;Rj18Tg00<0j3;Tg00=Dj1<Tg00>Wj1QTg00?bj13Tg00@Gj29Tg00A^j35Tg00BAR0j22Tg00B\j3@Tg00C6j3ATg00DSj4GTg00Dnj3PTg00EJf0R1g00Ej3@p=1%01#0p=E%01#0#0#0p=I%01#0#0#0#0#0#0#0p=K%01#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=H%01#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=7%41#4p=Bg00FJf1R2;P1p=:%31#3#3#3p=F%31#3#3#3#3#3#3#3p=?%41#4#4#4#4#4#4#4p==%31#3p=J%41#4#4#4p=>p,4GCHKp,2csR3#S#1g00G^,O3#LR4g00I0R5'DR6%R3R7g00JBR8'DR9'6R:%N3R;g00KTR<'DR='6R>%M3R?g00LgR@'DRA'6RBg00N:#E#IRC#E#K#H#7#7#7#7#7#7RD#0RE#Cg00NYRFg00O7RG#4#BRH#83;#<%Q3R3':RI'6RJg00O\?;FF#</:3RK'6RL%CD%3G#F#?#=#=#3#J#8%>HRH#4RD#3#4#>#=#3#B#>#3#>#83;#</:3RM'6RN%0E#E#I#H#7#7#7#7#C%8G7;F#</:3RG'6RE%CC%8H7;F#</:3RH'6RCg00PoRO%4D#BRD#87;F#</:3RF'6RPg00R@RQ%>DRD#3#J#F#?#?#?#8%4D#B#=#=#F#?#83;#</:3RD'6RR1935RS'6RT1938RU'6RV193<RW'6RX193@RY'6RZ193QRQ'6R[193ORO'6R\g00SR,93R3;51%1\R\%13R3'2P0P\P3g00T`R]?@45R^A@]78R_A@];<R`A@]?@R]'2Ra'2Rb'2RcP1A5[O2%1[R[%1ORO'2P0P[POPcP1A5ZQ2%1ZRZ%1QRQ'2P0PZPQPcP1A5XY2%1XRX%1YRY'2P0PXPYPcP1A5VW2%1VRV%1WRW'2P0PVPWPcP1A5TU2%1TRT%1URU'2P0PTPUPcP1A5RS2%1RRR%1SRS'2P0PRPSPcP1A5PD2%1PRP%1DRD'2P0PPPDPcP1A5CF2%1CRC%1FRF'2P0PCPFPcP1A5EH2%1ERE%1HRH'2P0PEPHPcP1A5NG2%1NRN%1GRG'2P0PNPGPcP1A5LM2%1LRL%1MRM'2P0PLPMPcP1A5JK2%1JRJ%1KRK'2P0PJPKPcP1A5BI2%1BRB%1IRI'2P0PBPIPcP1A5>A2%1>R>%1ARA'2P0P>PAPcP1A5:=2%1:R:%1=R='2P0P:P=PcP1A5692%16R6%19R9'2P0P6P9PcP1P^PbAA452P_PaAA781P`P]f59A;<f:9A?@CGCGCGX99X06P2P1O2n2001000000120000000b0X8=X0:P2P1O2n2001000000120000000b0X7AX0>P2P1O2n2001000000121000000b0X6IX0BP2P1O2n2011000000121000000b0X5KX0JP2P1O2n2101000000121000000b0X4MX0LP2P1O2n2111000000121000000b0XAGX0NP2P1O2n2111000000121000000b0X@HX0EP2P1O2n2101000000121000000b0X?FX0CP2P1O2n2101000000121000000b0X>DX0PP2P1O2n2101000000121000000b0X=SX0RP2P1O2n2101000000121000000b0X<UX0TP2P1O2n2101000000121000000b0X;WX0VP2P1O2n2101000000121000000b0X:YX0XP2P1O2n2101000000121000000b0X3QX0ZP2P1O2n2101000000121000000b0X2OX0[P2P1O2n2101000000121000000b0X13X0\P2P1O2n2101000000121000000b0b0o"). Qed.

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
ltac2:(KReplay.run1 (kr_t_ErbArtHandoffInstK ()) [] "p;2p;1p;3g00[hj22Tg0000j11Tg00B\j30Tg00EJR0g00EjR1'2g01g?#1=001do"). Qed.
Lemma geo_chk_1 : geo_chk HS_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_ErbArtHandoffInstK ()) [] "p;2p;1p;3g00[hj22Tg0000j11Tg00B\j30Tg00EJR0g00EjR1'2g01hG#1=001do"). Qed.
Lemma art_lits_chk_0 : art_lits_chk HS_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_ErbArtHandoffInstK ()) [] "p;2p;1p;3g00[hj22Tg01iOj11Tg00B\j30Tg00EJR0g00EjR1'2g01g?#1=001do"). Qed.
Lemma art_lits_chk_1 : art_lits_chk HS_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_ErbArtHandoffInstK ()) [] "p;2p;1p;3g00[hj22Tg01iOj11Tg00B\j30Tg00EJR0g00EjR1'2g01hG#1=001do"). Qed.
Lemma art_sym_chk_0 : art_sym_chk HS_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_ErbArtHandoffInstK ()) [] "p;2p;1p;3g00[hj22Tg01jcj11Tg00B\j30Tg00EJR0g00EjR1'2g01g?#1=001do"). Qed.
Lemma art_sym_chk_1 : art_sym_chk HS_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_ErbArtHandoffInstK ()) [] "p;2p;1p;3g00[hj22Tg01jcj11Tg00B\j30Tg00EJR0g00EjR1'2g01hG#1=001do"). Qed.
Lemma art_lazy_chk_0 : art_lazy_chk HS_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_ErbArtHandoffInstK ()) [] "p;2p;1p;3g00[hj22Tg01l8j11Tg00B\j30Tg00EJR0g00EjR1'2g01g?#1=001do"). Qed.
Lemma art_lazy_chk_1 : art_lazy_chk HS_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_ErbArtHandoffInstK ()) [] "p;2p;1p;3g00[hj22Tg01l8j11Tg00B\j30Tg00EJR0g00EjR1'2g01hG#1=001do"). Qed.

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
  Hypothesis BUD_ge : 2 ^ 37 + 2 ^ 20 + EbrInv.PRIMCAP <= BUDGET.      (* [comment removed for export] *)
  Hypothesis BUD_hi : BUDGET <= 2 ^ 39 - 2 ^ 35.
  (* [comment removed for export] *)
  Let FSH : art_fsinv_handoff := art_fsinv_handoff_proved.

  #[using="BUD_ge"] Lemma inst_bud : 0 <= BUDGET /\ 0 <= EbrInv.KMAX /\ 0 <= EbrInv.LENMAX < 2 ^ 62.
Proof.
ltac2:(KReplay.run1 (kr_t_ErbArtHandoffInstK ()) ["Inst"] "h02Hah14__x1h27__arithh34__ffh46__sat0h56__sat1h67__sat10h77__sat11h87__sat12h97__sat13h:7__sat14h;7__sat15h<6__sat2h=6__sat3h>6__sat4h?6__sat5h@6__sat6hA6__sat7hB6__sat8hC6__sat9hD8__varmaphE5__witp;1p;2p;3p;4p;8p;7g00?bj13Tg00;Rj11Tg00:mj12Tg010Zj26Tg00kTj27Tg011^j35Tg012Bj1LTg012bj1HTg01K?j2FTg013`j1ETg014>j1WTg014ij2?Tg00YNj1:Tg01O3j3CTg01K]j3VTg01<[j2UTg01=>j1QTg01G1j4DTg01L@j8PTg015oj2OTg00[hj2NTg016Qj2KTg00B\j3ITg017=j3JTg017\j4GTg00XQj2@Tg00b>j2MTg01=`j2=Tg011Bj2BTg00BAj28Tg015Lj3RTg01G\j7STg01H@j7TTg00NYR0f0R1'Bp=41=01p=0%31#3p=;g01OVR2f1R3;R1p=9P2P3g01V7P1CDp=>P3g01SQR4g01T0R5P5g01TPR6P1g01UWFSp=<f2R7P4P5P5P6P3P1FTp=Ag00O7R8#3R9#1R:%39R;#2R<#3#2R=#1R>'6%4:R?%0>17:>R@#4[[%0:RAg01\RRBA5:>3UW0%0@\B^0A%2<#2#1R<,6:%0<17:<R>#4[\?A5:<3VBX0A%0>\B^0A%28#2#2R>#2R<#3RC#1RD,6:%0D17:DRE#4[\?A5:D3VBX0A%0E\B^0A%3;R;#2#2#1RD,6:%0D17:DRF#4[\?A5:D3VBX0A%0F\B^0A%3;R;#3RF#1RD,6:%0D17:DRG#4[\?A5:D3VBX0A%0G\B^0A%29#;R9#1RD,6:%0D17:DRH#4[\?A5:D3VBX0A%0H\B^0A%1<RD,6:%0D17:DRI#4[\?A5:D3VBX0A%0I\B^0A%1;RD,6:%0D17:DRJ#4[\?A5:D3VBX0A%0J\B^0Ag01V^RA#L%HA1F23%E2%W2RAP4P5P5P61?2:R:%:='9%:9,9:5C2%3>#1R>,?2%:F,9:5V25C21U28R8'>,<A%Q51?20R5/>8,<A%;F#;#;#;#1RF,?2,>5,<A%:<,9:%:;,9:5C2R;,>5,<AP2P;g01U0%:C,9:CD,<A5AA5AA5AAGP1OA6P1P7g00EJRAg00EjR6'N1K17=IA6dAJ203CGb3bDbEX121@@H1M>G'@/=1%03%0F1@IJRJ#01BJE'8'8'8[^12P1p,6BUDGETR1p,6BUD_geO2b2b4b5b<b=b>b?b@bAbBbCb6b7b8b9b:b;%01g01mN,=0g01nTR1,=01B1E'8'8'8eo"). Qed.

  #[using="Hsp Hva Hve Hfit BUD_ge BUD_hi FSH"] Theorem as0_art_handoff_h : forall h, (h < 2)%nat -> forall E R FULL model, CSOK E (HSA h) R FULL model ->
    art_handoff_target art_fsg (vm_maps (m_vmmaps model)) (segments_reserved ASEGS0) (vm_noaccess (m_vmmaps model))
      (as0_BASEx (HSA h) E) BUDGET art_fsinv (as0_rn E (HSA h)) art_fsg0 K0D EbrInv.KCNT (2 ^ 37) (as0_A0x (HSA h) E) FULL (vml_of model).
Proof.
ltac2:(KReplay.run1 (kr_t_ErbArtHandoffInstK ()) ["Inst"] "p'0h02Hah12HCh22Hhh34__x1h41Hh54__x2h63Hh0h77__arithh84__ffh98__varmaph:5__with;4cstrh<2N0h=4__p1h>7__sat17h?7__sat18h@7__sat19hA7__sat20hB7__sat21hC7__sat22hD7__sat23hE7__sat24hF7__sat25hG7__sat26hH7__sat27hI7__sat28hJ7__sat29hK7__sat30hL4__x3hM5cstr0hN1hhO1ni001nhP1xhQ2BLhR2C0hS2CGhT2CHhU2CLhV2CShW2CZhX1EhY4FULLhZ3G16h[2GAh\2GPh]2GSh^2GTh_2N1h`2N2ha2N3hb2N4hc1Rhd6__sat0he6__sat1hf6__sat2hg6__sat3hh7__sat31hi7__sat32hj7__sat33hk7__sat34hl6__sat4hm6__sat5hn6__sat6ho6__sat7hp1ahq1lhr5modelhs1yp%0p&0p;1p;2p;8p;7p;4p;3p;6p;?p;Cp;Op;;p;<g009<R0j1@Tg01o\R1j2OTg00?bj10Tg00:mj14Tg00YNj1NTg01aik109Tg0204k20WTg020`k10QTg00\Bk80OTg00]Lk70NTg021Bj11Tg022Pj1fTg01iOj1\Tg00BAR2j2:Tg00DSj4KTg01d2R3j17Tg00;Rj15Tg011BR4j2_Tg00XQj23Tg023^j4hTg01fZj1gTg010Zj2ITg00kTj2JTg011^j3HTg012Bk100Tg012bk10@Tg013Bk10dTg01K?j2|Tg01MMj4~Tg013`k10]Tg014>k10\Tg014ik20:Tg01<[j2{Tg01=>k10[Tg01G1k408Tg01Mkk60YTg015ok20XTg00[hk207Tg016Qk20VTg017=k30TTg017\k40STg01jcj1oTg024Ej1XTg025<j1UTg0262k10RTg0270j1WTg027jj2YTg029=j2ZTg02:Mj2VTg02;^j1STg02<jk20PTg02>@j1`Tg02?Pj1QTg02@`j1FTg01=`j28Tg02B1m?0MTg00V2k30LTg0056k10KTg00W@j2cTg00Xnj2xTg02CFm?0ITg006`k10HTg007nk10GTg00B\j36k102Tg01^7k203Tg02D[mC0ETg02F1m?0DTg02GFk20CTg02Gik30JTg01:Zj2vTg01J6j3yTg01;Ck201Tg01J_j3^Tg015Lj3kTg01^Tk30BTg02HFk20ATg01cRj2nTg02Hfj2pTg00b>j2aTg00hNj2LTg02I=j4rTg01K]k30fTg00c<k60?Tg02I]mO0eTg02K6m;0cTg0000k10>Tg01l8k10;Tg02LLm<0bTg02M1m<0=Tg01G\k70<Tg01O3k30_Tg01L@k80^Tg02MVm?0`Tg02Njk10aTg01P4R5g01Q>g01RGS00f7R6f6R7f5R8f4R9f3R:f2R;f1R<f0R=N;0cp=eg00EJR>&0><g00EjR?36&0;==6>?':p=C%o<=6>?/:=p=dA6>;?A6><?/:=':p=b%f==6>?p=u%\==6>?p=t%o==6>?p=s&0>==6>?p=q&0;==6>?p=m13;</3=p=ig01OVR@007=p=Rg02P9RAPAP@P@P0P3P3P:g02PXP;P<P=N<0bp>06PAP@P1P3P4g02Q<P8P9P:P;P<P=N<0=p=}g00NYR4/8=p=21_4=p=DP;g01SQR1g01T0R0P0g01TPRBP@P<g01V7P=H08g01UWRCK0<p=M20:@=p=?B0_@<=p=<P<P1P0P0PBP=PCK0<p>0ZP:P1P0P0PBP;P<P=L0^p=[A6>=?p>0U%@=#@p=Pg02Q^P=P<P;P:P9g02RkP8g02T8g02UDg02VQP7P6f8RCf9RDN?0`p=T%0=#0p=B%0=#0#0#0#0#0#0#0p=j%0=#4p=l%4=#4p=9%4=#0p=;%0=#0#0#0#0#0#0#0#0#0#0#5p=G%0=#0#0#0#0#0#0#5p=z%0=#4#0#4p=]g02WW&0a='np==A6A<=p=A18;</:=p=>%0=#0#0#0p>05A6@=4p=w1:<=,:;p>0F13;</8=p=EPAP@P=P3P<P;P:P9P8P7P6PCN<0=p>04g00N:R3#@RE#@RF,O=RGg02Xfg00O7RH#0RI#4RJ#N%0IRK#0RL#0RM#0RN#0RO#NRP$09RQ+0W%NL$09$0Q\Qg02Z7g01YFRRp,2spRSp,5rdrawRTp,4brk0RUp,4argvRVp,4envpRWp,3uidRXp,2hwRYL0ORZPRPSPTPVPWPXPYK0NRRp,2fsR[P:%18P;P<P=GePAPZPRP[P7%1<P8P9P:Ge%1;R\#f%\\1C\\,d\3b]1^2GP71O3FPZPRP[P8%13P9P:P;Geg01g?RG#u%tGR\%sGR]%qGR^%mGRG':R_':R`':g02ZmP\P`g02\AP]P_g02]]P^PGg02_8g02`OCKCKCKCKW1W2PA%@=RG/OFPZPRP[PC%@<R^#1P6P7P8Ge%@;R_#1R]#f%\]1C]],d]3b]1]2P=1OEFPZPRP[P6%1EP7P8P9Geg01hGR]#u%t]R`%s]R\%q]Ra%m]R]':Rb':Rc':g02akP`Pcg02c?P\Pbg02d[PaP]g02f6g02gMCKCKCKCKW1W2%@G/OFPZPRP[PD%@^#1PCP6P7Ge%@_R^/OF%7;RR%5HRZ;iZ%5IRG'_R]P^13=ZXP@R^P^PRO1RaO1P^P_PaP^P;PR%RRH06H06PFPG%RGS01E}P<ChP]%g:%7:#2%4KRK#0R]#4#5RR,IGS02%DGR^%2R1JGRRa#D[[S03%2GR_g01\RRbAHGR<UW0S04%2a\b^0_S05%4KRK#4RR#5R\,IGS06%2\1JG\Rc#D[\^S07AHG\<VbX0_S08%2c\b^0_S09%4LRL#4R\#5R`,IGS0:%2`1JG`Rd#D[\^S0;AHG`<VbX0_R`%2d\b^0_Re%0JRf#0Rg#5Rh,IGRi%2h1JGhRj#D[\^RkAHGh<VbX0_Rh%2j\b^0_Rjp-0Rlg01V^Rm$00Rn&0@mS0<P@&0d@S0=P<1|@<C~&0]@S0>&0\@Ro20:@4%4HRp,{@Rq5Mo&0[0RrPoP@%?ZRs,<q/<sg01U0%?GRsH08-0ZoPrPoP1P0P0PBP:J0YC[C[20XoBS0?P=P;207>?20V=;$0UdB0T@4<H0SS0@b8b9b:X3@W=%2=Ai<ZZ/_GP:[[^3@^=lP=f=Rl#P#1RZ#f%\Z1CZZ,dZ3b%7lPDf:RZO4b7bdbebfbgblbmbnbob;b6W1W2XNAP=O1n0110000020011100XOAP=O1n0110000020011100P8P=O2%17R4#f%\41C44,d43bP2%16R4#u%\4%o41C443b%X:R4#U&0R5R5%W4%1CR4/Y7p,6BUDGETR?1Z74Pa1V47P9%S:M:TP=%1D#u%1ZRD#\%oD1CDD3bP2f;RD#1R4#t1C44,d4%X6R4#UP5%W4f<R4#1R7/YZP?1ZZ7Pa1V7ZPC%S6M:TP=%1l#tf>Rl#1R61C66'dP2f?R6#1RC#s1CCC%XDRC#UP5%WCf@RC#1R7/YlP?1Zl7Pa1V7lP4%SDM:TP=fARD#1#sfBR4#1R7/C7P2fCS0A#1R7#q%m7%X6R7#UP5%W7fDR7#1RZ/Y4P?1Z4ZPa1VZ4PC%S6M:TP=fERZ#1#qfFR4#1#mfGR>00P4%1>R4#`%4O#B#j#l#B#9#B#;#9#;#;#GRB%Q4%4pRp#9R0#4R1#0#B#j#zRt%F4%l]#]#;#;#;#;#9#GR]%=4%@FR4#P#P#P#P#P#P#PRu'A3>3>3>P2fHRv#1Rw#`/8B%Qw%Fw%=w/Au7>]7>t%X7Rw#UP5%WwfIRw#1Rx/Y>P?1Z>xPa1Vx>PZ%S7M:TP=fJ#1#`/8BfKR7#1RZ#Q%FZ%=Z/Au7>]7>tP2fLRZ#1Rx#Q/8t%Fx%=x/Au7>]%XvRx#UP5%WxfMRx#1R>/Y7P?1Z7>Pa1V>7Pw%SvM:TP=fNRw#1#Q/8tfOR>#1R7#F%=7/Au7>]P2fPR2#1R7#F/8]%=7/Au%XZR7#UP5%W7fQR7#1Ry/Y>P?1Z>yPa1Vy>Px%SZM:TP=fRRx#1#F/8]fSRy#1#=/AuPSPUPTPVPWPXPYP[fTRa#1RzPlPxP7P2P>PwN?0Mg00G^:0LxzRw&0Kz,cx%BO$05RO#0Rz#BRl#0R{#5R|'3R}'_13w|,8}':1x}|#w':PSPUPTPVPWPXPYP[fUR}#1RwP6PyPxP7P2P>N?0I&0Hw,cyR>&0Gw,cyRw%0{#B$05R{#5R6'356@%5ORO,xw#wg00SRR~,cy0036R613wO136O%4J#9#5RJ,JGR6,8>5>w3>40FPSPUPTPVPWPXPYP[p,3HspS0Bp,3HvaS0CfVS0D#1PCPaPyPxP7P2p,3Hvep,4HfitNC0E1ca~%5MRC;E6PSPUPTPVPWPXPYP[fWS0E#1PDP}PaPyPxP7N?0D1c}~/xC#wfXR~#1R7#=Rx/Au%7xRy%5LRD56@Rw&02AS0F&02@S0G%7<%7=56@1A<=20C<=40JXsAXPAS0HPxPy%RyPuPD%RDS0IN904P9ChPwfYRw/OF%7wRy/_GRxPwPy%RyPFPGQ01E}P~ChPxfZRx#g%7xRy#2f[R>#1#=RO#g%7O#2Q02Q03Q04Q05Q06Q07Q08Q091IGJS0J%2J%D6[\^S0KAHGJ<VbX0_S0L%26\b^0_S0MQ0:Q0;P`Pe%5NRN,IGS0N%2N1JGNR6#D[\^S0OAHGN<VbX0_S0P%26\b^0_S0Q%0LRL#5R6,IGS0R%261JG6RN#D[\^S0SAHG6<VbX0_S0T%2N\b^0_R6PiPkPhPj1v@41v@F1v@E1v@35y@5y@R35y@g01\nRE+01=^mnQ0<P@1|@;S0UP<1|@:C~Q0>Po1{@IRI%?]5MoPrPo1{@HRH%?t5MoPrPo%NR9k@s%N\9k@s60B@R\9MoqPr1<HIR4%NL9k@s'</<q%0{#j#zR{#?5MoC[C[C[Q0?Q0@b8b9b:X3@X5@XL@18<]18<t203cdRd,89Ai:9N?E8{[[[^3@^5@^L@P=P?fk#1R{#F%Q{PvPZp,6BUD_hiS0VO6b7b>b?b@bAbBbCbDbEbFbGbHbIbJbKbMb;b6b<%Q7%F7;iNQ007E?RNePNPAPug02hig01nTRN'3R7%1xS00#`/3?'3R{20AQQRc/n5Rt/p=#7g01mNR]'3%91#9#9R1#5Rq,3NRL'ag02j;RJ3EXOA&0@cROPQPQ1LP|%4M#B#G,LPCrPQPQ%4g#B#G,LP%Bp#;#;#G,LPCrPQPQ%0K#9#;#G,LP%5l,LPCrPQPQ%9R#;#G,LP%4fRf#lRR#4#;#;#G,LPCr&00c5^c5^c5^c5^cRP1nc=/pu#7/3]/aL=E{JXqO%1wRO#=R{/Au%7{RQ=6@DRlQ0FQ0GQ0HP{PQ%RQPuPDQ0IN904P8ChPl1OxF1_yGRlPxPy%RyPFPGQ01E}PwChPl%g>%7>#2f\#1#=R>#g%7>#2Q02Q03Q04Q05Q06Q07Q08Q09Q0JQ0KQ0LQ0MQ0:Q0;P`PeQ0NQ0OQ0PQ0QQ0RQ0SQ0TP6PiPkPhPj%50Rj,IG%2j1JGjRh#D[\^AHGj<VbX0_%2h\b^0_1IGC%2C1JGCRj#D[\^AHGC<VbX0_%2j\b^0_2013E=^mnQ0<P@Q0UP<Q0=C~Q0>Po%?B9MoHPrPoAMoI\Pr%lR#]#]#]#]#]#]#;#GRR#?%N09k@s%NM9k@s'<Rs'</<4%5fRf#?%5zRz#?'<%?q,<s60f@'<%91#;#9#9#9#9#j#j#zR1#?5MoC[C[Q0?Q0@b8b9b:X3@X5@18=B18;d13hjRj13;:5iR13fz13jq'a;E1[[^3@^5@P=P?fp#1#`P}Q0VO4b7b>b?b@bAbBbCbDbEbFbGbHbIbJbKbhbibjbkbMb;b6b<%`O/3?,37R713f]/aL;EJe1ncP/pu#7/3]/aL=E7JeP5g02kLJ0?P{P8J0?1pt{#7/3]/aL=E7JPSPUPTPVPWPXPYP[Q0BQ0CQ00P2PZPvP~Q0EQ0DP}PaP8P9P:P;P?PNg02lbP<p,6BUD_geP=Q0Ap,3FSHNO0eb\bQb[bZb^b]WbWaP<P=O2n2001000000121000000W4W`P<P=O2n2001000000121000000W4W_P<P=O2n2001000000121000000bpWWWSP<P=O2n2001000000121000000W4WVP<P=O2n2001000000121000000W4WUP<P=O2n2001000000121000000W4WRP<P=O2n2001000000121000000bTW1WrWYWcWXW2XNAo"). Qed.
End Inst.
