(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: recorded proofs replaced by tactic proofs; the string read-ahead slack of 9; addresses and numbers; taken in part from projects/jsoncons/fuzz_bigint/proofs/lib/As0DiagUsageC.v, lines 35, 83-193, 228-230. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.LeanFeed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare RefMemcpyLib L5Defs L5Kn L5KnA
     Ea0RegionPoisoned Ea0AsanMemcpy Ea0DiagKit Ea0DiagChk Ea0DiagMemcpy Ea0DiagStrnlen Ea0DiagGlue Ea0DiagUP Ea0DiagUsagePre.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_Ea0DiagUsageC () := "C46Stdlib5Lists4List:firstn_nilC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions7Z_to_bvK47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive01K47Corelib4Init9Datatypes4list01C47Corelib5Lists7ListDef3mapI47Corelib4Init9Datatypes4list00K47Corelib4Init5Logic2eq01C45stdpp9bitvector;definitions;bv_unsignedI47Corelib4Init5Logic2eq00C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Ea0DiagGlue2DG:list_bv_eqC13~~~K47Corelib4Init9Datatypes4list02I47Corelib7Numbers7BinNums1Z00C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Ea0DiagGlue2DG4SUF7C13~~~K47Corelib7Numbers7BinNums8positive03C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes6option00C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Ea0DiagUsagePre3DUP9usage_midC13~~~C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7seg_romC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec4mkstC13~~~K47Corelib4Init9Datatypes3nat02C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec4getrC13~~~C56Stdlib6ZArith6BinInt1Z3subC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addK47Corelib4Init9Datatypes6option01C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Ea0DiagGlue2DG6agree0C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7StoreOk9mem_growsC13~~~C46Stdlib5Lists4List2InC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic2ex00C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Ea0DiagGlue2DG:diag_cellsC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Defs2L56u32_atC13~~~C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega=RingMicromega5Psatz02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega7EnvRing5PExpr01C56Stdlib6ZArith6BinInt1Z3divK46Stdlib9micromega6VarMap1t01C56Stdlib6ZArith6BinInt1Z7div_posK46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1ZBdiv_le_upper_boundK47Corelib4Init5Logic3and01C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Ea0DiagGlue2DG5filewC13~~~C47Corelib4Init5Logic3notC89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:Ea0DiagKit2DK1UC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:Ea0DiagKit2DK>writable_growsC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:Ea0DiagKit2DK=defined_growsC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Defs2L57definedC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:Ea0DiagKit2DK8imgc_extC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Defs2L59img_clearC13~~~C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega:ZMicromega;ZArithProof03C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4asan9Ea0DiagUP9AS0DIAGUP7alignedC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Defs2L5;defined_subC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4asan9Ea0DiagUP9AS0DIAGUP9duDl_concC13~~~I46Stdlib;setoid_ring<Ring_polynom5PExpr00I47Corelib4Init9Datatypes4prod00I46Stdlib;setoid_ring<Ring_polynom3Pol00C46Stdlib;setoid_ring:ZArithRing>Zr_ring_lemma2C46Stdlib;setoid_ring;Ring_theory5IDphiK46Stdlib;setoid_ring<Ring_polynom5PExpr04C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7StoreOk?mem_grows_transC13~~~C56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z7eqb_neqC89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:Ea0DiagKit2DK7u64_extC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:Ea0DiagKit2DK7u32_extC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Ea0DiagGlue2DG>wv_entry_stageC13~~~I47Corelib4Init5Logic2or00C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:Ea0DiagKit2DK6u8_extC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Ea0DiagGlue2DG5rdn_7C13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>Ea0DiagStrnlen3DSN8cstr_extC13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>Ea0DiagStrnlen3DSN4cstr00C13~~~C47Corelib4Init3Nat3addC47Corelib4Init9Datatypes3appC47Corelib4Init5Peano2ltC47Corelib5Lists7ListDef3nthC47Corelib5Lists7ListDef6firstnC47Corelib4Init3Nat3subC46Stdlib5Lists4List9app_nil_rC56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib5Arith8PeanoNat3Nat8sub_diagI47Corelib4Init5Peano2le00C46Stdlib5Lists4List;firstn_all2C46Stdlib5Lists4List:firstn_appC35stdpp7tactics<f_equal_helpC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SeqExec:rdn_firstnC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6CatSim<msteps_transC13~~~C47Corelib4Init5Logic7and_indK47Corelib4Init5Logic2or01C47Corelib4Init5Logic9False_indC89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:Ea0DiagKit2DK9zeros_extC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib5L5KnA4L5KA8zeros_atC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Ea0DiagGlue2DG;u8_of_u32_5C13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib5L5KnA4L5KA<zeros_at_subC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:Ea0DiagKit2DK<u64_of_zerosC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:Ea0DiagKit2DK2URC13~~~C56Stdlib5Arith8PeanoNat3Nat3eqbC89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4L5Kn3L5K4in_bC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:Ea0DiagKit2DK4U_toC13~~~K46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z3oppC46Stdlib6ZArith4Zdiv?Z_div_plus_fullC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4asan9Ea0DiagUP9AS0DIAGUP9duEc_concC13~~~C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:Ea0DiagKit2DK8rdn_consC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4asan9Ea0DiagUP9AS0DIAGUP9duGc_concC13~~~C47Corelib4Init5Logic6eq_symC46Stdlib5Lists4List7existsbK47Corelib4Init5Logic2ex01C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Defs2L56u64_atC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec3rdnC13~~~I79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6CatSim6msteps00C13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Defs2L55u8_atC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Defs2L58writableC13~~~K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega5Tauto8GFormula06C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Defs2L5<writable_subC13~~~C47Corelib4Init5Logic6eq_indC46Stdlib;setoid_ring<Ring_polynom>mk_monpol_listC46Stdlib;setoid_ring<Ring_polynom:norm_substC46Stdlib;setoid_ring<Ring_polynom8Pphi_powC46Stdlib;setoid_ring<Ring_polynom6PEevalK46Stdlib;setoid_ring<Ring_polynom3Pol01K46Stdlib;setoid_ring<Ring_polynom3Pol03K46Stdlib;setoid_ring<Ring_polynom5PExpr03K46Stdlib;setoid_ring<Ring_polynom5PExpr06K46Stdlib;setoid_ring<Ring_polynom5PExpr05C46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib9micromega;ZifyClasses6mkapp2K47Corelib4Init5Logic2or02C47Corelib4Init5Logic6or_indC46Stdlib9micromega;ZifyClasses5mkappK47Corelib7Numbers7BinNums1Z01C79OSSVerify8jsonconsCfuzz_ubjson_encoder6images4Asan1M?loaded_segmentsC13~~~I47Corelib4Init9Datatypes3nat00I79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7FPState00C13~~~K46Stdlib9micromega:ZMicromega;ZArithProof01I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op201C56Stdlib6ZArith6BinInt1Z7quotremC46Stdlib;setoid_ring8Ring_tac@ring_subst_niterC56Stdlib6ZArith6BinInt1Z4of_NC46Stdlib;setoid_ring;InitialRing9get_signZK47Corelib4Init9Datatypes4bool02C56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addI47Corelib4Init5Logic5False00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4asan9Ea0DiagUP9AS0DIAGUP7KS_duDlC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4asan9Ea0DiagUP9AS0DIAGUP7KS_duEcC13~~~K47Corelib4Init9Datatypes3nat01C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Ea0DiagGlue2DG4PRE7C13~~~I47Corelib4Init5Logic4True00I46Stdlib;setoid_ring<Ring_polynom3Mon00K47Corelib4Init5Logic4True01C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Ea0DiagGlue2DG7PRE7_eqC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3libAEa0RegionPoisoned2SBC13~~~C46Stdlib9micromega8ZifyInst7Inj_Z_Zc89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=Ea0DiagUsageC3DUC8SUF7_eqJC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4asan9Ea0DiagUP9AS0DIAGUP7KS_duGcC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Ea0DiagUsagePre3DUP9usage_preC13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=Ea0DiagUsageC3DUC<usage_C_tailC13~~~". Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module DUC.
Import DK. Import DSN. Import DG. Import AS0DIAGUP.

Lemma SUF7_eqJ : SUF7 = map (Z_to_bv 8) [32; 73; 78; 80; 85; 84; 10].
Proof. apply list_bv_eq. vm_compute. reflexivity. Qed.

Section UA.
  Context (fx : FPState).
  Variables (R : bvmap 5 word) (M : word -> option byte) (S p can : Z) (bs t8 : list byte).
  #[local] Notation n := (Z.of_nat (length bs)).
  Hypothesis G1 : getr R (reg 1) = Z_to_bv 64 689724.        (* [comment removed for export] *)
  Hypothesis G2 : getr R (reg 2) = Z_to_bv 64 S.
  Hypothesis G10 : getr R (reg 10) = Z_to_bv 64 1300928.      (* [comment removed for export] *)
  Hypothesis G11 : getr R (reg 11) = Z_to_bv 64 90792.       (* [comment removed for export] *)
  Hypothesis G12 : getr R (reg 12) = Z_to_bv 64 p.           (* [comment removed for export] *)
  Hypothesis HS : 140735332552704 + 5440 <= S <= 140737488355328.
  Hypothesis Hal : S mod 16 = 0.
  Hypothesis HW : L5.writable RSEGS M (S - 5440) 5440.
  Hypothesis HD : L5.defined M (S - 5440) 5440.
  Hypothesis HIMG : L5.img_clear M 65536 1286144.
  Hypothesis Hp : S <= p /\ p + n + 1 + 9 <= 2 ^ 47.
  Hypothesis Hn : 74 <= n <= 131071.
  Hypothesis HSTR : cstr M p bs t8.
  Hypothesis HSH : forall x : word, SB + p / 8 - 7 <= bv_unsigned x < Z.min (SB + (p + n) / 8 + 8) (SB + 2 ^ 44) -> M x = Some (Z_to_bv 8 0).
  Hypothesis HSTK : L5KA.zeros_at M (SB + S / 8 - 680) 688.     (* [comment removed for export] *)
  Hypothesis HFMT : L5KA.zeros_at M 2147462224 16.              (* [comment removed for export] *)
  Hypothesis Hcan : 0 <= can < 2 ^ 64.
  Hypothesis HC : diag_cells M can.
  Hypothesis HSN : sn_cells M.
  Hypothesis HMC : mc_icpt_globs M.
  (* [comment removed for export] *)
  Variables m1 m2 m3 m4 m5 m6 m7 m8 : Z.
  Hypothesis Hm : (0 <= m1 < 2 ^ 64 /\ 0 <= m2 < 2 ^ 64 /\ 0 <= m3 < 2 ^ 64 /\ 0 <= m4 < 2 ^ 64) /\ (0 <= m5 < 2 ^ 64 /\ 0 <= m6 < 2 ^ 64 /\ 0 <= m7 < 2 ^ 64 /\ 0 <= m8 < 2 ^ 64).
  Hypothesis HMF : L5.u64_at RSEGS M (S + 72) 1154100 /\ L5.u64_at RSEGS M (S + 64) m1 /\ L5.u64_at RSEGS M (S + 56) m2 /\ L5.u64_at RSEGS M (S + 48) m3 /\ L5.u64_at RSEGS M (S + 40) m4
                   /\ L5.u64_at RSEGS M (S + 32) m5 /\ L5.u64_at RSEGS M (S + 24) m6 /\ L5.u64_at RSEGS M (S + 16) m7 /\ L5.u64_at RSEGS M (S + 8) m8.

  Theorem usage_C_tail : forall fx5 R5 M5, DUP.usage_mid R M S p can bs m1 m2 m3 m4 m5 m6 m7 m8 R5 M5 ->
    exists fxE RE ME,
      msteps RSEGS (st fx5 R5 0x1239b4 M5) (st fxE RE 0x121de0 ME)
      (* [comment removed for export] *)
      /\ getr RE (reg 17) = Z_to_bv 64 66 /\ getr RE (reg 10) = Z_to_bv 64 2 /\ getr RE (reg 11) = Z_to_bv 64 (S - 1128) /\ getr RE (reg 12) = Z_to_bv 64 2
      /\ getr RE (reg 9) = Z_to_bv 64 1300928 /\ getr RE (reg 18) = Z_to_bv 64 2 /\ getr RE (reg 19) = Z_to_bv 64 (S - 1128) /\ getr RE (reg 22) = Z_to_bv 64 (n + 7)
      /\ L5.u64_at RSEGS ME (S - 1128) (S - 464) /\ L5.u64_at RSEGS ME (S - 1120) 7 /\ L5.u64_at RSEGS ME (S - 1112) p /\ L5.u64_at RSEGS ME (S - 1104) n
      /\ rdn RSEGS ME (Z_to_bv 64 (S - 464)) 7 = Some PRE7 /\ rdn RSEGS ME (Z_to_bv 64 p) (length bs) = Some bs
      /\ L5.u32_at RSEGS ME 1301048 2
      /\ agree0 M ME S /\ mem_grows M ME
      /\ (forall fx' RX MX,
            (forall x : word, ~ (S - 1128 <= bv_unsigned x < S - 1096) -> MX x = ME x) -> mem_grows ME MX ->
            (forall k, In k [2; 3; 4; 8; 9; 21; 23; 24; 25; 26; 27]%nat -> getr RX (reg k) = getr RE (reg k)) ->
            exists fxE2 RE2 ME2,
              msteps RSEGS (st fx' RX 0x121dec MX) (st fxE2 RE2 0x121de0 ME2)
              (* [comment removed for export] *)
              /\ getr RE2 (reg 17) = Z_to_bv 64 66 /\ getr RE2 (reg 10) = Z_to_bv 64 2 /\ getr RE2 (reg 11) = Z_to_bv 64 (S - 584) /\ getr RE2 (reg 12) = Z_to_bv 64 2
              /\ getr RE2 (reg 9) = Z_to_bv 64 1300928 /\ getr RE2 (reg 18) = Z_to_bv 64 2 /\ getr RE2 (reg 19) = Z_to_bv 64 (S - 584) /\ getr RE2 (reg 22) = Z_to_bv 64 7
              /\ L5.u64_at RSEGS ME2 (S - 584) (S - 464) /\ L5.u64_at RSEGS ME2 (S - 576) 7 /\ L5.u64_at RSEGS ME2 (S - 568) 0 /\ L5.u64_at RSEGS ME2 (S - 560) 0
              /\ rdn RSEGS ME2 (Z_to_bv 64 (S - 464)) 7 = Some SUF7
              /\ L5.u32_at RSEGS ME2 1301048 2
              /\ agree0 M ME2 S /\ mem_grows M ME2
              /\ (forall fx'' RY MY,
                    (forall x : word, ~ (S - 584 <= bv_unsigned x < S - 552) -> MY x = ME2 x) -> mem_grows ME2 MY ->
                    (forall k, In k [2; 3; 4; 8; 9; 21; 23; 24; 25; 26; 27]%nat -> getr RY (reg k) = getr RE2 (reg k)) ->
                    exists fxF RF MF,
                      msteps RSEGS (st fx'' RY 0x121dec MY) (st fxF RF 0x11a3fc MF)
                      /\ getr RF (reg 10) = getr R (reg 8) /\ getr RF (reg 2) = Z_to_bv 64 (S + 80)
                      /\ agree0 M MF S /\ mem_grows M MF
                      /\ L5.u32_at RSEGS MF 1300928 5 /\ L5.u64_at RSEGS MF 1301024 0 /\ L5.u64_at RSEGS MF 1301016 6906520
                      /\ L5.u64_at RSEGS MF 1300984 0 /\ L5.u64_at RSEGS MF 1300968 0 /\ L5.u64_at RSEGS MF 1300960 0 /\ L5.u64_at RSEGS MF 1300936 0 /\ L5.u64_at RSEGS MF 1300944 0 /\ getr RF (reg 4) = getr R (reg 4))).
Proof.
    intros fx5 R5 M5 INV.
    destruct Hm as ((Hm1 & Hm2 & Hm3 & Hm4) & (Hm5 & Hm6 & Hm7 & Hm8)).
    pose proof HC as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & FW).
    assert (Pr : 140735332552704 <= p <= 140737488355318) by lia.
    assert (Nr : 0 <= n <= 131071) by lia.
    assert (DIV : 0 <= (p + n) / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
    assert (S8 : 0 <= S / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
    destruct INV as (A05 & MG05 & T). dk_split T.

    assert (W5 : L5.writable RSEGS M5 (S - 5440) 5440) by (eapply writable_grows; [exact MG05 | exact HW]).
    assert (D5 : L5.defined M5 (S - 5440) 5440) by (eapply defined_grows; [exact MG05 | exact HD]).
    assert (IMG5 : L5.img_clear M5 65536 1286144) by (apply (imgc_ext M M5); [intros x Hx; apply A05; flia | lia | lia | exact HIMG]).
    pose proof (duDl_conc fx5 R5 M5 (fun j => match j with 2%nat => S - 1024 | 33%nat => p | 34%nat => n | 40%nat => can | _ => 0 end)) as P. cbn beta iota in P.
    dk_feed P ltac:(first [apply UR | apply U_to | scc | shz]).
    dk_open P as fx8 R8 M8 MG8 FR8 FZ8 MS8 KS8.

    assert (AG58 : forall x : word, bv_unsigned x < S - 1136 \/ S - 1024 <= bv_unsigned x -> M8 x = M5 x) by (intros x Hx; apply FR8; lia).
    assert (A08 : forall x : word, ~ (S - 5440 <= bv_unsigned x < S) -> ~ filew (bv_unsigned x) -> M8 x = M x) by (intros x Hx Hf; rewrite AG58 by lia; apply A05; assumption).
    assert (MG08 : mem_grows M M8) by (eapply mem_grows_trans; eassumption).
    assert (W8 : L5.writable RSEGS M8 (S - 5440) 5440) by (eapply writable_grows; eassumption).
    assert (NE : Z.eqb (S - 457) (S - 464) = false) by (apply Z.eqb_neq; lia).
    destruct (wv_entry_stage fx8 R8 M8 1300928 (S - 1136) p n (S - 457) (S - 464) 2) as (RW & MW & MSW & W17 & W10 & W11 & W12 & W18 & W19 & W22 & KSW & I0 & I1 & I2 & I3 & AG8W & MGW);
      [ sc | sc | sc | sc | lia | lia | lia | lia | lia | lia | lia | lia | lia | lia | scc | scc | scc | dk_gmem | ].
    rewrite NE in W11, W12, W18, W19.
    assert (A0W : forall x : word, ~ (S - 5440 <= bv_unsigned x < S) -> ~ filew (bv_unsigned x) -> MW x = M x) by (intros x Hx Hf; rewrite AG8W by lia; apply A08; assumption).
    assert (MG0W : mem_grows M MW) by (eapply mem_grows_trans; eassumption).
    assert (AG5W : forall x : word, S - 1024 <= bv_unsigned x -> MW x = M5 x) by (intros x Hx; rewrite AG8W by lia; apply AG58; lia).
    assert (P7W : rdn RSEGS MW (Z_to_bv 64 (S - 464)) 7 = Some PRE7).
    { rewrite PRE7_eq. apply rdn_7; [lia | lia | ..];
        (eapply (u8_ext M5); [intros x Hx; apply AG5W; lia | lia | lia |]); match goal with |- L5.u8_at _ _ ?a _ => ring_simplify a end; assumption. }
    assert (STRW : cstr MW p bs t8) by (apply (cstr_ext M MW); [lia | lia | intros x Hx; apply A0W; flia | exact HSTR]).
    assert (RDSW : rdn RSEGS MW (Z_to_bv 64 p) (length bs) = Some bs).
    { destruct STRW as [A _ _]. rewrite (SeqExec.rdn_firstn RSEGS MW _ _ _ (length bs) A) by lia. f_equal. rewrite firstn_app, firstn_all2 by lia. rewrite Nat.sub_diag. cbn [firstn]. apply app_nil_r. }
    exists fx8, RW, MW.
    split. { eapply msteps_trans; [exact MS8|]. exact MSW. }
    split; [exact W17|]. split; [exact W10|]. split; [rewrite W11; f_equal; lia|]. split; [exact W12|].
    split; [rewrite (KSW 9%nat) by (cbn; tauto); sc|]. split; [exact W18|]. split; [rewrite W19; f_equal; lia|]. split; [rewrite W22; f_equal; lia|].
    split; [replace (S - 1128) with (S - 1136 + 8) by lia; exact I0|]. split; [replace (S - 457 - (S - 464)) with 7 in I1 by lia; replace (S - 1120) with (S - 1136 + 16) by lia; exact I1|].
    split; [replace (S - 1112) with (S - 1136 + 24) by lia; exact I2|]. split; [replace (S - 1104) with (S - 1136 + 32) by lia; exact I3|].
    split; [exact P7W|]. split; [exact RDSW|]. split; [scc|]. split; [exact A0W|]. split; [exact MG0W|].

    intros fx' RX MX AGXW MGXW KXW.
    assert (AGX8 : forall x : word, ~ (S - 1128 <= bv_unsigned x < S - 1096) -> MX x = M8 x) by (intros x Hx; rewrite AGXW by exact Hx; apply AG8W; lia).
    assert (KX : forall k, In k [2; 3; 4; 8; 9; 21; 23; 24; 25; 26; 27]%nat -> getr RX (reg k) = getr R8 (reg k)) by (intros k Hk; rewrite (KXW k Hk); apply KSW; cbn in Hk |- *; tauto).
    assert (AGX5 : forall x : word, S - 1024 <= bv_unsigned x -> MX x = M5 x) by (intros x Hx; rewrite AGX8 by lia; apply AG58; lia).
    assert (AGX5s : forall x : word, bv_unsigned x < 2 ^ 32 -> MX x = M5 x) by (intros x Hx; rewrite AGX8 by lia; apply AG58; lia).
    assert (AGX0 : forall x : word, ~ (S - 5440 <= bv_unsigned x < S) -> ~ filew (bv_unsigned x) -> MX x = M x) by (intros x Hx Hf; rewrite AGXW by lia; apply A0W; assumption).
    assert (MG0X : mem_grows M MX) by (eapply mem_grows_trans; eassumption).
    assert (WX : L5.writable RSEGS MX (S - 5440) 5440) by (eapply writable_grows; eassumption).
    assert (DX : L5.defined MX (S - 5440) 5440) by (eapply defined_grows; eassumption).
    assert (IMGX : L5.img_clear MX 65536 1286144) by (apply (imgc_ext M MX); [intros x Hx; apply AGX0; flia | lia | lia | exact HIMG]).
    assert (FWX : L5.writable RSEGS MX 1300928 152) by (eapply writable_grows; eassumption).
    assert (SKX : L5KA.zeros_at MX (SB + S / 8 - 680) 688).
    { apply (zeros_ext M MX); [intros x Hx; apply AGX0; unfold SB in Hx; flia | unfold SB; lia | unfold SB; lia | exact HSTK]. }
    assert (F8X : L5.u8_at RSEGS MX 1300928 5) by (apply u8_of_u32_5; [lia | lia|]; scc).
    assert (FMTX : L5KA.zeros_at MX 2147462224 16) by (apply (zeros_ext M MX); [intros x Hx; apply AGX0; unfold SB in Hx; flia | unfold SB; lia | unfold SB; lia | exact HFMT]).
    pose proof (u64_of_zeros MX 2147462224 (L5KA.zeros_at_sub MX 2147462224 16 2147462224 8 FMTX ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)) as FMT64X1.
    pose proof (u64_of_zeros MX 2147462232 (L5KA.zeros_at_sub MX 2147462224 16 2147462232 8 FMTX ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)) as FMT64X2.
    pose proof (duEc_conc fx' RX MX (fun j => match j with 2%nat => S - 1136 | 33%nat => p | 34%nat => n | 40%nat => can
       | 22%nat => U R 22 | 23%nat => U R 23 | 24%nat => U R 24 | 25%nat => U R 25 | 26%nat => U R 26 | 27%nat => U R 27
       | 122%nat => U RX 22 | 123%nat => U RX 23 | 125%nat => U RX 25 | 127%nat => U RX 27 | _ => 0 end)) as P. cbn beta iota in P.
    dk_feed P ltac:(first [apply UR | apply U_to | scc | shz]).
    dk_open P as fx9 R9 M9 MG9 FR9 FZ9 MS9 KS9.

    assert (AGX9 : forall x : word, bv_unsigned x < S - 3248 \/ S - 448 <= bv_unsigned x -> ~ (1300960 <= bv_unsigned x < 1300976) -> ~ (1300984 <= bv_unsigned x < 1300992) -> M9 x = MX x) by (intros x Hx Hf1 Hf2; apply FR9; lia).
    assert (A09 : forall x : word, ~ (S - 5440 <= bv_unsigned x < S) -> ~ filew (bv_unsigned x) -> M9 x = M x) by (intros x Hx Hf; rewrite AGX9 by (unfold filew in Hf; lia); apply AGX0; assumption).
    assert (MG09 : mem_grows M M9) by (eapply mem_grows_trans; eassumption).
    assert (W9 : L5.writable RSEGS M9 (S - 5440) 5440) by (eapply writable_grows; eassumption).
    assert (AG59s : forall x : word, bv_unsigned x < 2 ^ 32 -> ~ (1300960 <= bv_unsigned x < 1300976) -> ~ (1300984 <= bv_unsigned x < 1300992) -> M9 x = M5 x) by (intros x Hx Hf1 Hf2; rewrite AGX9 by lia; apply AGX5s; lia).
    assert (NE2 : Z.eqb (S - 457) (S - 464) = false) by (apply Z.eqb_neq; lia).
    destruct (wv_entry_stage fx9 R9 M9 1300928 (S - 592) 0 0 (S - 457) (S - 464) 2) as (RW2 & MW2 & MSW2 & X17 & X10 & X11 & X12 & X18 & X19 & X22 & KSW2 & J0 & J1 & J2 & J3 & AG9W & MGW2);
      [ sc | sc | sc | sc | lia | lia | lia | lia | lia | lia | lia | lia | lia | lia | scc | scc | scc | dk_gmem | ].
    rewrite NE2 in X11, X12, X18, X19.
    assert (A0W2 : forall x : word, ~ (S - 5440 <= bv_unsigned x < S) -> ~ filew (bv_unsigned x) -> MW2 x = M x) by (intros x Hx Hf; rewrite AG9W by lia; apply A09; assumption).
    assert (MG0W2 : mem_grows M MW2) by (eapply mem_grows_trans; eassumption).
    assert (SUFW : rdn RSEGS MW2 (Z_to_bv 64 (S - 464)) 7 = Some SUF7).
    {
      rewrite SUF7_eqJ. cbn [map].
      repeat (apply rdn_cons; [lia | cbn; lia | (change (rdn RSEGS MW2 (Z_to_bv 64 ?a) 1 = Some [Z_to_bv 8 ?v]) with (L5.u8_at RSEGS MW2 a v);
                eapply (u8_ext M9); [intros x Hx; apply AG9W; lia | lia | lia | match goal with |- _ _ _ ?a _ => ring_simplify a end; assumption]) | ]);
      reflexivity. }
    exists fx9, RW2, MW2.
    split. { eapply msteps_trans; [exact MS9|]. exact MSW2. }
    split; [exact X17|]. split; [exact X10|]. split; [rewrite X11; f_equal; lia|]. split; [exact X12|].
    split; [rewrite (KSW2 9%nat) by (cbn; tauto); sc|]. split; [exact X18|]. split; [rewrite X19; f_equal; lia|]. split; [rewrite X22; f_equal; lia|].
    split; [replace (S - 584) with (S - 592 + 8) by lia; exact J0|]. split; [replace (S - 457 - (S - 464)) with 7 in J1 by lia; replace (S - 576) with (S - 592 + 16) by lia; exact J1|].
    split; [replace (S - 568) with (S - 592 + 24) by lia; exact J2|]. split; [replace (S - 560) with (S - 592 + 32) by lia; exact J3|].
    split; [exact SUFW|]. split; [scc|]. split; [exact A0W2|]. split; [exact MG0W2|].

    intros fx'' RY MY AGYW MGYW KYW.
    assert (AGY9 : forall x : word, ~ (S - 584 <= bv_unsigned x < S - 552) -> MY x = M9 x) by (intros x Hx; rewrite AGYW by exact Hx; apply AG9W; lia).
    assert (KY : forall k, In k [2; 3; 4; 8; 9; 21; 23; 24; 25; 26; 27]%nat -> getr RY (reg k) = getr R9 (reg k)) by (intros k Hk; rewrite (KYW k Hk); apply KSW2; cbn in Hk |- *; tauto).
    assert (AGYX : forall x : word, S - 448 <= bv_unsigned x -> MY x = MX x) by (intros x Hx; rewrite AGY9 by lia; apply AGX9; lia).
    assert (AGY5 : forall x : word, S - 448 <= bv_unsigned x -> MY x = M5 x) by (intros x Hx; rewrite AGYX by lia; apply AGX5; lia).
    assert (AGY5s : forall x : word, bv_unsigned x < 2 ^ 32 -> ~ (1300960 <= bv_unsigned x < 1300976) -> ~ (1300984 <= bv_unsigned x < 1300992) -> MY x = M5 x) by (intros x Hx Hf1 Hf2; rewrite AGY9 by lia; apply AG59s; assumption).
    assert (AGY0 : forall x : word, ~ (S - 5440 <= bv_unsigned x < S) -> ~ filew (bv_unsigned x) -> MY x = M x) by (intros x Hx Hf; rewrite AGYW by lia; apply A0W2; assumption).
    assert (MG0Y : mem_grows M MY) by (eapply mem_grows_trans; eassumption).
    assert (WY : L5.writable RSEGS MY (S - 5440) 5440) by (eapply writable_grows; eassumption).
    assert (DY : L5.defined MY (S - 5440) 5440) by (eapply defined_grows; eassumption).
    assert (IMGY : L5.img_clear MY 65536 1286144) by (apply (imgc_ext M MY); [intros x Hx; apply AGY0; flia | lia | lia | exact HIMG]).
    assert (FWY : L5.writable RSEGS MY 1300928 152) by (eapply writable_grows; eassumption).
    pose proof (duGc_conc fx'' RY MY (fun j => match j with 2%nat => S - 592 | 33%nat => p | 34%nat => n | 40%nat => can
       | 8%nat => U R 8 | 9%nat => U R 9 | 18%nat => U R 18 | 19%nat => U R 19 | 20%nat => U R 20 | 21%nat => U R 21 | 22%nat => U R 22
       | 41%nat => m1 | 42%nat => m2 | 43%nat => m3 | 44%nat => m4 | 45%nat => m5 | 46%nat => m6 | 47%nat => m7 | 48%nat => m8
       | 118%nat => U RY 18 | 119%nat => U RY 19 | 120%nat => U RY 20 | 122%nat => U RY 22 | _ => 0 end)) as P. cbn beta iota in P.
    dk_feed P ltac:(first [apply UR | apply U_to | scc | shz]).
    dk_open P as fxF RF MF MGF FRF FZF MSF KSF.
    exists fxF, RF, MF.
    split; [exact MSF|].
    split. { match goal with H : getr RF (reg 10) = Z_to_bv 64 (U R 8) |- _ => rewrite H end. symmetry. apply U_to. }
    split; [sc|].
    split. { intros x Hx Hf. unfold filew in Hf. rewrite FRF by lia. apply AGY0; [exact Hx | unfold filew; lia]. }
    split; [eapply mem_grows_trans; [exact MG0Y | exact MGF]|].
    repeat split; first [sc | (eapply (DK.u64_ext M5); [intros x Hx; rewrite FRF by lia; apply AGY5s; lia | lia | lia | eassumption]) | dk_rk].
  Qed.

  Theorem usage_C :
    exists fxE RE ME,
      msteps RSEGS (st fx R 0x63d40 M) (st fxE RE 0x121de0 ME)
      (* [comment removed for export] *)
      /\ getr RE (reg 17) = Z_to_bv 64 66 /\ getr RE (reg 10) = Z_to_bv 64 2 /\ getr RE (reg 11) = Z_to_bv 64 (S - 1128) /\ getr RE (reg 12) = Z_to_bv 64 2
      /\ getr RE (reg 9) = Z_to_bv 64 1300928 /\ getr RE (reg 18) = Z_to_bv 64 2 /\ getr RE (reg 19) = Z_to_bv 64 (S - 1128) /\ getr RE (reg 22) = Z_to_bv 64 (n + 7)
      /\ L5.u64_at RSEGS ME (S - 1128) (S - 464) /\ L5.u64_at RSEGS ME (S - 1120) 7 /\ L5.u64_at RSEGS ME (S - 1112) p /\ L5.u64_at RSEGS ME (S - 1104) n
      /\ rdn RSEGS ME (Z_to_bv 64 (S - 464)) 7 = Some PRE7 /\ rdn RSEGS ME (Z_to_bv 64 p) (length bs) = Some bs
      /\ L5.u32_at RSEGS ME 1301048 2
      /\ agree0 M ME S /\ mem_grows M ME
      /\ (forall fx' RX MX,
            (forall x : word, ~ (S - 1128 <= bv_unsigned x < S - 1096) -> MX x = ME x) -> mem_grows ME MX ->
            (forall k, In k [2; 3; 4; 8; 9; 21; 23; 24; 25; 26; 27]%nat -> getr RX (reg k) = getr RE (reg k)) ->
            exists fxE2 RE2 ME2,
              msteps RSEGS (st fx' RX 0x121dec MX) (st fxE2 RE2 0x121de0 ME2)
              (* [comment removed for export] *)
              /\ getr RE2 (reg 17) = Z_to_bv 64 66 /\ getr RE2 (reg 10) = Z_to_bv 64 2 /\ getr RE2 (reg 11) = Z_to_bv 64 (S - 584) /\ getr RE2 (reg 12) = Z_to_bv 64 2
              /\ getr RE2 (reg 9) = Z_to_bv 64 1300928 /\ getr RE2 (reg 18) = Z_to_bv 64 2 /\ getr RE2 (reg 19) = Z_to_bv 64 (S - 584) /\ getr RE2 (reg 22) = Z_to_bv 64 7
              /\ L5.u64_at RSEGS ME2 (S - 584) (S - 464) /\ L5.u64_at RSEGS ME2 (S - 576) 7 /\ L5.u64_at RSEGS ME2 (S - 568) 0 /\ L5.u64_at RSEGS ME2 (S - 560) 0
              /\ rdn RSEGS ME2 (Z_to_bv 64 (S - 464)) 7 = Some SUF7
              /\ L5.u32_at RSEGS ME2 1301048 2
              /\ agree0 M ME2 S /\ mem_grows M ME2
              /\ (forall fx'' RY MY,
                    (forall x : word, ~ (S - 584 <= bv_unsigned x < S - 552) -> MY x = ME2 x) -> mem_grows ME2 MY ->
                    (forall k, In k [2; 3; 4; 8; 9; 21; 23; 24; 25; 26; 27]%nat -> getr RY (reg k) = getr RE2 (reg k)) ->
                    exists fxF RF MF,
                      msteps RSEGS (st fx'' RY 0x121dec MY) (st fxF RF 0x11a3fc MF)
                      /\ getr RF (reg 10) = getr R (reg 8) /\ getr RF (reg 2) = Z_to_bv 64 (S + 80)
                      /\ agree0 M MF S /\ mem_grows M MF
                      /\ L5.u32_at RSEGS MF 1300928 5 /\ L5.u64_at RSEGS MF 1301024 0 /\ L5.u64_at RSEGS MF 1301016 6906520
                      /\ L5.u64_at RSEGS MF 1300984 0 /\ L5.u64_at RSEGS MF 1300968 0 /\ L5.u64_at RSEGS MF 1300960 0 /\ L5.u64_at RSEGS MF 1300936 0 /\ L5.u64_at RSEGS MF 1300944 0 /\ getr RF (reg 4) = getr R (reg 4))).
Proof.
    destruct (DUP.usage_pre fx R M S p can bs t8 G1 G2 G10 G11 G12 HS Hal HW HD HIMG Hp ltac:(lia) HSTR HSH HSTK HFMT Hcan HC HSN m1 m2 m3 m4 m5 m6 m7 m8 Hm HMF) as (fx5 & R5 & M5 & MS5 & INV).
    destruct (usage_C_tail fx5 R5 M5 INV) as (fxE & RE & ME & MSE & REST).
    exists fxE, RE, ME. split; [eapply msteps_trans; [exact MS5 | exact MSE] | exact REST].
  Qed.
End UA.
End DUC.
