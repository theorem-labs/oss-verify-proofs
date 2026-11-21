(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (54 recorded proofs replaced by written proofs (ms_inb_true, ms_cov_cons, ms_cov_app and 51 more)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk MemSplit MmapSim RefMemcpyLib.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_MemsetLib () := "C47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4andbI47Corelib4Init5Logic3and00C47Corelib4Init5Logic3iffC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z2ltC46Stdlib4Bool4Bool=andb_true_iffC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9MorphismsFreflexive_proper_proxyC47Corelib7Classes>Morphisms_Prop@and_iff_morphismC56Stdlib6ZArith6BinInt1Z6leb_leC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC56Stdlib6ZArith6BinInt1Z6ltb_ltK47Corelib4Init5Logic3and01C47Corelib4Init5Logic7and_indK47Corelib4Init9Datatypes4prod01C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndc59OSSVerify5KrLib2AS9MemsetLib6ms_inbC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C47Corelib7Classes?RelationClasses>iff_TransitiveI47Corelib7Numbers7BinNums1Z00C47Corelib7Classes?RelationClasses=iff_ReflexiveI47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00c59OSSVerify5KrLib2AS9MemsetLib6ms_covC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3orbK47Corelib4Init5Logic2eq01C46Stdlib5Lists4List=repeat_lengthC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List;existsb_appC47Corelib4Init9Datatypes3appC46Stdlib5Lists4List2InC46Stdlib5Lists4List7existsbI47Corelib4Init5Logic2ex00C46Stdlib5Lists4List>existsb_existsc59OSSVerify5KrLib2AS9MemsetLib;ms_inb_trueC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01c59OSSVerify5KrLib2AS9MemsetLib8ms_chainC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K47Corelib7Numbers7BinNums8positive02K46Stdlib9micromega7EnvRing5PExpr02K47Corelib7Numbers7BinNums8positive01K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z;lt_ge_casesI47Corelib4Init5Logic2or00K47Corelib4Init5Logic2or01K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega7EnvRing5PExpr03K47Corelib4Init5Logic2or02C47Corelib4Init9Datatypes8list_indK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01C46Stdlib5Lists4List4inclc59OSSVerify5KrLib2AS9MemsetLib<ms_chain_covC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9MemsetLib9ms_cov_InC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00c59OSSVerify5KrLib2AS9MemsetLib5cfillC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C45stdpp9bitvector;definitions;bv_unsignedC46Stdlib4Bool4Bool<andb_false_rC56Stdlib6ZArith6BinInt1Z3subC46Stdlib5LogicHFunctionalExtensionalityIfunctional_extensionalityK47Corelib4Init9Datatypes4bool02C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic3notC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic9False_indC59OSSVerify5KrLib2AS7StoreOk9mem_growsC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00I47Corelib4Init5Logic5False00K47Corelib4Init5Logic4True01C56Stdlib6ZArith6BinInt1Z8leb_specI47Corelib4Init9Datatypes8BoolSpec00C56Stdlib6ZArith6BinInt1Z8ltb_specK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib2AS5Hoare3at_C1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6repeatC59OSSVerify5KrLib2AS7CatExec6wbytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega7EnvRing5PExpr07C59OSSVerify5KrLib2AS<RefMemcpyLib4at_uC1?~~~~~~~~~~~~~~~C46Stdlib4Bool4BoolBnot_true_iff_falseC47Corelib7Classes9Morphisms@subrelation_reflC47Corelib7Program6Basics4implC47Corelib7Classes9Morphisms5flip2C47Corelib7Classes9MorphismsFsubrelation_respectfulC47Corelib4Init5Logic6eq_symc59OSSVerify5KrLib2AS9MemsetLib;ms_cov_consC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC59OSSVerify5KrLib2AS8MemSplit>wbytes_outsideC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natC45stdpp9bitvector;definitions7Z_to_bvC47Corelib5Lists7ListDef3nthC47Corelib4Init5Peano2ltC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specC46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib5Lists4List=nth_repeat_ltC59OSSVerify5KrLib2AS8MemSplit=wbytes_insideC1?~~~~~~~~~~~~~~~C47Corelib7Classes9MorphismsBsubrelation_properK46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelC47Corelib7Classes>Morphisms_Prop@not_iff_morphismI47Corelib4Init9Datatypes3nat00C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_ltC47Corelib7Classes9MorphismsIiff_flip_impl_subrelationK46Stdlib9micromega=RingMicromega3Op201K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses8or_morphC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega8ZifyInst7Inj_Z_Zc59OSSVerify5KrLib2AS9MemsetLib?ms_cov_by_chainC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9MemsetLib:cfill_fullC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okc59OSSVerify5KrLib2AS9MemsetLib;cfill_growsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7StoreOk<store_ok_subC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7StoreOk=store_ok_monoC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C56Stdlib6ZArith6BinInt1Z3mulC35stdpp7tactics<f_equal_helpC56Stdlib6ZArith6BinInt1Z9pow_add_rC56Stdlib6ZArith4Zdiv1Z>mod_mod_divideC56Stdlib6ZArith6BinInt1Z=mod_pos_boundc59OSSVerify5KrLib2AS9MemsetLib3cbzC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions5bv_eqC56Stdlib6ZArith6BinInt1Z6moduloC45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z7mod_modC59OSSVerify5KrLib2AS8PropExec<bv_wrap8_modC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions@Z_to_bv_unsignedc59OSSVerify5KrLib2AS9MemsetLib5cbyteC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00c59OSSVerify5KrLib2AS9MemsetLib9cbyte_modC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9MemsetLibAmod4_mod_pow2_genC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec=bv_wrap64_modC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9MemsetLib7ms_replC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing5PExpr05C47Corelib4Init9Datatypes7nat_indC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesc59OSSVerify5KrLib2AS9MemsetLib>ms_repl_nonnegC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z7mod_addC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z7add_0_lC56Stdlib6ZArith6BinInt1Z9div_smallC56Stdlib6ZArith6BinInt1Z7div_addC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2c59OSSVerify5KrLib2AS9MemsetLib9cbz_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7StepTac6u_Z2bvC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9MemsetLib3c32C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9MemsetLib4c32hC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9MemsetLib3c64C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9MemsetLibEZ_to_le_bytes_ms_replC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9MemsetLib9cbyte_cbzC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9MemsetLib5u_c32C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesc59OSSVerify5KrLib2AS9MemsetLib5u_c64C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6shiftlC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC56Stdlib6ZArith6BinInt1Z?mul_mod_distr_lC56Stdlib6ZArith6BinInt1Z8mul_commC56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C59OSSVerify5KrLib2AS8PropExec6v_slliC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7div_mulc59OSSVerify5KrLib2AS9MemsetLib8u_slli56C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec7v_mulhuC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9MemsetLib6u_c32hC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec6v_srliC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z7testbitC56Stdlib6ZArith6BinInt1Z=testbit_neg_rC56Stdlib6ZArith6BinInt1Z;shiftl_specC59OSSVerify5KrLib2AS8PropExec>Z_testbit_highC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6bits_0C56Stdlib6ZArith6BinInt1Z9land_specC56Stdlib6ZArith6BinInt1Z9bits_inj'C56Stdlib6ZArith6BinInt1Z4lxorC56Stdlib6ZArith6BinInt1Z@add_nocarry_lxorC56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z8lxor_lorc59OSSVerify5KrLib2AS9MemsetLibDlor_disjoint_shift32C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec4v_orC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions8bv_swrapC56Stdlib6ZArith6BinInt1Z3oppC45stdpp9bitvector;definitions?bv_half_modulusK46Stdlib9micromega7EnvRing5PExpr06C46Stdlib6ZArith4ZdivBZminus_mod_idemp_lc59OSSVerify5KrLib2AS9MemsetLib>mod4_mod_pow2'C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z9land_onesC59OSSVerify5KrLib2AS8PropExec6v_subwC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec6v_andiC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7add_modC56Stdlib6ZArith6BinInt1Z4lnotC56Stdlib6ZArith6BinInt1Z4predC56Stdlib6ZArith6BinInt1Z:ones_equivC56Stdlib6ZArith6BinInt1Z=ones_mod_pow2C56Stdlib6ZArith8Zbitwise1Z?sub_land_same_lC56Stdlib6ZArith6BinInt1Z5ldiffC56Stdlib6ZArith6BinInt1Z:ldiff_landC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z<ldiff_ones_rC56Stdlib6ZArith6BinInt1Z9mod_smallC56Stdlib6ZArith6BinInt1Z:land_assocc59OSSVerify5KrLib2AS9MemsetLib;land_trunc4C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00C56Stdlib6ZArith6BinInt1Z=pow2_bits_eqbc59OSSVerify5KrLib2AS9MemsetLib<land_4_casesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec5v_addC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS5Hoare5at_atC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9MemsetLib:ms_v_add_ZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec5v_subC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec6v_addiC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyK4ELinuxProcessSemantics5Riscv5Instr5instr0=C45stdpp9bitvector;definitions4BvWfK45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC59OSSVerify5KrLib2AS8PropExec4getrC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C59OSSVerify5KrLib2AS8PropExec6regupdC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepC59OSSVerify5KrLib2AS8PropExec9step_subwC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec4mkstC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9MemsetLib>asanreflect_fxC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics5Riscv5Instr5instr00K4ELinuxProcessSemantics5Riscv5Instr5aluop02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K4ELinuxProcessSemantics5Riscv5Instr5instr0BC59OSSVerify5KrLib2AS8PropExec:step_mulhuC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5mulop04K4ELinuxProcessSemantics5Riscv5Instr5instr0:C59OSSVerify5KrLib2AS8PropExec7step_orC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop09K4ELinuxProcessSemantics5Riscv5Instr5instr07C45stdpp9bitvector;definitions9bv_signedC59OSSVerify5KrLib2AS5Hoare7at_addiC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9MemsetLib>cfill_store_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7MmapSim:step_sb_atC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9MemsetLib;cfill_storeC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5msize01C59OSSVerify5KrLib2AS7SeqExec:step_sw_atC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5msize03C59OSSVerify5KrLib2AS7SeqExec:step_sd_atC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5msize04C59OSSVerify5KrLib2AS5Hoare?regs_agree_reflC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9MemsetLib7ms_clobC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS5Hoare@regs_agree_transC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS9MemsetLib8ms_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS5Hoare>regs_agree_updC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS<RefMemcpyLib5keepsC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6or_indC59OSSVerify5KrLib2AS<RefMemcpyLib;callee_keptC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums8positive00".
(* [comment removed for export] *)
Unset Lia Cache.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ms_inb (i : Z) (iv : Z * Z) : bool := (fst iv <=? i) && (i <? fst iv + snd iv).
Definition ms_cov (L : list (Z * Z)) (i : Z) : bool := existsb (ms_inb i) L.

Lemma ms_inb_true : forall i o m, ms_inb i (o, m) = true <-> o <= i < o + m.
Proof.
  intros i o m. unfold ms_inb. cbn [fst snd]. rewrite andb_true_iff, Z.leb_le, Z.ltb_lt. tauto.
Qed.

Lemma ms_cov_cons : forall iv L i, ms_cov (iv :: L) i = ms_inb i iv || ms_cov L i.
Proof. reflexivity. Qed.

Lemma ms_cov_app : forall L1 L2 i, ms_cov (L1 ++ L2) i = ms_cov L1 i || ms_cov L2 i.
Proof. intros. unfold ms_cov. apply existsb_app. Qed.

Lemma ms_cov_In : forall L i o m, In (o, m) L -> o <= i < o + m -> ms_cov L i = true.
Proof.
  intros L i o m Hin Hi. unfold ms_cov. apply existsb_exists. exists (o, m). split; [exact Hin|].
  apply ms_inb_true. exact Hi.
Qed.

(* [comment removed for export] *)
Fixpoint ms_chain (from to : Z) (L : list (Z * Z)) : Prop :=
  match L with
  | [] => to <= from
  | (o, m) :: L' => o <= from /\ ms_chain (o + m) to L'
  end.

Lemma ms_chain_cov : forall L from to i,
  ms_chain from to L -> from <= i < to -> exists o m, In (o, m) L /\ o <= i < o + m.
Proof.
  induction L as [|[o m] L IH]; intros from to i Hc Hi; cbn [ms_chain] in Hc.
  - lia.
  - destruct Hc as [Ho Hc].
    destruct (Z.lt_ge_cases i (o + m)) as [Hlt|Hge].
    + exists o, m. split; [left; reflexivity | lia].
    + destruct (IH (o + m) to i Hc ltac:(lia)) as (o' & m' & Hin & Hi').
      exists o', m'. split; [right; exact Hin | exact Hi'].
Qed.

(* [comment removed for export] *)
Lemma ms_cov_by_chain : forall (L L' : list (Z * Z)) n,
  incl L' L -> ms_chain 0 n L' -> forall i, 0 <= i < n -> ms_cov L i = true.
Proof.
  intros L L' n Hincl Hc i Hi.
  destruct (ms_chain_cov L' 0 n i Hc Hi) as (o & m & Hin & Hom).
  apply (ms_cov_In L i o m); [apply Hincl, Hin | exact Hom].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section CFill.
  Variable mem0 : word -> option byte.
  Variable d : word.
  Variable n : Z.
  Variable c : byte.
  Hypothesis Hn : 0 <= n.
  Hypothesis Hnw : bv_unsigned d + n < 2 ^ 64.

  Definition cfill (L : list (Z * Z)) : word -> option byte :=
    fun x => if (bv_unsigned d <=? bv_unsigned x) && (bv_unsigned x <? bv_unsigned d + n)
                && ms_cov L (bv_unsigned x - bv_unsigned d)
             then Some c else mem0 x.

  Lemma cfill_nil : cfill [] = mem0.
  Proof.
    apply functional_extensionality. intro x. unfold cfill. cbn [ms_cov existsb].
    rewrite andb_false_r. reflexivity.
  Qed.

  Lemma cfill_grows : forall L, mem_grows mem0 (cfill L).
  Proof.
    intros L x Hx. unfold cfill. destruct (_ && _); [discriminate | exact Hx].
  Qed.

  (* [comment removed for export] *)
  Lemma cfill_ext : forall L1 L2,
    (forall i, 0 <= i < n -> ms_cov L1 i = ms_cov L2 i) -> cfill L1 = cfill L2.
  Proof.
    intros L1 L2 H. apply functional_extensionality. intro x. unfold cfill.
    destruct (Z.leb_spec (bv_unsigned d) (bv_unsigned x)); [|reflexivity].
    destruct (Z.ltb_spec (bv_unsigned x) (bv_unsigned d + n)); [|reflexivity].
    cbn [andb]. rewrite H by lia. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma cfill_store : forall L o (m : nat),
    0 <= o -> o + Z.of_nat m <= n ->
    wbytes (cfill L) (at_ d o) (repeat c m) = cfill ((o, Z.of_nat m) :: L).
  Proof.
    intros L o m Ho Hm. apply functional_extensionality. intro x.
    pose proof (u64_range d). pose proof (u64_range x).
    assert (Ha : bv_unsigned (at_ d o) = bv_unsigned d + o) by (apply at_u; lia).
    destruct (Z.lt_ge_cases (bv_unsigned x) (bv_unsigned d + o)) as [Hlo|Hge];
      [| destruct (Z.lt_ge_cases (bv_unsigned x) (bv_unsigned d + o + Z.of_nat m)) as [Hin|Hhi]].
    - rewrite wbytes_outside by (rewrite repeat_length, Ha; lia).
      unfold cfill. rewrite ms_cov_cons.
      replace (ms_inb (bv_unsigned x - bv_unsigned d) (o, Z.of_nat m)) with false
        by (symmetry; apply not_true_iff_false; rewrite ms_inb_true; lia).
      reflexivity.
    - rewrite wbytes_inside by (rewrite repeat_length, Ha; lia).
      rewrite nth_repeat_lt by (rewrite Ha; lia). unfold cfill. rewrite ms_cov_cons.
      replace (ms_inb (bv_unsigned x - bv_unsigned d) (o, Z.of_nat m)) with true
        by (symmetry; apply ms_inb_true; lia).
      destruct (Z.leb_spec (bv_unsigned d) (bv_unsigned x)); [|lia].
      destruct (Z.ltb_spec (bv_unsigned x) (bv_unsigned d + n)); [|lia].
      reflexivity.
    - rewrite wbytes_outside by (rewrite repeat_length, Ha; lia).
      unfold cfill. rewrite ms_cov_cons.
      replace (ms_inb (bv_unsigned x - bv_unsigned d) (o, Z.of_nat m)) with false
        by (symmetry; apply not_true_iff_false; rewrite ms_inb_true; lia).
      reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma cfill_full : forall L,
    (forall i, 0 <= i < n -> ms_cov L i = true) ->
    cfill L = wbytes mem0 d (repeat c (Z.to_nat n)).
  Proof.
    intros L Hcov. apply functional_extensionality. intro x.
    pose proof (u64_range d). pose proof (u64_range x).
    unfold cfill.
    destruct (Z.leb_spec (bv_unsigned d) (bv_unsigned x)) as [H1|H1].
    - destruct (Z.ltb_spec (bv_unsigned x) (bv_unsigned d + n)) as [H2|H2]; cbn [andb].
      + rewrite Hcov by lia. rewrite wbytes_inside by (rewrite repeat_length; lia).
        rewrite nth_repeat_lt by lia. reflexivity.
      + rewrite wbytes_outside by (rewrite repeat_length; lia). reflexivity.
    - cbn [andb]. rewrite wbytes_outside by (rewrite repeat_length; lia). reflexivity.
  Qed.

  Lemma cfill_full_chain : forall L L',
    incl L' L -> ms_chain 0 n L' ->
    cfill L = wbytes mem0 d (repeat c (Z.to_nat n)).
  Proof. intros L L' Hi Hc. apply cfill_full. apply (ms_cov_by_chain L L'); assumption. Qed.

  (* [comment removed for export] *)
  Lemma cfill_store_ok : forall segs L o (m : nat),
    store_ok segs mem0 d (Z.to_nat n) = true ->
    0 <= o -> o + Z.of_nat m <= n ->
    store_ok segs (cfill L) (at_ d o) m = true.
  Proof.
    intros segs L o m Hok Ho Hm. pose proof (u64_range d).
    apply (store_ok_mono segs m mem0); [apply cfill_grows|].
    apply (store_ok_sub segs mem0 d (at_ d o) (Z.to_nat n) m); try (rewrite ?at_u; lia). exact Hok.
  Qed.
End CFill.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma mod4_mod_pow2_gen : forall t k j, 0 <= j <= k -> (t mod 2 ^ k) mod 2 ^ j = t mod 2 ^ j.
Proof.
  intros t k j Hk. apply Z.mod_mod_divide.
  exists (2 ^ (k - j)). rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.

(* [comment removed for export] *)
Definition cbyte (cv : word) : byte := Z_to_bv 8 (bv_unsigned cv).
(* [comment removed for export] *)
Definition cbz (cv : word) : Z := bv_unsigned cv mod 256.
(* [comment removed for export] *)
Definition c32 (cv : word) : word := Z_to_bv 64 (cbz cv * 16843009).
(* [comment removed for export] *)
Definition c32h (cv : word) : word := Z_to_bv 64 (cbz cv * 16843009 * 2 ^ 32).
(* [comment removed for export] *)
Definition c64 (cv : word) : word := Z_to_bv 64 (cbz cv * 72340172838076673).

Lemma cbz_range : forall cv, 0 <= cbz cv < 256.
Proof. intros cv. unfold cbz. apply Z.mod_pos_bound. lia. Qed.

Lemma cbyte_mod : forall cv, Z_to_bv 8 (bv_unsigned cv mod 256) = cbyte cv.
Proof.
  intros cv. unfold cbyte. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap8_mod. apply Z.mod_mod. lia.
Qed.

Lemma cbyte_cbz : forall cv, cbyte cv = Z_to_bv 8 (cbz cv).
Proof. intros cv. unfold cbz. symmetry. apply cbyte_mod. Qed.

(* [comment removed for export] *)
Lemma cbyte_Z : forall z, cbyte (Z_to_bv 64 z) = Z_to_bv 8 z.
Proof.
  intros z. unfold cbyte. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap8_mod, bv_wrap64_mod.
  apply mod4_mod_pow2_gen. lia.
Qed.

(* [comment removed for export] *)
Fixpoint ms_repl (k : nat) : Z := match k with O => 0 | S k' => 1 + 256 * ms_repl k' end.

Lemma ms_repl_nonneg : forall k, 0 <= ms_repl k.
Proof. induction k; cbn [ms_repl]; lia. Qed.

Lemma Z_to_le_bytes_ms_repl : forall k z, 0 <= z < 256 ->
  Z_to_le_bytes k (z * ms_repl k) = repeat (Z_to_bv 8 z) k.
Proof.
  induction k as [|k IH]; intros z Hz; [reflexivity|].
  cbn [Z_to_le_bytes ms_repl repeat]. pose proof (ms_repl_nonneg k). f_equal.
  - apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap8_mod.
    replace (z * (1 + 256 * ms_repl k)) with (z + (z * ms_repl k) * 256) by lia.
    rewrite Z.mod_add by lia. reflexivity.
  - rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
    replace (z * (1 + 256 * ms_repl k)) with (z + (z * ms_repl k) * 256) by lia.
    rewrite Z.div_add by lia. rewrite Z.div_small by lia. rewrite Z.add_0_l. apply IH. exact Hz.
Qed.

Lemma u_c32 : forall cv, bv_unsigned (c32 cv) = cbz cv * 16843009.
Proof. intros cv. pose proof (cbz_range cv). unfold c32. apply u_Z2bv; lia. Qed.

Lemma u_c32h : forall cv, bv_unsigned (c32h cv) = cbz cv * 16843009 * 2 ^ 32.
Proof. intros cv. pose proof (cbz_range cv). unfold c32h. apply u_Z2bv; lia. Qed.

Lemma u_c64 : forall cv, bv_unsigned (c64 cv) = cbz cv * 72340172838076673.
Proof. intros cv. pose proof (cbz_range cv). unfold c64. apply u_Z2bv; lia. Qed.

Lemma wleb4_c32 : forall cv, word_to_le_bytes 4 (c32 cv) = repeat (cbyte cv) 4.
Proof.
  intros cv. unfold word_to_le_bytes. rewrite u_c32, cbyte_cbz.
  change 16843009 with (ms_repl 4). apply Z_to_le_bytes_ms_repl. apply cbz_range.
Qed.

Lemma wleb8_c64 : forall cv, word_to_le_bytes 8 (c64 cv) = repeat (cbyte cv) 8.
Proof.
  intros cv. unfold word_to_le_bytes. rewrite u_c64, cbyte_cbz.
  change 72340172838076673 with (ms_repl 8). apply Z_to_le_bytes_ms_repl. apply cbz_range.
Qed.

(* [comment removed for export] *)
Lemma u_slli56 : forall cv, bv_unsigned (v_slli cv 56) = cbz cv * 2 ^ 56.
Proof.
  intros cv. unfold v_slli, cbz. rewrite Z_to_bv_unsigned, Z.shiftl_mul_pow2 by lia.
  pose proof (u64_range cv).
  unfold bv_wrap. change (bv_modulus 64) with (2 ^ 56 * 256).
  rewrite Z.mul_comm, Z.mul_mod_distr_l by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma mulhu_c32 : forall cv (m : word), bv_unsigned m = 4311810304 ->
  v_mulhu (v_slli cv 56) m = c32 cv.
Proof.
  intros cv m Hm. unfold v_mulhu, c32. f_equal. rewrite u_slli56, Hm.
  rewrite Z.shiftr_div_pow2 by lia.
  replace (cbz cv * 2 ^ 56 * 4311810304) with ((cbz cv * 16843009) * 2 ^ 64) by lia.
  apply Z.div_mul. lia.
Qed.

Lemma slli32_c32 : forall cv, v_slli (c32 cv) 32 = c32h cv.
Proof.
  intros cv. unfold v_slli, c32h. f_equal. rewrite u_c32, Z.shiftl_mul_pow2 by lia. reflexivity.
Qed.

Lemma srli32_c32h : forall cv, v_srli (c32h cv) 32 = c32 cv.
Proof.
  intros cv. unfold v_srli, c32. f_equal. rewrite u_c32h, Z.shiftr_div_pow2 by lia.
  apply Z.div_mul. lia.
Qed.

Lemma lor_disjoint_shift32 : forall a b, 0 <= a -> 0 <= b < 2 ^ 32 ->
  Z.lor (a * 2 ^ 32) b = a * 2 ^ 32 + b.
Proof.
  intros a b Ha Hb.
  assert (Hl : Z.land (a * 2 ^ 32) b = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i 32).
    - rewrite <- Z.shiftl_mul_pow2, Z.shiftl_spec by lia. rewrite (Z.testbit_neg_r a) by lia. reflexivity.
    - rewrite (Z_testbit_high 32 b) by lia. apply andb_false_r. }
  rewrite <- Z.lxor_lor by exact Hl. symmetry. apply Z.add_nocarry_lxor. exact Hl.
Qed.

Lemma or_c64 : forall cv, v_or (c32h cv) (c32 cv) = c64 cv.
Proof.
  intros cv. pose proof (cbz_range cv). unfold v_or, c64. f_equal. rewrite u_c32h, u_c32.
  rewrite lor_disjoint_shift32 by lia. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma mod4_mod_pow2' : forall t k, 2 <= k -> (t mod 2 ^ k) mod 4 = t mod 4.
Proof.
  intros t k Hk. apply Z.mod_mod_divide.
  exists (2 ^ (k - 2)). change 4 with (2 ^ 2). rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma negw_and3 : forall x : word,
  v_andi (v_subw (Z_to_bv 64 0) x) 3 = Z_to_bv 64 ((- bv_unsigned x) mod 4).
Proof.
  intros x. unfold v_andi, v_subw. f_equal.
  change (bv_wrap 64 3) with (Z.ones 2). rewrite Z.land_ones by lia.
  rewrite Z_to_bv_unsigned. change (bv_unsigned (Z_to_bv 64 0)) with 0.
  unfold bv_swrap. rewrite bv_wrap64_mod.
  change (bv_half_modulus 32) with (2 ^ 31).
  unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32). change (2 ^ 2) with 4.
  rewrite mod4_mod_pow2' by lia.
  rewrite <- Zminus_mod_idemp_l.
  rewrite mod4_mod_pow2' by lia.
  replace (0 - bv_unsigned x + 2 ^ 31) with ((- bv_unsigned x) + 536870912 * 4) by lia.
  rewrite Z.mod_add by lia.
  rewrite Zminus_mod_idemp_l.
  replace (- bv_unsigned x - 2 ^ 31) with ((- bv_unsigned x) + (- 536870912) * 4) by lia.
  rewrite Z.mod_add by lia. reflexivity.
Qed.

Lemma neg_mod4_range : forall u, 0 <= (- u) mod 4 <= 3.
Proof. intros u. pose proof (Z.mod_pos_bound (- u) 4). lia. Qed.

Lemma neg_mod4_aligns : forall u, (u + (- u) mod 4) mod 4 = 0.
Proof.
  intros u. rewrite Z.add_mod, Z.mod_mod by lia.
  rewrite <- Z.add_mod by lia. replace (u + - u) with 0 by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma land_trunc4 : forall a, 0 <= a < 2 ^ 64 -> Z.land a (2 ^ 64 - 4) = a - a mod 4.
Proof.
  intros a Ha.
  replace (2 ^ 64 - 4) with (Z.ldiff (Z.ones 64) (Z.ones 2)).
  2:{ rewrite Z.ldiff_land, <- Z.sub_land_same_l, Z.land_ones by lia.
      rewrite Z.ones_mod_pow2 by lia. rewrite !Z.ones_equiv. lia. }
  rewrite Z.ldiff_land, Z.land_assoc, Z.land_ones by lia.
  rewrite Z.mod_small by lia.
  rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia.
  rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
  pose proof (Z.div_mod a 4 ltac:(lia)). lia.
Qed.

Lemma andi_m4 : forall m, 0 <= m < 2 ^ 64 ->
  v_andi (Z_to_bv 64 m) (-4) = Z_to_bv 64 (m - m mod 4).
Proof.
  intros m Hm. unfold v_andi. f_equal. rewrite u_Z2bv by lia.
  change (bv_wrap 64 (-4)) with (2 ^ 64 - 4). apply land_trunc4. exact Hm.
Qed.

(* [comment removed for export] *)
Lemma land_4_cases : forall a, 0 <= a -> Z.land a 4 = 0 \/ Z.land a 4 = 4.
Proof.
  intros a Ha.
  destruct (Z.testbit a 2) eqn:E; [right|left];
    apply Z.bits_inj'; intros i Hi; rewrite Z.land_spec;
    change 4 with (2 ^ 2); rewrite Z.pow2_bits_eqb by lia;
    destruct (Z.eqb_spec 2 i) as [<-|Hne]; rewrite ?E, ?Z.bits_0; try reflexivity;
    apply andb_false_r.
Qed.

Lemma andi_4_cases : forall x : word, exists s4, v_andi x 4 = Z_to_bv 64 s4 /\ (s4 = 0 \/ s4 = 4).
Proof.
  intros x. exists (Z.land (bv_unsigned x) 4). split.
  - unfold v_andi. f_equal.
  - apply land_4_cases. apply u64_range.
Qed.

(* [comment removed for export] *)
Lemma ms_v_add_Z : forall (x : word) z, 0 <= z < 2 ^ 64 ->
  v_add x (Z_to_bv 64 z) = at_ x z.
Proof. intros x z Hz. unfold v_add, at_. rewrite u_Z2bv by lia. reflexivity. Qed.

Lemma ms_v_add_at_Z : forall (x : word) o z, 0 <= z < 2 ^ 64 ->
  v_add (at_ x o) (Z_to_bv 64 z) = at_ x (o + z).
Proof. intros x o z Hz. rewrite ms_v_add_Z by lia. apply at_at. Qed.

Lemma ms_v_sub_ZZ : forall a b, 0 <= b <= a -> a < 2 ^ 64 ->
  v_sub (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a - b).
Proof. intros a b H1 H2. unfold v_sub. rewrite !u_Z2bv by lia. reflexivity. Qed.

Lemma ms_v_addi_Z : forall a i, 0 <= a < 2 ^ 64 ->
  v_addi (Z_to_bv 64 a) i = Z_to_bv 64 (a + i).
Proof. intros a i Ha. unfold v_addi. rewrite u_Z2bv by lia. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ms_step_subw_at : forall segs regs pc mem rom w rd rs1 rs2 v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op32 ALU_SUB rd rs1 rs2, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_subw (getr regs rs1) (getr regs rs2) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs1 rs2 v Hf He Hd Hrd Hv.
  rewrite (step_subw segs regs pc mem rom w rd rs1 rs2 Hf He Hd). rewrite Hrd, Hv. reflexivity.
Qed.

Lemma ms_step_mulhu_at : forall segs regs pc mem rom w rd rs1 rs2 v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Mul M_MULHU rd rs1 rs2, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_mulhu (getr regs rs1) (getr regs rs2) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs1 rs2 v Hf He Hd Hrd Hv.
  rewrite (step_mulhu segs regs pc mem rom w rd rs1 rs2 Hf He Hd). rewrite Hrd, Hv. reflexivity.
Qed.

Lemma ms_step_or_at : forall segs regs pc mem rom w rd rs1 rs2 v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op ALU_OR rd rs1 rs2, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_or (getr regs rs1) (getr regs rs2) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs1 rs2 v Hf He Hd Hrd Hv.
  rewrite (step_or segs regs pc mem rom w rd rs1 rs2 Hf He Hd). rewrite Hrd, Hv. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Stores.
  Variable segs : list Segment.
  Variable mem0 : word -> option byte.
  Variable d : word.
  Variable n : Z.
  Variable cv : word.
  Hypothesis Hn : 0 <= n.
  Hypothesis Hnw : bv_unsigned d + n < 2 ^ 64.
  Hypothesis Hok : store_ok segs mem0 d (Z.to_nat n) = true.

  #[local] Abbreviation CF := (cfill mem0 d n (cbyte cv)).

  Lemma cf_sb : forall regs pc rom w rs1 rs2 (imm : bv 12) L o0 o,
    fetch_word segs pc = Some w -> is_ecall w = false ->
    decode_any w = Some (Store SZ1 rs1 rs2 imm, 4%Z) ->
    getr regs rs1 = at_ d o0 -> (o0 + bv_signed imm = o)%Z ->
    getr regs rs2 = cv ->
    0 <= o -> o + 1 <= n ->
    RiscvSemantics.step segs (mkst regs pc (CF L) rom) =
    MachineOk (mkst regs (v_addi pc 4) (CF ((o, 1) :: L)) rom).
  Proof.
    intros regs pc rom w rs1 rs2 imm L o0 o Hf He Hdc Hrs1 Ho Hrs2 H0 H1.
    replace ((o, 1) :: L) with ((o, Z.of_nat 1) :: L) by reflexivity.
    rewrite <- (cfill_store mem0 d n (cbyte cv) Hnw L o 1) by lia.
    eapply step_sb_at; [exact Hf | exact He | exact Hdc | | exact Hrs2 | reflexivity |].
    - rewrite Hrs1, at_addi, Ho. reflexivity.
    - apply (cfill_store_ok mem0 d n (cbyte cv) Hnw segs); assumption || lia.
  Qed.

  Lemma cf_sw : forall regs pc rom w rs1 rs2 (imm : bv 12) L o0 o v,
    fetch_word segs pc = Some w -> is_ecall w = false ->
    decode_any w = Some (Store SZ4 rs1 rs2 imm, 4%Z) ->
    getr regs rs1 = at_ d o0 -> (o0 + bv_signed imm = o)%Z ->
    getr regs rs2 = v -> word_to_le_bytes 4 v = repeat (cbyte cv) 4 ->
    0 <= o -> o + 4 <= n ->
    RiscvSemantics.step segs (mkst regs pc (CF L) rom) =
    MachineOk (mkst regs (v_addi pc 4) (CF ((o, 4) :: L)) rom).
  Proof.
    intros regs pc rom w rs1 rs2 imm L o0 o v Hf He Hdc Hrs1 Ho Hrs2 Hv H0 H1.
    replace ((o, 4) :: L) with ((o, Z.of_nat 4) :: L) by reflexivity.
    rewrite <- (cfill_store mem0 d n (cbyte cv) Hnw L o 4) by lia.
    rewrite <- Hv.
    eapply step_sw_at; [exact Hf | exact He | exact Hdc | | exact Hrs2 |].
    - rewrite Hrs1, at_addi, Ho. reflexivity.
    - apply (cfill_store_ok mem0 d n (cbyte cv) Hnw segs); assumption || lia.
  Qed.

  Lemma cf_sd : forall regs pc rom w rs1 rs2 (imm : bv 12) L o0 o v,
    fetch_word segs pc = Some w -> is_ecall w = false ->
    decode_any w = Some (Store SZ8 rs1 rs2 imm, 4%Z) ->
    getr regs rs1 = at_ d o0 -> (o0 + bv_signed imm = o)%Z ->
    getr regs rs2 = v -> word_to_le_bytes 8 v = repeat (cbyte cv) 8 ->
    0 <= o -> o + 8 <= n ->
    RiscvSemantics.step segs (mkst regs pc (CF L) rom) =
    MachineOk (mkst regs (v_addi pc 4) (CF ((o, 8) :: L)) rom).
  Proof.
    intros regs pc rom w rs1 rs2 imm L o0 o v Hf He Hdc Hrs1 Ho Hrs2 Hv H0 H1.
    replace ((o, 8) :: L) with ((o, Z.of_nat 8) :: L) by reflexivity.
    rewrite <- (cfill_store mem0 d n (cbyte cv) Hnw L o 8) by lia.
    rewrite <- Hv.
    eapply step_sd_at; [exact Hf | exact He | exact Hdc | | exact Hrs2 |].
    - rewrite Hrs1, at_addi, Ho. reflexivity.
    - apply (cfill_store_ok mem0 d n (cbyte cv) Hnw segs); assumption || lia.
  Qed.
End Stores.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ms_clob : list reg := [11; 12; 13; 14; 15; 16]%bv.
Definition ms_agree (regs regs' : bvmap 5 word) : Prop :=
  regs_agree (fun r => In r ms_clob) regs regs'.

Lemma ms_agree_refl : forall regs, ms_agree regs regs.
Proof. intros regs. apply regs_agree_refl. Qed.

Lemma ms_agree_trans : forall r1 r2 r3, ms_agree r1 r2 -> ms_agree r2 r3 -> ms_agree r1 r3.
Proof. intros r1 r2 r3. apply regs_agree_trans. Qed.

Lemma ms_agree_upd : forall regs regs' (rd : reg) v,
  ms_agree regs regs' -> In rd ms_clob -> ms_agree regs (regupd regs' rd v).
Proof. intros regs regs' rd v H Hin. apply regs_agree_upd; assumption. Qed.

Lemma ms_agree_getr : forall regs regs' (r : reg),
  ms_agree regs regs' -> ~ In r ms_clob -> getr regs' r = getr regs r.
Proof. intros regs regs' r H Hn. apply H. exact Hn. Qed.

Lemma ms_agree_keeps : forall regs regs', ms_agree regs regs' -> keeps regs regs'.
Proof.
  intros regs regs' H r Hr. apply H. unfold callee_kept in Hr. unfold ms_clob. cbn [In] in *.
  intros Hc. decompose [or] Hr; subst; decompose [or] Hc; try discriminate; auto.
Qed.

Ltac in_clob := cbn [ms_clob In]; repeat first [ left; reflexivity | right ].
Ltac solve_ms_agree :=
  repeat (apply ms_agree_upd; [| in_clob]); first [apply ms_agree_refl | assumption].
