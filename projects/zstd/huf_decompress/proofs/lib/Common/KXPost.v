(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require PropExec.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXMem KXTac KXGo.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_KXPost () := "C47Corelib4Init9Datatypes3fstC46Stdlib5Lists4List7existsbK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions7Z_to_bvC59OSSVerify5KrLib3Lib8PropExec5v_srlC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3divI47Corelib4Init5Logic2eq00C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z6shiftrK47Corelib4Init5Logic2eq01C56Stdlib6ZArith6BinInt1Z3mulK47Corelib7Numbers7BinNums8positive01K47Corelib4Init5Logic2ex01C56Stdlib6ZArith4Zdiv1Z>mod_mod_divideC35stdpp7tactics<f_equal_helpC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z=mod_pos_boundK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C47Corelib4Init5Logic8eq_ind_rC69OSSVerify5KrLib6Common7KXSound3KXS8u_lit64aC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem5alu64C59OSSVerify5KrLib3Lib8PropExec7alu_srlC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic3and00I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K4ELinuxProcessSemantics5Riscv5Instr5aluop07K69OSSVerify5KrLib6Common6KXExec3KX24expr01C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC56Stdlib5Arith8PeanoNat3Nat8ltb_specC47Corelib4Init5Peano2ltI47Corelib4Init5Peano2le00C56Stdlib5Arith8PeanoNat3Nat3ltbI47Corelib4Init9Datatypes8BoolSpec00C69OSSVerify5KrLib6Common6KXExec3KX22evC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthK69OSSVerify5KrLib6Common6KXExec3KX24expr02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common6KXExec3KX26edenotC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common6KXPost2ezC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib3Lib8PropExec5v_addC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common7KXSound3KXS3eqmC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common7KXSound3KXS7eqm_modC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common7KXSound3KXS7eqm_addC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common7KXSound3KXS;eqm_Z_to_bvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec7alu_addC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec5v_subC1?~~~~~~~~~~~~~~~K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7compareC69OSSVerify5KrLib6Common7KXSound3KXS9eqm_mul_lC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC59OSSVerify5KrLib3Lib8PropExec7alu_subC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common6KXPost:srl_lit_ezC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib6Common6KXExec3KX24expr03C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib6Common6KXExec3KX24expr04C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics5Riscv3Sem5alu32C4ELinuxProcessSemantics5Riscv7Prelude4sextK69OSSVerify5KrLib6Common6KXExec3KX24expr05C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem7mul_divK69OSSVerify5KrLib6Common6KXExec3KX24expr06C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib6Common6KXExec3KX24expr07C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common6KXExec3KX27ext_valC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib6Common6KXExec3KX24expr08C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common6KXExec3KX22ebC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common6KXExec3KX28blob_valC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec5v_mulC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common7KXSound3KXS9eqm_mul_rC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common7KXSound3KXS9eqm_transC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec5m_mulC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common6KXExec3KX28expr_indC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MStateCZ_to_bv_bv_unsignedC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symI69OSSVerify5KrLib6Common6KXExec3KX24expr00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I4ELinuxProcessSemantics5Riscv5Instr5aluop00K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5aluop02K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00K4ELinuxProcessSemantics5Riscv5Instr5aluop03K4ELinuxProcessSemantics5Riscv5Instr5aluop04K4ELinuxProcessSemantics5Riscv5Instr5aluop05K4ELinuxProcessSemantics5Riscv5Instr5aluop06I4ELinuxProcessSemantics5Riscv5Instr5mulop00K4ELinuxProcessSemantics5Riscv5Instr5aluop08K4ELinuxProcessSemantics5Riscv5Instr5aluop09K4ELinuxProcessSemantics5Riscv5Instr5aluop0:K4ELinuxProcessSemantics5Riscv5Instr5mulop01K4ELinuxProcessSemantics5Riscv5Instr5mulop02K4ELinuxProcessSemantics5Riscv5Instr5mulop03K4ELinuxProcessSemantics5Riscv5Instr5mulop04K4ELinuxProcessSemantics5Riscv5Instr5mulop05K4ELinuxProcessSemantics5Riscv5Instr5mulop06K4ELinuxProcessSemantics5Riscv5Instr5mulop07K4ELinuxProcessSemantics5Riscv5Instr5mulop08K47Corelib4Init9Datatypes3nat02C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC59OSSVerify5KrLib3Lib5Frame3mkRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8KXBridge7kx_regsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common6KXPost9kx_regs_zC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common6KXPost5ez_okC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C69OSSVerify5KrLib6Common6KXExec3KX26a_baseC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common7KXSound3KXS6estartC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common6KXExec3KX25a_offC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib6Common6KXExec3KX25saddr01C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7bv_wrapC45stdpp9bitvector;definitions:bv_modulusC45stdpp9bitvector;definitions=bv_wrap_smallC45stdpp9bitvector;definitions@Z_to_bv_unsignedI69OSSVerify5KrLib6Common6KXExec3KX25saddr00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5KXTac7kE_atomC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega5Tauto8GFormula05C56Stdlib6ZArith6BinInt1Z4of_NC69OSSVerify5KrLib6Common6KXExec3KX24elenC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common7KXSound3KXS5elenZC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith4Znat5Nat2Z6inj_leI69OSSVerify5KrLib6Common6KXExec3KX23env00C1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib6Common7KXSound3KXS7know_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common7KXSound3KXS8log_flatC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib6Common6KXExec3KX26sentry01C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7forallbC47Corelib4Init9Datatypes9andb_propC69OSSVerify5KrLib6Common6KXExec3KX2>ranges_apart_xC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common7KXSound3KXS4flatC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5KXMem9log_apartC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common7KXSound3KXSDranges_apart_x_soundC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common6KXPost;elenZ_elen'C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C47Corelib4Init9Datatypes8list_indc59OSSVerify5KrLib6Common6KXPost:kx_apart_bC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02I47Corelib4Init5Logic2or00I69OSSVerify5KrLib6Common6KXExec3KX26sentry00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib6Common6KXExec3KX26kentry00C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01c59OSSVerify5KrLib6Common6KXPost;kx_log_wr_bC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5KXMem6log_wrC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3lebC47Corelib4Init9Datatypes4andbC69OSSVerify5KrLib6Common6KXExec3KX2:wr_coveredC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat6leb_leC59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC47Corelib4Init5Logic3notK69OSSVerify5KrLib6Common6KXExec3KX28sidecond05C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common7KXSound3KXS9scs_denotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common7KXSound3KXS8sc_denotC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C69OSSVerify5KrLib6Common6KXExec3KX2:storeok_scC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common7KXSound3KXS@storeok_sc_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common6KXExec3KX26adenotC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega;ZifyClasses;rew_iff_revC59OSSVerify5KrLib3Lib3Mem>store_ok_wviewC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common7KXSound3KXS6flat_uC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Z2Nat2idC46Stdlib9micromega;ZifyClasses5mkappK46Stdlib9micromega5Tauto8GFormula03C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_ltI69OSSVerify5KrLib6Common6KXExec3KX28sidecond00C1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init9Datatypes4prod00c59OSSVerify5KrLib6Common6KXPost;kx_log_in_bC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5KXMem:log_insideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common6KXExec3KX29zf_coversC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InI47Corelib4Init5Logic2ex00C46Stdlib5Lists4List>existsb_existsC69OSSVerify5KrLib6Common7KXSound3KXS?zf_covers_soundC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common6KXPost7win_ivlC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C47Corelib5Lists7ListDef3mapC47Corelib4Init9Datatypes3sndC59OSSVerify5KrLib3Lib5Frame6insideC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib3Lib5Frame3ivlC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00K46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z3oppC59OSSVerify5KrLib6Common5KXTac2kEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8KXBridge9zatoms_ltC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5KXTac3zsaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8KXBridge4zdenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5KXTac3zleC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common6KXPost;kx_apart_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common4KXGo@estart_zsa_splitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common4KXGo8elen_zleC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Common8KXBridge4zexp00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common6KXExec3KX26erangeC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C69OSSVerify5KrLib6Common7KXSound3KXS<erange_soundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8KXBridge<reads_scopedC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_errorC59OSSVerify5KrLib6Common8KXBridge7kx_valsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8KXBridge6kx_envC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3addC59OSSVerify5KrLib6Common8KXBridge5rdvalC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8KXBridge;kx_vals_nthC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C59OSSVerify5KrLib3Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec3rdnC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common6KXPost9estart_ezC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5KXTac>kx_rd_bytes_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common6KXExec3KX28expr_eqbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common7KXSound3KXS;expr_eqb_eqC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common6KXPost7kx_pickC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02C59OSSVerify5KrLib6Common8KXBridge4mkRlC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common7KXSound3KXS7regs_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec4getrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common6KXExec3KX26sr_getC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3subC46Stdlib9micromega;ZifyClasses9and_morphC59OSSVerify5KrLib6Common8KXBridge9getr_mkRlC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symK46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z7eqb_neqK45stdpp9bitvector;definitions2bv01C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses9not_morphK46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z9mod_smallC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC45stdpp9bitvector;definitions4BvWfC69OSSVerify5KrLib6Common6KXExec3KX24ridxC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common6KXPost:kx_pick_okC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3seqc59OSSVerify5KrLib6Common6KXPost<kx_regs_keepC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6mkapp2C4ELinuxProcessSemantics5Riscv3Sem2w0C56Stdlib6ZArith4Znat5Nat2Z8inj_succC56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxc59OSSVerify5KrLib6Common6KXPost<log_apart_ezC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common6KXPost<estart_ez_kEC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common6KXPost=log_inside_ezC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof03C56Stdlib6ZArith6BinInt1Z9pow_add_rC56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundC56Stdlib6ZArith6BinInt1Z7div_posC56Stdlib6ZArith6BinInt1Z=pow_le_mono_rI47Corelib7Numbers7BinNums1N00".
Import ListNotations.
Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma srl_lit_ez : forall z sh, alu64 ALU_SRL (Z_to_bv 64 z) (Z_to_bv 64 sh) = Z_to_bv 64 ((z mod 2^64) / 2^(sh mod 64)).
Proof.
ltac2:(KReplay.run1 (kr_t_KXPost ()) [] "h01zh11bh21ah31Hh47__arithh54__ffh68__varmaph75__with82shp;1p;2p;3p;4p;8p;7p;6p-1R0p10000R1p4p710p8P0P1p4p7210p8P0p1000Mp4p710p8g000ij11Tg001Nj1XTg001lj1MTg002Oj23j1BTg0035j2WTg003lj1<Tg004Jj24j1TTg004gj20Tg005Gj28j1UTg005dj32Tg006>j2@Tg006hj2:Tg007Hj25Tg007bj2?Tg008?j1;Tg008dj4RTg009>j4OTg009dj89Tg00:Aj27Tg00:]j2>Tg00;9j3LTg00;`j1KTg00<@j1ITg00<`j1HTg00=>j1GTg00=\j1FTg00>Gj2=Tg00>jj4JTg00?Uj7ETg00@9j2DTg00@[j2NTg00AGj3CTg00Afj4PTg00BXj3QTg00CAj66Tg00C_j1ATg00D_j3STg00EGj2VTg00F@R0g00F^R1#1R2#1#1#1#1#1R3#XR4#MR5f1R6,34R7f0R8,34R9'WR:f2R;%<2R2%<3R3'4R<'0R=1063,42'8,34R>9258X15P0106<R?1@47R@/03,:8,34=25>X00P0108<RA1083RB,:=,34=25>X00P010A3RA,42R=,8?RCA259>X00P0P5%B4R>P>PC142BRC,8?RDP5\0/5>P0P0%U?R>P>P=PCP0\0RC/5>P0P0%T2R>P>PAPB15C>P8P<P3P01?83920<X00%;1#;#1#;#1#<,42R21?23,50CRCOG9G9G91:?Ag00GCR2/78R1g00Ga10;6R<,>2R>17<6f3/0;,>2AL;68P6n2001000000120000000UX10X20P>\1^10^20P8P?P3g00H<R1#K%I1%H0%G0%F0R1g00Hhg00IGR>P>g00IgR>P01=02g00JG1=03CJg00JnFE1D1>P8P;g00KNR>g00KnR1'51N8;=2>1dAC026CPb5b6b71723P8b4O3b39Q?AE61@49%A8E6P@%A6E6134D925:eg00LN?S791V79E6X80W0o"). Qed.

Section Ez.
Variable zv : list Z.
Variable E : env.
Hypothesis HA : forall j, (j < length zv)%nat -> ev E j = Z_to_bv 64 (nth j zv 0).

Fixpoint ez (e : expr) : Z :=
  match e with
  | ELit z => z
  | EVar j => if Nat.ltb j (length zv) then nth j zv 0 else bv_unsigned (ev E j)
  | EAlu ALU_ADD a b => ez a + ez b
  | EAlu ALU_SUB a b => ez a - ez b
  | EMd M_MUL a b => ez a * ez b
  | EAlu ALU_SRL a (ELit sh) => (ez a mod 2^64) / 2^(sh mod 64)
  | _ => bv_unsigned (edenot E e)
  end.

Lemma ez_ok : forall e, edenot E e = Z_to_bv 64 (ez e).
Proof.
ltac2:(KReplay.run1 (kr_t_KXPost ()) ["Ez"] "p'0h01bi001bh13IHbh21zi011zh32opi022oph43IHah51ai031ah61ni041nh72b1h82b2h92sxi052sxh:1Hh;2Hah<1Lh=7__arithh>6__sat3h?4__x1h@4__x2hA1ei061ehB1ii071ihC1ki081khD2loi092lohE4__ffhF6__sat0hG6__sat1hH6__sat2hI8__varmaphJ5__withK2b0i0:2b0hL1jhM2shi0;2shi0<2a0i0=2e0i0>1mi0?3op0p&0p;1p;2p;3p;4p;6p;7p;5p;:g000ij1ETg001Nj1eTg001lj1tTg002Oj25Tg007Hj2PTg00M:j1_Tg00N7j2sTg00NWj2pTg00O<j2RTg00OTj2JTg00Onj2UTg00PNR0j3iTg00Q2j2fTg00Qkk40;Tg006>j21Tg00RGj1`Tg00SDj24Tg00D_j33Tg00TAj1=Tg00U6j2>Tg00USj2BTg003lj1[Tg004Jj2GTg004gj2<Tg005Gj2FTg005dj30Tg00V0j2lTg00Vgj2ATg00Wbj1KTg00Xaj6WTg00C_j1VTg00Y`j3ITg00Zcj2jTg00CAj6@Tg00[\j2hTg00;`j1gTg00<@k10>Tg00\Sk20=Tg00<`k10<Tg00]1k40:Tg00=>k109Tg00=\k108Tg00]Oj2cTg00^2k104Tg00>Gk203Tg00^Pk302Tg00_3k301Tg00_Vk300Tg00>jj4}Tg00?Uj7|Tg00@9j2{Tg00@[j2zTg00AGj3yTg00Afj4xTg007bj2:Tg00`9j2wTg00:Aj2^Tg00`aj3vTg00aEj2]Tg00b6j2uTg00bWj4\Tg00cXj6XTg00d4j2rTg00dmj2qTg00ejj3LTg00fgj3OTg00gdj1TTg00hLj3ZTg00i4j3HTg00i_j3QTg00j\j46Tg00kFj3NTg00lCj4YTg00m@j4oTg00n>j4aTg00o;j2dTg0104j4bTg0113j2nTg011jj4mTg012kk505Tg013lk206Tg014cm:07Tg015bj1MTg016ej4STg00:]j2kTf4R1f3R2f2R3'4f1R4f0R5#='530p=;15459023p=7P11523P4%M5CSp=~g00F@R6P1P2P3P4P5E@p=Dg00GCR7/k5p=C1145,53p=9P2P3P4%M5CSp=8g00LN?345p=2f5R81123,51P4%M5CSp=?g017AR9g00F^R:#ER;#E#E#E#ER<#ER=#eR>#tR?p,1ER@P5P>P5D;RAXA915>5,P?P?P@%_5RBP>PBD;RBeX26g018>RCp,2zvRD,s6RE,p51R5E1JE51U5E3i1U4Eg00KNRFP01R3E1JE3P?1f@1R0P>PFP6P4P6P1PDP7H0;11>0RDn0100000020000C7P41R2Ep,2HAP1P5O2W<P5O11JE2P?P>PDP0P0D~W<P5O1n200210000000021000010000bKb0P?P@%`5R0P>P0D;R0eWLg018]RDPDP?14@1RE14@3RG535RHP>PDP6P5%=1RI%=3RJ'>RK1BIJRL11>HRHPHPHPHP9P6P3%=8RM%[;RN%[=R='GRO'<RP1<5=,GNRQ'F14@8RR14@2RS534,1>f7RT,4@RU=32R,1>RVPVPVPVf8RV,4@RWf6RX,4@RY531,1>RZPZn0110000081010;101043010?10<10:3010?10<10:3010?10<10:3010?10<10:4010510910410=40105108107104PHPHPHn01102000:00000000000000000000C7P1P?%=2RH,5>RZg019IR[?35G15>KR\50?X0?P?%=4R],5>R^15>IR_=3[5=0?\X0?P?1lZ^R`A0?5\X0?11>ZR\11>^Ra'>1>H]Rb1<HORc15>J,1>Rd,>5/AKX261<]ORe1<IORf/>5/AKX26PcPHPeP]%KHRK%K]RgEWPa%V]RhDDP\%VHRiDD3I15>bRb90?`eA3[Z^1jZ^E@14@4R`P5E@PSP3E@A3[S`=0?beP?PZg01:5Rb?35G15>LR[50?X0?P?P^A3b_5=0?[X0?P?1hZ^RjA0?5[X0?1B\a1BH]R[Pc1B5d/ALX26Pe1Bf5/ALX26g00H<Rk#g&0>kP620=63P4&0<6H0:&096&086Rkg00Hhg00IGRlPlg00IgRlP61c6:Rm&04:R:-0361c6;R;60266016g01:aB006m;C}g00JnF|1{klP5P3g00KnRl,PF1z53=0FldAy674CxbEbIbJX?6X@6Rl1::4,>51B54506^?6^@6RkP5PJPIO2b=1::],>H=06[P61::J,>I1BPcR;/A5X261wN=1^7NRm%C=1^7O[Rn[%CNRog01;HRpAvN=4UW;%CORq\p^;o%=XRX/]O%CX%=V/<ORV#C\q[1]MO%CM%=T/<ORT#C\q[P2g01;d1u7N'PPmeO1PnPlPkP5PVf:RV#=/<OO2b=b>bFbGbHb>1<JORk,::,>f1Bfk506P61::cRk,>P1::I,>X,A5X26PPPMPk1::H%KMP:PcPHPKC\EWP;P5EXb:PLP5EXb:PaPhDDP\PiDD3I15>[R[90?jeA3bZ^1rZ^E@P`P5E@PSP3E@A3bS`=0?[eP?g01<J?3S`R[99>>RbP[P[C8A0?[beP?g01=6?3S`Rb99>>R[PbPbC8A0?b[eP?g01=b?3S`R[99>>RbP[P[C8A0?[beP?g01>N?3S`Rb99>>R[PbPbC8A0?b[eP9P?12R`P>P9P6P41<XORO/FQ12YG,1>12WE,1>RWPWPWPWf9,4@/2R,1>RWPWn0110000081010;101043010?10<10:3010?10<10:3010?10<10:3010?10<10:4010510910410=40105108107104C7^1AP4P?15>XP?15>3,25P>1<3=,GN,FTC7X0?1qX4PYP8E@P?%_4,4@,2YP>1<4=,GN,FOC7eX1BXM6P5O1P?P>P>1f@4,2YRBPBPBE?P?%`4,4@,2YRBP>11>BC7eX10X6CP5O1P?P@AL345R0P>P0D;P?P>P>14@VRVA32G`'2R0P0P0E?P?AL234,4@,2VR0P>11>0C7eW1X89X79X3DP3P4P5O3P?P@AO345R0P>P0D;P?P>P>%e<R<%TGR0%T`RB5Z27H>,2VROPOPOE?P?AO234,4@,2VROP>11>OC7eW1X89X79X3DP3P4P5O3g01?:ROP?P@AQ345RNP>PND;P?P>P>P>P2PGP`C6,2VRNPNPNE?P?AQ234,4@,2VRNP>11>NC7eW1X89X79W3P3P4P5O3P?P@AN345RNP>PND;P?P>P>P<P2P0PBC69H<>,2VR0P0P0E?P?AN234,4@,2VRVP>11>VC7eW1X89X79X3OP3P4P5O3P?P@P2P3P4P5CYRVP>PVD;P?P>P>f<,4@RVP1P2P3P`CoR0'2RNPNPNE?P?P1P2P3P4CYRN,4@R=,2VR8P>11>8C7eW1X09X6CXDCX9FP2P3P4P5O4P?P@P2P3P4P5CaR8P>P8D;R8P?P>P>P11d@2P3P4Cb,2VRXPXPXE?P?P1P2P3P4Ca,4@,2VRVP>11>VC7eW1X6CXB6XCCX9FP2P3P4P5O4n0110601081110110104301021031003110210310030102103100311021031004010510910410640105108107104P5O1P?12S`P>P9P6P41FfQ12EG,1>12YE,1>RYPYPYPY12UR,1>RUPUn0110000081010;101043010?10<10:3010?10<10:3010?10<10:3010?10<10:4010510910410=40105108107104C7eP?g01?f?3S`RU99>>RRPUPUC8A0?UReP?g01@R?3S`RR99>>RUPRPRC8A0?RUeP?g01A>?3S`RU99>>RRPUPUC8A0?URen01103010:01010000000001000000P?P@AL124RRP>PRD;eX1AX09X4AX59W3P?P>P>%TSRR=Z1B9H<>RUPUPUE?P?P@AO124RUP>PUD;eX1AX09X4AX59X3DPOP?P>P5PEPGC6REP>POP6P51:IJRJ11>EREPEPEPEPEPEPEn0110200080000000000000000C7P1P?PZP>g01AjREP5PGC615>JRG50?X0?P?P^P>PEP_P5C6=0?GX0?P?1nZ^R_A0?5GX0?1:\a1:H]RGPc1:5d/AJX26Pe1:f5/AJX261:ce1:HePGPePcPHPKCmPHPeP]PgC\I05PaPhDDP\PiDD3I15>GRG90?_eP>PEPZP^C6206Z^E@P`P5E@PSP3E@P>PEPSP`C6=0?GeP?P>g01BVPSP`C6RG99>>REPGPGC8A0?GEeP?P>g01CBPSP`C6RE99>>RGPEPEC8A0?EGeP?P>g01CnPSP`C6RG99>>REPGPGC8A0?GEeP?P>g01DZPSP`C6RE99>>RGPEPEC8A0?EGeP?P>g01EFPSP`C6RG99>>REPGPGC8A0?GEeP?P>g01F2PSP`C6RE99>>RGPEPEC8A0?EGeP?P>g01F^PSP`C6R`99>>RSP`P`C8A0?`Sen0110>01080100000000000000P?P@AQ124RSP>PSD;eX1AX09X4AX59X3OP?P>P>P<P1PRPBC69H<>R<P<P<E?P?P@AN124R1P>P1D;eX1AX09X4AX59X3OP?P>P>P0P0P0E?P?P=P>%=NC7eX4AX59X6CXDCX9FP?P>P>P21d@3P4P5CbR4P4P4E?P8eX6CXB6XCCX9FP5N:07WAo"). Qed.

Definition kx_regs_z (sr : list expr) : bvmap 5 word :=
  mkR (Z_to_bv 64 (ez (nth 1 sr (ELit 0)))) (Z_to_bv 64 (ez (nth 2 sr (ELit 0)))) (Z_to_bv 64 (ez (nth 3 sr (ELit 0))))
      (Z_to_bv 64 (ez (nth 4 sr (ELit 0)))) (Z_to_bv 64 (ez (nth 5 sr (ELit 0)))) (Z_to_bv 64 (ez (nth 6 sr (ELit 0))))
      (Z_to_bv 64 (ez (nth 7 sr (ELit 0)))) (Z_to_bv 64 (ez (nth 8 sr (ELit 0)))) (Z_to_bv 64 (ez (nth 9 sr (ELit 0))))
      (Z_to_bv 64 (ez (nth 10 sr (ELit 0)))) (Z_to_bv 64 (ez (nth 11 sr (ELit 0)))) (Z_to_bv 64 (ez (nth 12 sr (ELit 0))))
      (Z_to_bv 64 (ez (nth 13 sr (ELit 0)))) (Z_to_bv 64 (ez (nth 14 sr (ELit 0)))) (Z_to_bv 64 (ez (nth 15 sr (ELit 0))))
      (Z_to_bv 64 (ez (nth 16 sr (ELit 0)))) (Z_to_bv 64 (ez (nth 17 sr (ELit 0)))) (Z_to_bv 64 (ez (nth 18 sr (ELit 0))))
      (Z_to_bv 64 (ez (nth 19 sr (ELit 0)))) (Z_to_bv 64 (ez (nth 20 sr (ELit 0)))) (Z_to_bv 64 (ez (nth 21 sr (ELit 0))))
      (Z_to_bv 64 (ez (nth 22 sr (ELit 0)))) (Z_to_bv 64 (ez (nth 23 sr (ELit 0)))) (Z_to_bv 64 (ez (nth 24 sr (ELit 0))))
      (Z_to_bv 64 (ez (nth 25 sr (ELit 0)))) (Z_to_bv 64 (ez (nth 26 sr (ELit 0)))) (Z_to_bv 64 (ez (nth 27 sr (ELit 0))))
      (Z_to_bv 64 (ez (nth 28 sr (ELit 0)))) (Z_to_bv 64 (ez (nth 29 sr (ELit 0)))) (Z_to_bv 64 (ez (nth 30 sr (ELit 0))))
      (Z_to_bv 64 (ez (nth 31 sr (ELit 0)))).

Lemma kx_regs_ez : forall sr, kx_regs E sr = kx_regs_z sr.
Proof.
ltac2:(KReplay.run1 (kr_t_KXPost ()) ["Ez"] "h01bh12srp%0p;1p;2p;Op;3p;4p;6g00<@j1ETg000ij17Tg001Nj18Tg001lj19Tg01GJj16Tg00M:j1@Tg008?j1;Tg01Gij2:Tg00SDj24Tg01HUlO2Tg005dj33Tg007Hj2DTg01IGj2CTg01JCj1?Tg00Qkj4=Tg00TAj1>Tg002Oj2<Tg01K?j1ATg00CAj6BTg017AR0f2R1f1R2f0R3C=p=1%>3,<2p=0f6f5f4f31412%A3EBp=5%E0g00F^#7R0#7#7#7#7#7#8R1#9R4g01L7#6R5g00GC#@R6713S00,01S01%;0#8/:4R0P3p,1ER7%65R8?126S02'4%68R9?126R:,47S03%69R;?126R<,47S04%6;R=?126R>,47S05%6=R??126R@,47RA%6?RB?126RC,47RD%6BRE?126RF,47RG%6ERH?126RI,47RJ%6HRK?126RL,47RM%6KRN?126RO,47RP%6NRQ?126RR,47RS%6QRT?126RU,47RV%6TRW?126RX,47RY%6WRZ?126R[,47R\%6ZR]?126R^,47R_%6]R`?126Ra,47Rb%6`Rc?126Rd,47Re%6cRf?126Rg,47Rh%6fRi?126Rj,47Rk%6iRl?126Rm,47Rn%6lS06?126Ro,47RpQ06#6S07?126Rq,47RrQ07#6S08?126Rs,47RtQ08#6S09?126Ru,47RvQ09#6S0:?126Rw,47RxQ0:#6S0;?126S0<,47RyQ0;#6S0=?126S0>,47RzQ0=#6S0??126S0@,47R{Q0?#6S0A?126S0B,47R|Q0A#6S0C?126R},47R~MO2A1526,01R5Q02,01R2101:R:101<R<101>R>101@R@101CRC101FRF101IRI101LRL101ORO101RRR101URU101XRX101[R[101^R^101aRa101dRd101gRg101jRj101mRm101oRo101qRq101sRs101uRu101wRwQ0<,01S0<Q0>,01S0>Q0@,01S0@Q0B,01S0B101}MO2R}33X04P4A1836R8,01S02P5P3Q03Q04Q05PAPDPGPJPMPPPSPVPYP\P_PbPePhPkPnPpPrPtPvPxPyPzP{P|P~MO2=30}X04P4A1936R9,01S03P5P2P3Q04Q05PAPDPGPJPMPPPSPVPYP\P_PbPePhPkPnPpPrPtPvPxPyPzP{P|P~MO2=30}X04P4A1;36R;,01S04P5P2P:P3Q05PAPDPGPJPMPPPSPVPYP\P_PbPePhPkPnPpPrPtPvPxPyPzP{P|P~MO2=30}X04P4A1=36R=,01S05P5P2P:P<P3PAPDPGPJPMPPPSPVPYP\P_PbPePhPkPnPpPrPtPvPxPyPzP{P|P~MO2=30}X04P4A1?36R?,01S0DP5P2P:P<P>P3PDPGPJPMPPPSPVPYP\P_PbPePhPkPnPpPrPtPvPxPyPzP{P|P~MO2=30}X04P4A1B36RB,01S0EP5P2P:P<P>P@P3PGPJPMPPPSPVPYP\P_PbPePhPkPnPpPrPtPvPxPyPzP{P|P~MO2=30}X04P4A1E36RE,01S0FP5P2P:P<P>P@PCP3PJPMPPPSPVPYP\P_PbPePhPkPnPpPrPtPvPxPyPzP{P|P~MO2=30}X04P4A1H36RH,01S0GP5P2P:P<P>P@PCPFP3PMPPPSPVPYP\P_PbPePhPkPnPpPrPtPvPxPyPzP{P|P~MO2=30}X04P4A1K36RK,01S0HP5P2P:P<P>P@PCPFPIP3PPPSPVPYP\P_PbPePhPkPnPpPrPtPvPxPyPzP{P|P~MO2=30}X04P4A1N36RN,01S0IP5P2P:P<P>P@PCPFPIPLP3PSPVPYP\P_PbPePhPkPnPpPrPtPvPxPyPzP{P|P~MO2=30}X04P4A1Q36RQ,01S0JP5P2P:P<P>P@PCPFPIPLPOP3PVPYP\P_PbPePhPkPnPpPrPtPvPxPyPzP{P|P~MO2=30}X04P4A1T36RT,01S0KP5P2P:P<P>P@PCPFPIPLPOPRP3PYP\P_PbPePhPkPnPpPrPtPvPxPyPzP{P|P~MO2=30}X04P4A1W36RW,01S0LP5P2P:P<P>P@PCPFPIPLPOPRPUP3P\P_PbPePhPkPnPpPrPtPvPxPyPzP{P|P~MO2=30}X04P4A1Z36RZ,01R\P5P2P:P<P>P@PCPFPIPLPOPRPUPXP3P_PbPePhPkPnPpPrPtPvPxPyPzP{P|P~MO2=30}X04P4A1]36R],01R_P5P2P:P<P>P@PCPFPIPLPOPRPUPXP[P3PbPePhPkPnPpPrPtPvPxPyPzP{P|P~MO2=30}X04P4A1`36R`,01RbP5P2P:P<P>P@PCPFPIPLPOPRPUPXP[P^P3PePhPkPnPpPrPtPvPxPyPzP{P|P~MO2=30}X04P4A1c36Rc,01ReP5P2P:P<P>P@PCPFPIPLPOPRPUPXP[P^PaP3PhPkPnPpPrPtPvPxPyPzP{P|P~MO2=30}X04P4A1f36Rf,01RhP5P2P:P<P>P@PCPFPIPLPOPRPUPXP[P^PaPdP3PkPnPpPrPtPvPxPyPzP{P|P~MO2=30}X04P4A1i36Ri,01RkP5P2P:P<P>P@PCPFPIPLPOPRPUPXP[P^PaPdPgP3PnPpPrPtPvPxPyPzP{P|P~MO2=30}X04P4A1l36Rl,01RnP5P2P:P<P>P@PCPFPIPLPOPRPUPXP[P^PaPdPgPjP3PpPrPtPvPxPyPzP{P|P~MO2=30}X04P4Q06?136Rp,01RYP5P2P:P<P>P@PCPFPIPLPOPRPUPXP[P^PaPdPgPjPmP3PrPtPvPxPyPzP{P|P~MO2=30}X04P4Q07?136Rr,01RVP5P2P:P<P>P@PCPFPIPLPOPRPUPXP[P^PaPdPgPjPmPoP3PtPvPxPyPzP{P|P~MO2=30}X04P4Q08?136Rt,01RSP5P2P:P<P>P@PCPFPIPLPOPRPUPXP[P^PaPdPgPjPmPoPqP3PvPxPyPzP{P|P~MO2=30}X04P4Q09?136Rv,01RPP5P2P:P<P>P@PCPFPIPLPOPRPUPXP[P^PaPdPgPjPmPoPqPsP3PxPyPzP{P|P~MO2=30}X04P4Q0:?136Rx,01RMP5P2P:P<P>P@PCPFPIPLPOPRPUPXP[P^PaPdPgPjPmPoPqPsPuP3PyPzP{P|P~MO2=30}X04P4Q0;?136Ry,01RJP5P2P:P<P>P@PCPFPIPLPOPRPUPXP[P^PaPdPgPjPmPoPqPsPuPwP3PzP{P|P~MO2=30}X04P4Q0=?136Rz,01RGP5P2P:P<P>P@PCPFPIPLPOPRPUPXP[P^PaPdPgPjPmPoPqPsPuPwQ0<P3P{P|P~MO2=30}X04P4Q0??136R{,01RDP5P2P:P<P>P@PCPFPIPLPOPRPUPXP[P^PaPdPgPjPmPoPqPsPuPwQ0<Q0>P3P|P~MO2=30}X04P4Q0A?136R|,01RAP5P2P:P<P>P@PCPFPIPLPOPRPUPXP[P^PaPdPgPjPmPoPqPsPuPwQ0<Q0>Q0@P3P~MO2=30}X04P4Q0C?136R6,01R1P5P2P:P<P>P@PCPFPIPLPOPRPUPXP[P^PaPdPgPjPmPoPqPsPuPwQ0<Q0>Q0@Q0BP3MO2=30}X04Q01Q02Q03Q04Q05Q0DQ0EQ0FQ0GQ0HQ0IQ0JQ0KQ0LP\P_PbPePhPkPnPYPVPSPPPMPJPGPDPAP1MO2,D0P7P6P6F5P7P|P|F5P7P{P{F5P7PzPzF5P7PyPyF5P7PxPxF5P7PvPvF5P7PtPtF5P7PrPrF5P7PpPpF5P7PlPlF5P7PiPiF5P7PfPfF5P7PcPcF5P7P`P`F5P7P]P]F5P7PZPZF5P7PWPWF5P7PTPTF5P7PQPQF5P7PNPNF5P7PKPKF5P7PHPHF5P7PEPEF5P7PBPBF5P7P?P?F5P7P=P=F5P7P;P;F5P7P9P9F5P7P8P8F5P7Q00Q00F51C73%?3530eW1o"). Qed.

Lemma estart_ez : forall a, 0 <= ez (a_base a) < 2^64 -> estart E a = ez (a_base a) + a_off a.
Proof.
ltac2:(KReplay.run1 (kr_t_KXPost ()) ["Ez"] "p'0h01bh11Rh21ah31kh41zi006a_basei015a_offi021sp;1p;2p;3p;6g01LVj14Tg00TAj11Tg00:]j29Tg000ij12Tg003lj1>Tg004Jj2ETg00:Aj27Tg00Gaj28Tg01MSj2<Tg01NQj1;Tg00U6j20Tg005dj33Tg01OMj2:Tg001Nj1HTg001lj1GTg002Oj2FTg006>j26Tg01PKj2DTg007Hj2CTg01Q1j1BTg01QZj3ATg00CAj65Tg01RFj2@Tg00SDj2=Tg01K?j1?Tg01S5R0P0g00GCR0f0R1#4#1R2'9g00F^#2R3#>%23#2#2#2#2R3#>'ER4,72'8g00F@R2p,1ER5f1R6'<%46#1%;6'033[P1g017A1:61#4#1R7,901774'8%H3R3#GR7f2R4#1R8,F3R91631/04f3#1/04R:532X07P21D38R71014=32:X42R:P2P8P:1086,C2P7P11908%B3,78'8e9A38E516391@38E51=54%?4E51:46R4#4R8,=5,63%;4R3'0%18/03R3532e1<54=323eW1X32W0P6P1O2n01102000121100101W2o"). Qed.

End Ez.

Lemma kE_atoms : forall zv xs j, (j < length zv)%nat -> ev (kE zv xs) j = Z_to_bv 64 (nth j zv 0).
Proof.
ltac2:(KReplay.run1 (kr_t_KXPost ()) [] "g01T3o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section LogChecks.
Variable segs : list Segment.

Definition kx_apart_b (kn : list kentry) (log : list sentry) (a : saddr) (n : expr) : bool :=
  forallb (fun s => match s with SE ea w _ => ranges_apart_x kn (a_base ea) (a_off ea) (elen w) (a_base a) (a_off a) n end) log.

Lemma elenZ_elen' : forall E w, (w <= 8)%nat -> elenZ E (elen w) = Z.of_nat w.
Proof.
ltac2:(KReplay.run1 (kr_t_KXPost ()) ["LogChecks"] "h04__x1h11Eh22Hwh33Hw0h47__arithh54__ffh68__varmaph75__with84cstrh91wh:1zp;1p;2p;3p;4p;7p;6p;<p;8g01GJj10Tg00OTR0j2@Tg000ij11Tg001Nj1DTg01TlR1j1;Tg01PKj2STg005dj33Tg007Hj25Tg003lj16Tg00:]R2j22Tg01ULj4BTg01V3j1ATg00;`j1^Tg00<@j1VTg00\Sj2UTg00=>j1RTg00=\j1PTg00>Gj27Tg00]Oj2LTg00>jj48Tg01VXj1JTg01W:j3ITg01W]j7HTg00@9j2FTg00@[j2GTg00AGj3ETg00Afj4KTg004Jj2=Tg00:Aj2:Tg00Gaj29Tg01XAj1MTg01Q1j1NTg01QZj3OTg00CAj6>Tg002Oj2QTg006>j2?Tg01RFj2TTg00M:j1]Tg00SDj2\Tg01X_j1[Tg01YZj2WTg01ZWl<XTg00?Uj7YTg01[<j8ZTg018>R3g00F@R4P0P1P2g01[`f5f4R2f3R1f2R0f1R5f0R6M<Xp=CP5g00HhR7g00IGR8P8g00IgR9P6g00JnFYp=4P1P7P8P8P9P0P5P6GZp=<g01\Bg01L7#0#0#0#0#0#0#0#0R1,@6P4g00F^R:#1R;#1#1R<#1#1#1R=#DR>%;5R?'SR@%;0RA9346X:4RBP4P?PB154?RBP@1@51%6<R<,2?R@P5P?PBP1P<154<ECP6CBP@%A0g00GCR@/2Ag00H<RA#^%VA1U45%R4%P4RAP4174@g01]>R11L4:R:C8,4ARB%J8RCPAP4P:P1174<C8,4APCPAP7P8P8P9PBP4P:g00JG%6;R;,74=I4>C8,4AFHC<C<1FA9P6P0g00KNRAg00KnR9'51G60=3A9dAE4@5CKb5b6b7X0412@6125<12@0%6=,=;,:0'9[[^04P6%;2P5P0O3b4b8b312@?R@%M>,=;,:?'9e%N>,:?,9@e9O>?E>1Q>?,?>1T>?E>%]?,\0,?>=34?e%[5,W0=34?eW2X93W1o"). Qed.

Lemma kx_apart_ok : forall E M kn log a n,
  know_ok segs E M kn -> log_flat E log -> kx_apart_b kn log a n = true -> log_apart E log (estart E a) (elenZ E n).
Proof.
ltac2:(KReplay.run1 (kr_t_KXPost ()) ["LogChecks"] "p'0h01Dh12H1h21si001sh31Hh42H2h53Hflh62IHh72Hfh83logh91Eh:3Hf'h;3Hknh<2Hwh=1Mh>1ah?2a0h@7a_base0hA7a_base1hB6a_off0hC6a_off1hD2eai012eahE2knhF1lhG1nhH4resthI1vhJ1wi021whK1zi036a_basei045a_offi056e_addri065e_vali077e_widthp;1p;4p;2p;3p;7p;<p;6p;5g000ij1CTg001Nj1OTg001lj1KTg01]ej1TTg00<@j1NTg01^Gj4[Tg01_Fj23Tg00;`j1XTg01`Fj3?Tg01LVj12Tg01NQj10Tg01X_j17Tg01aEj3FTg01aaj3ZTg00GaR0j2ITg01bDj7ETg01GJj1<Tg00OTj2LTg01Tlj11Tg01cIj3@Tg01MSj28Tg01YZj2DTg01dEj4HTg01e@l<VTg01fLj3QTg00cXj6PTg01OMj25Tg01gJj4UTg01gej5^Tg01hGj4]Tg005dj3MTg01iDj3\Tg00U6j2BTg00:]j2ATg01idj2JTg00KNR1f3R2f2R3f1R4f0R5C]g00KnR63Mp==f5R7f4R818231D45CHp=9g01j>R9?\45p=:f6R:P7P8P2%23%04P5FEp=>AM156p=41B34/A5p=Y1B23/A4/J5p=W1545,83p=G1D45,B3p=S1A821B34/A5'Jp=R%24%05'5,83p=61B:7/A81D34,B2/A5'Jp=;g01\Bg00F^#C#C#CR6#C#C#C#O#K%O6#K#T[g01k=#N%N9R6g01S5R;g017AR<p,4segsR=P7P8P2C[P9f7R>/35P:P4P8P2C=f9R?P3P?P7P?P8E9[[X86%X9R@,3:P7P@P2P3C=g01l<W3W7P913?5f8R@P4P:P7C=f;RAP3PAP>PAP:E9[[f:RB1:34'3P?1:23P>P:C=f<RC1:82PCP@PCP>E9[[[^F6P5g018>f>RD/35f=REP4PAPBC=f@RFP3PFPCPFPAE9[[f?RGA?823/:4'3PDA?782/:3PCPAC=PG%2:RH%0:RI%77PEPEPCF>RJP9P1P5fCRK%23RL%03RM%74RNfAROPOPFF>n01100000130101102106X29=F92RP;Z5%4J%4P'IP0PF%2>%0>%7:PDPDPEF>#4P9P1P5fDRPPLPMPNfBRJPJPOF>n01100000130101102106X29=F98#4PKA?@>:/:7PKPGPKPDE9P5PJ%2?%0?%7@PFPFPGF>#4P9P1P5fGRQPLPMPNfERR#2RS%0RRTPPFEn01100000130101102106X29=F9>#4P0g01L7#<#<#<#<#<#<#<#<RU,LBfFRV%1B7@A13V@'IPQA?CAB/:?PQPKPQPJE9P:1LCUfIRU%1E7@D13UA'IP0fJR0%1D7@G130CfKRCA?FGD/:EPCPQPCPVE9P5fLRE%1F7@OfMRD/3GfNRW/8KRX%1J18W0RY1DWURZ=YYXCWPWPFPYPZCHP=PWPDPE%2KR=%0KRX%7JR[%20R\%00R]PUfHR^P?M<VAGW=XRX?SW[AGW\]R]P]PZPXDRg00F@RXfOR]%7K'DfPR\?GSTRTP5A6\EERSPSP\PCPTF;XKXP5%1KRTAQ]K:EPA6]PPRPPTA6]CCRTPTP]P0PPF;P;fQRP%1R7@5P\%24RT%04RS%7VPWPWPDF>#4fSRV?GLMR[%1QA6V]]RQPQPVPWP[F;fTR[/82RQ%1^R=18[\R_P_P[P]PQF;]0]1]5PR1545=@[=PV1534R=#2RR%0=RQ%7UPPPPP\F>#4fVRU1523R_;6_R`%10fRRa=6UaRbPbPUPPP`F;P;fXR`/30fWR0PCP4P[C=fZRCPEPCP3PCfUE9[[P015:7R7#2%07%7DPTPSP[FE#4P9P1P5f\R[PLPMPNPHPIfYRIFEn01100000130101102106X29=F9E#4f[RE15@>RH;6HRH%1]A6E22RSPSPEPUPHF;15?@R?,8[RH%1\18[8RUPUP[P0PHF;]0]4]1]6PV13EDPCPWP=P0C=f]R=P]P=P_P=P`E9[[PC%2?%0?%7\PRPQP0FE#4P9P1P5f_PLPMPN15>:R>P>P[F>n01100000130101102106X29=F9]#4f^R]15ABRB;6BRB%1a1582R8=6]8R8P8P]PIPBF;P5W0W4W1W6XCXXA<P4P5O2n01100000120103104P^P4POP5O4W0W1W5XBXX@<P4P5O2n01100000121103104P2PAP5O3b0b0PGP5P@O2CUPWA?KJO/:FPYPZCHeW:W5P4P5O2n2001000000121000000W3W<P4P5O2n2001000000121000000W4W1P4P5O2n2001000000121000000b3W3W7W6XH6XI<WJXD;P3P4P5O3n01100000131105107106X?9P2D^W;WGW>W8WEW=W9o"). Qed.

Definition kx_log_wr_b (kn : list kentry) (log : list sentry) : bool :=
  forallb (fun s => match s with SE a w _ => Nat.leb 1 w && Nat.leb w 8 && wr_covered kn kn a w end) log.

Lemma kx_log_wr_ok : forall E m kn log,
  know_ok segs E m kn -> log_flat E log -> kx_log_wr_b kn log = true -> log_wr segs m E log.
Proof.
ltac2:(KReplay.run1 (kr_t_KXPost ()) ["LogChecks"] "p'0h01Hh12H1h22H2h34__p1h44__x1h52Hvh61mh71si001sh82H0h92Hfh:3Hw0h;7__arithh<4__ffh=4__p2h>8__varmaph?5__with@4__x2hA4__x3hB4cstrhC1jhD3loghE1nhF1xhG1zhH1EhI2H3hJ2H4hK3Hf'hL3HflhM2HjhN3HknhO2HwhP2IHhQ1ShR1ai011ahS2a0hT1bhU2knhV1lhW4resthX1vhY1wi021whZ2z4i036e_addri045e_vali057e_widthp&0p;1p;4p;2p;3p;6p;;p;7p;5p;<p;8g000ij1FTg001Nj1fTg001lj1^Tg01]ej1lTg00<@j1PTg01^Gk404Tg01_Fj29Tg01lXj2BTg01mVj47Tg00;`j1STg01GJj1<Tg01nNj21Tg01nnj23Tg01oLj4:Tg01aEj3XTg01aaj3QTg00GaR0j24Tg00OTR1j26Tg020Mj2{Tg01TlR2j12Tg01cIj3LTg00:]R3j25Tg00:AR4j2>Tg01MSj2MTg00U6j2CTg0210j1DTg021_j3GTg01VXj1\Tg005dj38Tg022\j1?Tg0235j2kTg01iDj3HTg0246j4[Tg0257j3jTg0267j2iTg00CAj6hTg026Xj3gTg027Ym;0;Tg028aj2ZTg029^k40:Tg02:^R5j1YTg00O<R6k209Tg02;>j2NTg003lj1dTg01ULj4ETg01V3j1cTg02;[k203Tg01idj2bTg02<=j2OTg02<fj3JTg02=Oj2aTg00\Sj2WTg00]1k400Tg00=>j1~Tg00=\j1|Tg00]Oj2TTg008?j1zTg00>jj4@Tg00>Gj2wTg02>;j7vTg00@9j2uTg007Hj2]Tg00@[j2tTg00AGj3xTg00Afj4yTg02>_j4sTg02?Jj7rTg006>j2_Tg02@Ej4qTg00cXj6`Tg02ACj2}Tg01gJj4pTg01gek501Tg01`Fk302Tg02Aal<oTg01ZWl<eTg02BFj6nTg00?Uj7mTg01W]k705Tg01[<k806Tg00KNR7f0R8g00KnR938p=0g01j>R:f1R;;H8p=Rf3R<f2R=<02;=H:8p=;g00F@R>/]8p==P>g018>R?P>P>P5f4R5P2P<g02BjP=P;P8M<op>08P?P>P6P2P4g02CWf5R4P5P<P=P;P8M<ep>07P?P>P1P2P3g01[`P4P5P<P=P;P8M<ep=IP;g00HhR3g00IGR2P2g00IgR1P8Enp=VP;P3P2P2P1P8g00JnFmp=AP=P3P2P2P1P;P8K05p=KP<P3P2P2P1P=P;P8L06p=Ug01\Bg00F^R6#FR@#F#FRA#F#F#F#fRB#^%fA#^RC#lRD[g01k=#P%P:REp,4segsRFP<P=P;H04P:19481B5;#0PFf6RGf7RHP=C7[[XDE%S:RI,951B<I#0g01l<W0W9P:19H81BG;#0PFf8RIf9RJP=C7[[1R=;,9I1R<=,BH#0PFPJf:RK1R5<C7[[[^VEP8g01S5g017Af<RL/98f;RM/B;#0PFf=RNf>ROP=C7[[P5P<P=P;C;,9NP4P5P<P=C;,BL#0g01L7RP#<RQ/14%<QRR#<RS#<#<#<#<#<RT,14'3PNPNPGP4C:'3RUP:P7P811Q;11;T'3RVfARWPWP=P;C:'3n01100000130101102104X7:=X:<RX;Q8%0U%0X'4P011QG11GT'3POPOPHPGC:'3#0P:P7P8fBRXPXP=P;C:,3Vn01100000130101102104X7:=X:5#0PFf@RUPWPIPHPGP4C;C7P811QI11IT'3PUPUPJPIC:'3#0P:P7P8fERJPJP=P;C:,3Vn01100000130101102104X7:=X:H#011QK11KT'3RVPXPXPMPKC:RY;Q;%0V%0Y'4P011QM11MT'3#0fCRYPYPLPMC:#0PFPJfFRVPNPLPMPKC;C7P811QN11NT'3#0PVPVf?RZPOC:#011QZR[11ZTR\;Q;%0[%0\'4P011QU#011UT#0PFfJR\fKR[PXPWPUPZC;C7P811QX#011YT#0P011;8#016=;[RY16;811=;#0RX[16<=\X1{;8P;n2001000000120000000X6?XE?RXPY^6?^E?RYP8PQPJP=O316QJPXPYP8fGRYPTP<O316YTP0fHRX/6TfRRJfIRZ%2X3L19JV'4PFPJfSR]P\PZPXPYC;C7fD16\TfURYfLRX%2[3L19YZ'4P0fVR0fMRZ%2X3L190\PFP0fWR\fNR^PZPXP[C;C7P8fXR[fORX%2^3LfYR_/9Zg00GCR`/58RafQRb#2,>8'4f[Rcf\Rd/M]/C;#D5GF%\CRC58D#?[^C>PFP_fZReP^C7PFPeP_P[PbfPRfP0P;PKPIP7P9PFPePcP7g02D9Rc#PP8%ScRg1kJb=Hcgn0100000020000C[XT7AjF_e,icP[P[PbPfC:PWEhPFP_PeAg[bfC[eN;0;PFP_1ZebPfH0:#0%2J,>8,4aPFPdf]RJfTRW'ZRcP]%Y;RgP=209g]1N`;Rh%2]Ri'>PgPhP8XF>1N`8XF>P;P;%=;I08P]Pi%=iRhJ0716]T%dARA,5iRjP]PiPhPTPA%=ARhEIPMCEPj16QW%d6Rj%2WRM'5RiPQPj%=jR]PWPM%=MEIPOCEPi16YTRi%2YRO/5ARWPYPO%=OPTPAPhEIROPKCEPW%c0%20RK,5`203`41>`41N`4Rk=8>4'4154`A8>k`'4'b1N`GP>p-0Rkg00H<Rl1O>SRS1O>R1O>Q1O>P5J>RP5J>5J>g02E:RR'aAJ>SP/aR%SlRR5Hl3H%PlRlP>1W>=P;1W><H00%~>RP%|>RSPSP3P2P2P11VS4P>1T>6R3g01:aRm%z6,T>R6C@,AS5KS1VSGP>P3Pm1w>`RmC@,AS5KSFv%\2R2PSP>Pmg01]>RGP6C@,ASP>P6g00JGR61T>@R@C@,AS5KSP2P>P3P6P@C@,ASCUCU1uS1R1P8P=1]791t8=#0dAx>`;CyR9b<b>b?X4>X@>XA>X3kW=A8>8=,4<A8>8`,45'b15`<1><='41>=<[[^4>^@>^A>^3k^=kP815I`1>`IPI%2eR5P;P=PHO7b;bZbJbBb:b2b2CsFr1_Bc%2g'C#D9GFd=8DC#?P>f^Rd/ZY,_B%Y<#2RB,C8#D9GFd=8DC#?XG>P81MdYRgPdPYPMP4CqE`%Y=#2,Cg#D9GFJ=8DC#?P>PBf_RBf`/M\/C8#D5GF=8DC#?XG>P8P<PiPWPOPNCEPW16Q015jKRWPQPjP]P0PK%=KEIPUCEPW16\T%2\RW/5ARUP\PW%=WPTPAPhEIPLCEPU%c[%2[,5`PRPl1W>;PPPSP>PmPGP3C@,ASR31VS<5KSP2P3CUP1P9b<b>b?X4>X3k14a;15`;[^4>^3kP81>I5PIPHO3b;bBb:b2b2,}<E`1MB0/C<#D9GFd=8DC#?P8b5b5b5WMXC>bQPZP8PVO2CpPFP_PePbPfPXP^C;C7eWKWLP;P8O2n2001000000121000000W0WOP;P8O2n2001000000121000000b1b0b8b0W1W8P;P8O2n2001000000121000000b1WIW1P;P8O2n2001000000121000000b1W2W1P;P8O2n2001000000121000000b0W0W9WPXWEWXXY?WRP=P;P8O3n01100000131103105104XS:P;I01WNWDWUW6WHo"). Qed.

(* [comment removed for export] *)
Definition kx_log_in_b (kn : list kentry) (wins : list (saddr * expr)) (log : list sentry) : bool :=
  forallb (fun s => match s with
                    | SE a w _ => Nat.leb w 8 &&
                        existsb (fun c => zf_covers kn (a_base a) (a_off a) w (a_base (fst c)) (a_off (fst c)) (snd c)) wins
                    end) log.

Definition win_ivl (E : env) (c : saddr * expr) : ivl := (estart E (fst c), estart E (fst c) + elenZ E (snd c)).

Lemma kx_log_in_ok : forall E M kn wins log,
  know_ok segs E M kn -> kx_log_in_b kn wins log = true -> log_inside E log (map (win_ivl E) wins).
Proof.
ltac2:(KReplay.run1 (kr_t_KXPost ()) ["LogChecks"] "p'0h01ch13Hinh21Hh32Hch41xi001xh52H1h61si011sh72C1h82C2h91lh:1Ah;2Hwh<4__x1h=4__x2h>4__x3h?4__x4h@2c'hA1fhB3loghC1mhD1nhE4winshF1EhG2H2hH3HknhI2IHhJ3IHwhK1MhL7__arithhM4__ffhN8__varmaphO5__withP1ai021ahQ2a0hR2abhS2akhT2cbhU2ckhV4cstrhW1ei031ehX2knhY3lenhZ4resth[1vh\1wi041wh]2wsi056a_basei065a_offi076e_addri085e_vali097e_widthi0:2hii0;1ii0<2loi0=1pp&0p;1p;2p;4p;3p;7p;=p;6p;5p;8g000ij1LTg001Nj1eTg001lj1^Tg01]ej1jTg00<@j1MTg02EfR0k206Tg01^Gk403Tg02FFj3KTg02GDj3@Tg00;`j1WTg01`Fj3VTg01GJj1BTg01nNj2=Tg01LVj10Tg01NQj11Tg000MR1j3:Tg01nnj2JTg02H@j7NTg01aEj3YTg01aaj3\Tg00OTj2TTg020Mj2mTg01Tlj18Tg02I@j33Tg02IWR2j2QTg02J1j3iTg01OMj24Tg02JTl=hTg00:]j25Tg01YZj2CTg00U6j2;Tg00GaR3j2HTg01MSj27Tg02K[j1Uj2fTg01iDj3ZTg005dj3OTg01idR4j2dTg01V3k105Tg00\Sj2bTg00<`k104Tg00]1j4[Tg00=>k102Tg00=\k101Tg00]Oj2STg008?j1~Tg00_3j3aTg00>jj4`Tg01VXj1|Tg01W]j7{Tg00@9j2wTg007Hj2vTg00@[j2uTg00AGj3tTg00Afj4sTg02LUj3rTg00CAj6xTg02Loj3yTg01gej6qj5zTg01gJj4pTg02MIj4RTg0000j3oTg02Mej3}Tg02NBj3PTg02O7j4nTg00?Uk700Tg01[<j8lTg00KNR5f0R6g00KnR73Op=2f2R8g02OWR9f1R:#UP6CRp=Gg01j>R;?Z:6p=Ig01S5R<g017AR=;o6p=EA}<=6p=Ff6R>f5R?#0f4R@#1f3RAP8P:P6FNp=<AO567,H:p=A178:=PA6p=kP?P9%U@PACR178:%863Pp=?P>P?P@PAP8P:P6FN=O57p=DP<P=P:P6Cnp=914:6,78p=61;8:/56p=>P@P9PAP8CR?P:6p=gP@P9%UAP8CR?P:6p=X1;:6,58p=cP:g00HhR9g00IGRBPBg00IgRCP6g00JnK00p=_PAP9PBPBPCP8P:P6Glp=]g01\Bg00F^RD#LRE#LRF#LRG#L#L#L#e#^%eG#^#j[g01k=#M206<=RG#MRH%M;RIp,4segsRJP@PAP8H03P;AK@A6#2f7RKAGGK@7@:[XBI%W;9KA8#2g01l<W2P;AK>?6#2f9RLAGGL>7@:[1I8:9KK>#2f:RM1IA8AGGMK3@[[^9IP6g018>RNf;RO?KM6#2f>RPAGGPO7@:[f<RQAV@A8/I:7KO#2g01L7#B#B#B#B#B#B#B#BRR,=@PPP>P>P?%E6RS#0RT%1SRS%F6RUF<X0G=:GQ'JRVP;P5P61=:RRWfBRX%0ARY%1ARZP8PTPSPUFNX0Gf@R[5:G'Jn01101000130102104108X6;=Y;8R\;\6%2V/A\P31=?Rf?R\PKPKP>PTPSPUF<X0Gf=RV5:G'J#2P;P5P6fCR]PYPZP8PTPSPUFNX0GfAR^5:G,JWn01101000130102104108X6;=Y;A#2AVK>?/I@AGG^P5@^P61=KRP^PLPLf8R_PTPSPUF<X0G=:G\'J#2P;P5P6fFR`PYPZP8PTPSPUFNX0GfDRZ5:G,JWn01101000130102104108X6;=Y;>#21=LRRWP]POPOPMPTPSPUF<X0G=:G^RY;\:%2W/AYP31=MR#2PZPQPQPOPTPSPUF<X0G=:GX#2AVQOM/ILAGG`]5@`P61=QR#2fGRYP\P\PPPTPSPUF<X0GfERW5:G#2P31=:6#21T8:[Ra1T:61=8:#2Rb[1TA8\b1m:6P:n2001000000120000000XCNXDNPa^CN^DNP6P\PRP8O31T\RfKRRfHRN5GGRaPRP^%8[CkA@RPaP1p4p710R1P5\6Rb%M:RcP3A:8:6#2A3@68PAP6O1Rd'AX4A,QA[ReA3A6:P8P6O1'AX48,Q8A:A8:#2Rf[A3?6AP@P6O1'AX4@,Q@\fAi8:6P:n2001000000120000000W9WAW:Pe^9c^Ab^:1P6PGPRP]P]PXPTPSPUF<R1X0GfIRbPAO4fJRc93G6/A1X4G,QGP2PGA3G6RfLR2PZPZP]PTPSPUF<'AX4GPGfNR1PRP1PZP]E?P6fMRe93G6P1P`P`PWPTPSPUF<'AP3A3G:1fORU%0Y%1YP`%E:RS#0RT%1SRS%F:RfFDPGfRRgPUPgPNPYE?P6fPRU93GAPg%0c%1cPb%E@Rb#0%1b%F@FDP0P<P=fSRb93G6fURc%0e%1eP2PTPSPfFDPGfXRfPcPfP1PeE?]3]1P?P<19:6fWRe53GfYR1fQRS#0%1SPU198:RU#ERT#0%1T%FUFDPGf\RUP1PUPgPSE?]3]1^W=P6g00F@RS148:Rg/96fZRT53GPUfTR2#0%12Pb14A8Rb/9:Rh#ERi#0%1i%FhFDPJf_RJf^Rhf]Ri%0cRj%1cRkP2P@PAP8PTPZP6M=hA6J@ARlA6JjkRk'5%821CJ8,;l5>k'HP3f`R3?6?@RkfVRl#0%1l563R2'5%8c1C3A,;k5>2PGfaR2PhP2PePlE?P6fbRl14K>Re'7%0f%1f56l'5fcR2%01%1136%8f14_KRf,721C2>';3>P<P2%06%16PT14MLR1#0%11P_FDffRh14OMRk'7%0:%1:56h'5fgR3%08%1836%8U14QORU,731C3M';3>PGfhRMfePMPAPiE?]8]7]3PTPh14:6RT#0%1TPi14VQRQ#0%1QPOFDfiRO?6PV%0g%1g56O'5fjRg%0b%1b36%8JA6g\P1CgV';3>PG14^[/9\=3G6PGfmRg#URJP:A6g>?Rg%8lRlDg]1XEH14[\/9P%WGR>53Gg02PIPGPJP>PgPlDgP6n010000000W114X^/9[=3G6PGfnRlP:PlPeP2E?]114]X/9^AZG8:53GP414Z]/9XRX9OGAA3GX8P0PSPSp-0RXfp/f@frR4/7kRk,5:%83R3=>k6'HPGP4P?PkP3DX'dn200110;00012010<10:P614WZ/9]R]9OG@PG14`W/9ZRZP0PSPSPX1f46ftR4/7QRQ,5:%8ORO=>Q6'HPGP4PKPQPODX'dn200110;00012010<10:X@GfqRO%EZ'7RQ17O1R1'5%8hR4,;1RX%FZ,CO7cQ'HRQPGPOP@P1P4DXRZ&05hg00GCRh/54g00H<R4#W%M4PSPS1bS@P8&04SC[P:1bSAC[&02S&01SR4PS1SSERE%~D,SS5aSg01]>R01SSDRD1SSF5aSC`,_4RF%|BRWP4PSPDP0PEC`,_4REPWP4P9PBPBPCPEPFF{C]C]1w4CP6P81v571u68#2dAtSh:CsbMbNbOX<SX=SX>SX?S1;6A9>:815:8158A1;8?9>A@'H[[^<S^=S^>S^?SP6fsR@/C`%8M17@UA6@NYP_PLO6bLbVPQePQe3rP?P6ExW2P6O1A3G]A%E?,7OR]/51%F?,CO9cX]'H?yZdW1P6O1n200100000021100010000PGfoRZAZGA8PZPffdE?eW1WJX]HX@GPMPVEqW8W7W3XSSXR=P:P6O2n01101000121105106P?P:P6O3W8W7P:P6O2n2001000000121000000b2W3W1XY=WUXT=P:P6O2n01101000121105106X6<P:P6O2n200110=000121101103P:P6O2W3W1P:P6O2n2001000000121000000W2X0GP:P6O2n2001000000121100000b5b2PVPKO1CpAV^[\/IP=@Raeb;b2W5W;P:P6O2n2001000000121000000b5WGW5P:P6O2n2001000000121000000b2W2WIXZIX[=W\XP<P8P:P6O3n01101000131107109108XQ;P:DzWHWBWEWXWKWFo"). Qed.

Lemma log_inside_mono : forall E log W1 W2, log_inside E log W1 -> (forall a n, inside W1 a n -> inside W2 a n) ->
  log_inside E log W2.
Proof.
ltac2:(KReplay.run1 (kr_t_KXPost ()) ["LogChecks"] "p'0h01ah11nh21Hh32HWh43logh51Eh62H1h72H2h82IHh92W1h:2W2h;2a0h<1lh=4resth>1vh?1wi006e_addri015e_vali027e_widthi031sp;1p;3p;2p;4p;5g00<@j15Tg02GDj31Tg02NBj30Tg00;`j17Tg01iDj34Tg01`Fj36Tg01MSj22Tg01Tlj13Tg00GaR0j2:Tg01gJj49Tg01gej58Tg01\Bg01j>R1#5R2g02OW#5R3P1f4R4f0R5f2R631g00F@R7f5R8f1R9;05A0869[^17]0f6R:f3R;716[[X42%71=1;9A0495A0469[^17^07g01l<W3W2P1A1:54f7R<?095A0<69[^17^07f8R=?168[[A4169=1<8A0=95A0=69[^17^07f9R>A414;;1:[[[^<2P5g01S5g018>g017Af;R??15>f<R@?095A0@69[^17^07f=RAf:RB716[[A64;6=419=1@BA0A95A0A69[^17^07P0f>R0/2:%3850@A10;@f?R7/2<%3:50@A174@':P9f@/2=%3<500fA?1:7fBR=/2BRB%3>R>507A1=<7P4PBP>P9O3P:P5P4O2C9W7W6P9P5O2n2001000000120000000A6:84=41;=10?eW3W2W8X=2W>W?W0P6P9P5O3n01103000130100102101X;1P6D8X:3W9W4W5o"). Qed.

End LogChecks.

(* [comment removed for export] *)
Ltac kx_wins_reify WS l :=
  lazymatch WS with
  | nil => constr:(@nil (saddr * expr))
  | cons (?a, ?n) ?r => let x := kx_rz a l in let y := kx_rz n l in let t := kx_wins_reify r l in
                         constr:(cons (zsa x, zle y) t)
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma kx_mul_m1 : forall x, -1 * x = - x.
Proof.
ltac2:(KReplay.run1 (kr_t_KXPost ()) [] "h04__x1h17__arithh24__ffh38__varmaph45__with51xp;1p;2p;3p;4p;7g00;`j1CTg00<@j1BTg00\Sj22Tg00=>j11Tg00=\j1ATg00^2j1:Tg00>Gj23Tg00]Oj24Tg00^Pj35Tg02Pfj26Tg00>jj47Tg00?Uj78Tg00@9j29Tg007Hj2@Tg00@[j2;Tg005dj30Tg00AGj3<Tg00Afj4=Tg007bj2>Tg02QIj1?Tg00F@R0g00H<R1#C%B1f1R1,20%10%A0R2g00Hhg00IGR3P3g00IgR3P0g00F^R4#:R5,301404R4550g01:a1604C7g00JnF81923f0R3f2R2g00KNR4g00KnR6'@1;32=046dg00GC=<01C=b2b3b4X001>53%?3500^00P3P1O1b1W5o"). Qed.

(* [comment removed for export] *)
Ltac kx_norm_m1 :=
  repeat match goal with |- context [-1 * ?x] => rewrite (kx_mul_m1 x) end;
  repeat match goal with |- context [Z_to_bv 64 (?a + - ?b)] => change (Z_to_bv 64 (a + - b)) with (Z_to_bv 64 (a - b)) end.

(* [comment removed for export] *)
Ltac kx_abstract :=
  repeat match goal with
  | |- context [bv_unsigned (edenot ?E ?e)] =>
      let v := fresh "kv" in set (v := bv_unsigned (edenot E e)) in *; clearbody v
  | |- context [bv_unsigned (ev ?E ?j)] =>
      let v := fresh "kv" in set (v := bv_unsigned (ev E j)) in *; clearbody v
  end.

(* [comment removed for export] *)
Ltac kx_post_regs :=
  lazymatch goal with
  | |- context [MS (kx_regs ?E ?sr) ?F ?pc ?fc ?rv ?mm ?rom] =>
      let b := eval unfold E in E in
      lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
        rewrite (kx_regs_ez zv E (kE_atoms zv xs) sr);
        let na := eval vm_compute in (length zv) in
        cbv [kx_regs_z ez s_regs s_pc s_log]; change (length zv) with na; cbv [nth Nat.ltb Nat.leb];
        rewrite ?Z_to_bv_bv_unsigned; kx_norm_m1
      end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section ZConv.
Variable segs : list Segment.

Lemma kx_apart_z : forall zv xs m kn log za zn b c,
  know_ok segs (kE zv xs) m kn -> log_flat (kE zv xs) log ->
  zatoms_lt (length zv) za = true -> zatoms_lt (length zv) zn = true -> zsa za = SA b c ->
  0 <= zden zv za - c < 2^64 -> 0 <= zden zv za < 2^64 -> 0 <= zden zv zn < 2^64 ->
  kx_apart_b kn log (zsa za) (zle zn) = true ->
  log_apart (kE zv xs) log (zden zv za) (zden zv zn).
Proof.
ltac2:(KReplay.run1 (kr_t_KXPost ()) ["ZConv"] "h01Ah11zh22H1h32H2h42HBh52HFh62HKh72R1h82R2h92R3h:1Sh;1bh<1ch=2knh>3logh?1mh@2xshA2zahB2znhC2zvp;1p;2p;4p;3p;:p;9p;6p;5g00<@j16Tg000ij11Tg001Nj1>Tg001lj1<Tg01]ej1MTg02Qfj22Tg01^Gj4JTg01_Fj2ITg00N7j2BTg02RZj2@Tg02SXj14Tg01OMj2DTg005dj3CTg02TMj20Tg00USj2LTg00:]j2:Tg003lj1ATg004Jj2KTg00:Aj29Tg00Gaj2;Tg02UFj15Tg01hGj4HTg02V;l:GTg01MSj2=Tg01YZj28Tg01dEj43Tg02W9l9FTg00cXj6?Tg02X:j5ETg00KNf0R0g00Kn3Cp=7g00F@R1#6g00F^#1R2#1#1R3#1#1#1R4#>#<R5#6%>3#<#M\5g01k=#6g01j>#6g02Y3R5g017Ap,4segsR3f8R6f7R7'2f6f5R8CJf9R9/26/I8f:R:,B1/@8#7f;R;,B1/@8#7g01S5%47f4R<,D83Cg00GCR=f=R>/06/L8R?':%A2%A4'KR4,9?';f>R?/09R2,:=1924';f?R2/09R9,:=1994';P>f<R9%4;%5:CH#7P3fAR3f@R4'2R=P2P?P>%49R@%5;RAP6P7P0M:GP=P>1==@18=AC3P1fBRA/23R=%4>'=fCR@/2AR6P2P0%5>,86RBC3X11P010A>RCPAP3P>P;P:P7P8P<f3R<M9FE?P=P?PC%59,8=C3P1PBfDRB/2@P410B2P0C3X11P010@>RBP@PAP>P7P<DEE?P6P210@?PBC3P0b0b0b0W4W9W8W7W:W3W2W5W6X<1W;XB5WAW>W=W?W@WCo"). Qed.

(* [comment removed for export] *)
Lemma kx_erange_ok : forall E m kn e lo hi,
  know_ok segs E m kn -> erange kn e = Some (lo, hi) -> lo <= bv_unsigned (edenot E e) <= hi.
Proof.
ltac2:(KReplay.run1 (kr_t_KXPost ()) ["ZConv"] "h01Eh11Hh22HKh31eh42hih52knh62loh71mp;1p;4p;2p;3p;9g000ij10Tg001Nj13Tg001lj12Tg01]ej11Tg00<@j1;Tg01^Gj4:Tg02Efj29Tg02Ynj25Tg02O7j46Tg02Zkj27Tg005dj34Tg02[Ml98Tg01\Bg00F^#0#0#0R0#0#0#0#3#2%30#2#1[g01k=#;g017Ag00F@R0p,4segsR1f5R2f4R3f3R4C:1900R5#11534P0P0f2R6f1R7C6,7534P1f7f6P2P3P4P6P7f0M98W1W2X40W6W3W5W7W0o"). Qed.

(* [comment removed for export] *)
Lemma kx_erange_ev : forall E m kn j lo hi,
  know_ok segs E m kn -> erange kn (EVar j) = Some (lo, hi) -> lo <= bv_unsigned (ev E j) <= hi.
Proof.
ltac2:(KReplay.run1 (kr_t_KXPost ()) ["ZConv"] "h01Eh11Hh22HKh32hih41jh52knh62loh71mp;1p;4p;2p;3p;9g000ij10Tg001Nj14Tg001lj13Tg01]ej11Tg00<@j1<Tg01^Gj4;Tg02Efj2:Tg00RGj12Tg02Ynj26Tg02O7j47Tg02Zkj25Tg005dj38Tg02[Ml99Tg01\Bg00F^#0#0#0R0#0#0#0#4#3%40#3#1[g01k=#<g018>g00F@R0p,4segsR1f5R2f4R3f3R4C;1:00R5#1%24,63P0P0f2R6f1R7C7,5538P1f7f6P2%23P4P6P7f0M99W1W2X30W6W4W5W7W0o"). Qed.

End ZConv.

(* [comment removed for export] *)
Ltac kx_range e H :=
  lazymatch goal with HK : know_ok ?segs ?E ?m ?kn |- _ =>
    let r := eval vm_compute in (erange kn e) in
    lazymatch r with
    | Some (?lo, ?hi) =>
        let EQ := fresh "EQ" in
        assert (EQ : erange kn e = Some (lo, hi)) by (vm_compute; reflexivity);
        lazymatch e with
        | EVar ?j => pose proof (kx_erange_ev segs E m kn j lo hi HK EQ) as H
        | _ => pose proof (kx_erange_ok segs E m kn e lo hi HK EQ) as H
        end; clear EQ
    | None => fail 1 "kx_range: no interval for" e
    end
  end.

Lemma kx_vals_nth_ev : forall segs m ws reads i a n sx E,
  reads_scoped (length ws) reads = true -> nth_error reads i = Some (a, n, sx) ->
  E = kx_env ws (kx_vals segs m ws reads) ->
  ev E (length ws + i) = rdval segs m (adenot E a) n sx.
Proof.
ltac2:(KReplay.run1 (kr_t_KXPost ()) [] "h01Eh11Hh22H1h32H2h41ah51ih61mh71nh85readsh94segsh:2sxh;2wsp;1p;2p;3p;4p;5p;:p;6g00<@j12Tg000ij10Tg001Nj14Tg001lj18Tg01]ej19Tg02Efj26Tg00N7j25Tg02\Qj2=Tg005dj31Tg02]Rj3<Tg02O7j43Tg02Zkj2;Tg02^0j47Tg02^lj2:Tg02_gj2CTg00Q2j2BTg028aj2ATg02`>j5@Tg02a8l:?Tg00CAj6>Tg02b8#2g00F^#0#0#0R0#0#0#0#4#8R1%40#8#9[%21g01S5R0g018>R2'6R3g00KNR4'6R5#2g01\BR6f6R7,51f5R8'=g00Kn514%95A<578P3P4P0P2f4R3f3R9C3f2R:C3,;531f8R5f:R;f9R<P5f7R=C7':916:P6f;R>P;P<P5C7,:<f0R?151;/C5'Bf<P>1A?=P7P8D@511X06P>P;P<P5P=P7P8P3P:f1M:?P9P?E>W1W3W2W0X:4X72X40X52W8W;W6W9o"). Qed.

(* [comment removed for export] *)
Ltac kx_read_eq j H :=
  lazymatch goal with
  | XS := kx_vals ?segs ?m ?ws ?reads |- _ =>
      lazymatch goal with
      | EE := kx_env ws XS |- _ =>
        let na := eval vm_compute in (length ws) in
        let i := eval vm_compute in (j - na)%nat in
        let r := eval vm_compute in (nth_error reads i) in
        lazymatch r with
        | Some (?a, ?n, ?sx) =>
            pose proof (kx_vals_nth_ev segs m ws reads i a n sx EE ltac:(vm_compute; reflexivity) (eq_refl r) eq_refl) as H;
            change (length ws + i)%nat with j in H
        end
      end
  end.

(* [comment removed for export] *)
Ltac kx_post_mem_free :=
  lazymatch goal with
  | |- context [MS _ _ _ _ _ (mem_denot ?E ?m ?log) _] =>
    lazymatch goal with HK : know_ok ?segs E m ?kn, HLF : log_flat E log |- _ =>
      repeat match goal with
      | H : stk segs m ?lo ?hi |- _ => apply (kx_stk_log segs E m log lo hi) in H
      | H : wr_at segs m ?a ?n |- _ => apply (kx_wr_at_log segs E m log a n) in H
      | H : wmono segs ?m0 m |- _ => apply (kx_wmono_log segs E m0 m log) in H
      | H : mem_inv segs m |- _ =>
          let H' := fresh "MI" in
          pose proof (kx_mem_inv_log segs E m log H HLF (kx_log_wr_ok segs E m kn log HK HLF ltac:(vm_compute; reflexivity))) as H';
          clear H
      end
    end
  end.

(* [comment removed for export] *)
Section RdZ.
Variable segs : list Segment.

Lemma kx_rd_ez : forall zv xs m a n A bs,
  (1 <= n)%nat -> bytes_at segs m A bs ->
  0 <= ez zv (kE zv xs) (a_base a) < 2^64 /\ A <= ez zv (kE zv xs) (a_base a) + a_off a /\
  ez zv (kE zv xs) (a_base a) + a_off a + Z.of_nat n <= A + Z.of_nat (length bs) ->
  exists bs', rdn segs m (adenot (kE zv xs) a) n = Some bs'.
Proof.
ltac2:(KReplay.run1 (kr_t_KXPost ()) ["RdZ"] "h04__x1h14__x2h24__x3h31Hh43Hn0h57__arithh64__ffh78__varmaph85__with94__x4h:4__x5h;3bs'h<4cstrh=5cstr0h>1zh?1Ah@2HBhA2HnhB2L1hC2L2hD1RhE1ahF2bshG1mhH1nhI2xshJ2zvp;1p;2p;4p;3p;5p;6p;;p;<p;7p;8g00<@j1>Tg000ij19Tg001Nj1JTg001lj1ETg01]ej1QTg01GJj1]Tg00OTR0j2MTg02c7j4YTg02Qfj24Tg00:]R1j21Tg003lj1CTg004Jj2RTg00:Aj2BTg00GaR2j28Tg01NQj15Tg00U6j20Tg01TlR3j12Tg00N7j27Tg028aj2LTg02clj4KTg02Zkj2XTg005dj3ATg02IWj2HTg007Hj2@Tg01ULj4VTg01V3j1FTg00;`j1UTg00\Sj2<Tg00]1j4=Tg00=>j1TTg00=\j1STg00]Oj2:Tg008?j1DTg00_3j3?Tg00>jj4ITg01VXj1iTg00@9j2hTg00@[j2gTg00AGj3fTg00Afj4cTg01MSj2bTg01T3j2_Tg02daj5\Tg00CAj6NTg00<`j1^Tg02e]l;[Tg01LVj1`Tg00TAj3aTg01ZWl<ZTg00?Uj7dTg01[<j8eTf2R4f1R5f0R6#`3ap=3%26,05p=;1045/16p=61056,14p=Gg018>R7g00F@R8P0P3P1g01[`f5R1f4R3f3R0P4P5P6M<Zp=WP5g00HhR9g00IGR:P:g00IgR;P6g00JnFdp=PP0P9P:P:P;P4P5P6Gep=O%>8g00F^R9#9R<#9R=#9R>#9#9#9R?#J#ER@#>%J>#ER>#Q\@g01S5%>>R@g01L7#]RA/M4p,4segsRBP1P4P5CYg00GCRCf8RDf7RE,4D;31RF'1%C<%C?'RR?,BF'8%51,0FRF,10%2317>4,;056F'8'8P2f9RF14FDf6RG33RH,1C1BH?'8%5G,0HRH,13%2117>0,;356H'8%Q@RHPBPFf;RIf:RJ'4RK/LDPECK1X@6RL3AX;@,H@P6A3IKDRK,1C1BK?'8f<RK14KI;3F%5F'0R?,1E%2D17>G,;E56?'8P2f=R2142K;3J%5J'0R?,1D%2F17>E,;D56?PBP2f?R?f>RD'4RE/LKPICK=AHLX;@,H@P6A3?EK%5K5GJf@RE14E?;32%52'0%2K17>J,;I36PBP?fARB/4ER@PDP2PKPIPJPFP8A3B@D%5D'0RF1126X>81MA2%C9RI%22RL'1RHPAPI1@8IP2PL1@8LEWPJCVRJPH17>KRK#FRL%2KRK,1CRI%F?RA%2?,1CRGg00H<RM#URN%>MRMP81<84P51<80C=%T8RO%S8RPP81:89RQg01]>RR1:8<RS%D9,:8R95?8CI,PPRT%i:R:PTCO1hP;R;P6P4g00KNRTg00KnRU'@1g64=ATUdAf8C5CcRCb6b7b8X08X18X281054RU,16AG540[^08^18^28P6fBRT#5RVfERWfD,4W;3TRTPEP1O4b5b=b<b41b@DRWPBP@1_BEPDP1D\R@ENP8PF%2D102K566X>8PJPHPLPIPAPGPNPMP8P81<83P4%^8RMC=P5P81<81P0PMC=C=POPPP8A?8QS=?89PR1:8=%D<,:85?8CI,PPRPP:PPCOP;PCb6b7b8X08X18X28X98X:810651003764103196U0[^08^18^28^98^:8P617>?#2PE%2BPVPTP3O6b5b=b<b4PWP@ENM;[WCWBP5P6O2n2001000000121000000W3WDP5P6O2n2001000000121000000W3W@WAWFX?8XH7WEWGWIWJo"). Qed.
End RdZ.

(* [comment removed for export] *)
Ltac kx_rd_with_hook H hook :=
  lazymatch goal with
  | |- exists bs, rdn ?segs ?m (adenot ?E ?a) ?n = Some bs =>
      let b := eval unfold E in E in
      lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
        let HB := fresh "HB" in
        lazymatch type of H with
        | bytes_at _ _ _ _ => pose proof H as HB
        | u8arr _ _ _ _ => pose proof (proj1 H) as HB
        | rw_cells _ _ _ _ => pose proof (proj2 (proj1 H)) as HB
        | ro_cells _ _ _ _ => pose proof (proj2 H) as HB
        end;
        change E with (kE zv xs);
        apply (kx_rd_ez segs zv xs m a n _ _ ltac:(lia) HB);
        clear HB;
        let na := eval vm_compute in (length zv) in
        cbv [ez a_base a_off]; change (length zv) with na; cbv [nth Nat.ltb Nat.leb]; rewrite ?length_map; hook; kx_abstract; lia
      end
  end.
Ltac kx_rd_with H := kx_rd_with_hook H idtac.
Ltac kx_rd_hook hook :=
  first [ match goal with H : bytes_at _ _ _ _ |- _ => kx_rd_with_hook H hook end
        | match goal with H : u8arr _ _ _ _ |- _ => kx_rd_with_hook H hook end
        | match goal with H : rw_cells _ _ _ _ |- _ => kx_rd_with_hook H hook end
        | match goal with H : ro_cells _ _ _ _ |- _ => kx_rd_with_hook H hook end ].
Ltac kx_rd := kx_rd_hook idtac.

(* [comment removed for export] *)
Section Keep.
Variable zv : list Z.
Variable E : env.
Hypothesis HA : forall j, (j < length zv)%nat -> ev E j = Z_to_bv 64 (nth j zv 0).

Definition kx_pick (x : word) (e e' : expr) : word := if expr_eqb e e' then x else Z_to_bv 64 (ez zv E e').

Lemma kx_pick_ok : forall x e e', x = edenot E e -> kx_pick x e e' = edenot E e'.
Proof.
ltac2:(KReplay.run1 (kr_t_KXPost ()) ["Keep"] "p'0h01Hh12e'h22Hxh31bi001bh41eh51xp;1p;2p;3p;6p;4g000ij11Tg001Nj1=Tg001lj18Tg00SDj22Tg005dj30Tg02f]j23Tg007Hj2;Tg00TAj35Tg002Oj24Tg02g\j37Tg00cXj66Tg01K?j49Tg016ej4:Tg02h_j3<Tg00F^#1#1#1#1#1#1#=R0#8R1g017AR2f2R3p,1ER4f1R5'2R65011335g00KNR7f0R8,;7f3R9/33=078P7f5R:f4R;'3=078P7P1P5f7p,2zvR<?54:,40n0100000020000124:501]0P513;9R=g00Kn507A7:;8A02:;P2f6f81248501X12P;P:P8E6b0W0g02iY907=P1124;A5<4;,40P<P4p,2HAP;C9C:W0n0110000020000P8O1b0b3A<935=016eW2X12W4W5o"). Qed.

Definition kx_regs_keep (xl : list word) (sr sr' : list expr) : bvmap 5 word :=
  mkRl (map (fun i => kx_pick (nth i xl w0) (nth (S i) sr (ELit 0)) (nth (S i) sr' (ELit 0))) (seq 0 31)).

Lemma kx_regs_keep_ok : forall xl sr sr', regs_ok E sr (mkRl xl) -> kx_regs E sr' = kx_regs_keep xl sr sr'.
Proof.
ltac2:(KReplay.run1 (kr_t_KXPost ()) ["Keep"] "h07__arithh14__ffh28__varmaph35__with41bh54__x1h61xh71yh83Hi0h94cstrh:2HRh;4__p1h<4__x2h=1ih>1zh?1Hh@2H0hA4__p2hB1nhC2z0hD1GhE2HihF3HnehG1mhH2srhI3sr'hJ2xlp%0p%1p&0p;1p;3p;2p;6p;4p;<p;8p;Op;7p;Bg000ij1@Tg001Nk107Tg001lk10RTg00<@j1iTg02j9j1nTg02k2k30[Tg01GJR0j15Tg00O<R1j2ZTg008?j1JTg01TlR2j1?Tg002Oj2QTg02l1j2vTg02lfj2\Tg02mcj2pTg00OTR3k204Tg00GaR4j2ATg003lj1>Tg00U6j2DTg00:]R5j2ETg02n:j6|Tg00:AR6j23Tg01ULj4qTg01V3j1dTg00;`k10FTg00\Sj2tTg00=>k10>Tg00=\k10=Tg00>Gj2hTg00]Oj2zTg01VXk109Tg00_3k306Tg00@9k20]Tg007Hj2FTg00@[k20\Tg005dj34k103Tg00AGk30ZTg00Afk40YTg02>_j4XTg02nck30XTg00cXk60WTg00USj2VTg02oak20UTg030Dk30TTg02;[k201Tg01idj2_Tg02<=j2bTg00^2k10QTg030ak20PTg031Bk30OTg02<fj3^Tg02=Oj2lTg01iDj3jTg00<`k10NTg00]1k40MTg00_Vk30LTg00SDj21k10BTg00CAj6KTg00M:k10KTg031kj2kTg022\j1STg032Hk20JTg006>j2yTg032ij3wTg01PKk20ITg033Lj1eTg01ZWl<LTg033jk30GTg034Sk60ETg004gk20DTg0357k30@Tg01RFk20?Tg035Zj3gTg036Gk20ATg036jj1uTg00Qkj3}j2xk10<j4PTg02:^R7j1fTg009dj8]Tg01Gik20:Tg01HUlO6Tg037ej4;Tg038bk20VTg02MIk40fTg01IGk20eTg039>k30dTg02Aal<rTg00>jj4cTg00?Uj7oTg01W]k70cTg01[<k80bTg02;>k20aTg03:=mB0_Tg02BFk60^Tg02>;k70`Tg02h_k305Tf3R8f2R9f1R:f0R;'134p=MP9P:P;g03:cS00CPp=2%J;#>p=Ng00F@R</F;p=Tg018>R=P=P<P<P0P2P2P8g03;HP9P:P;M<rp=mP=P<P3P2P5g01[`f5R3f4R0P8P9P:P;M<Lp>00P=P<P1P2P6g02CWR>P3P0P8P9P:P;M<Lp=`g00GCR?/E;p=GP<P:g01]>P;Ccp=OP:g00HhR@g00IGRAPAg00IgRBP;g00JnRCFop=C1h<;p=sP9P@PAPAPBP<P:g00JGRDP;CcPCFop=aP9P@PAPAPBP:P;K0cp=UP8P@PAPAPBP9P:P;L0bp=HA4=:;p=W20a?;p=IA4<:;p=BP=P=P=P<P<P<g03;lP2P2P2f6REg03<LP3P0P8P9P:P;NB0_p>0SP=P<P;P2P:P9P8P0P3PEf7RFf8RGM<Lp>02A4<;?p=RP:P@PAPAPBP;J0^p=~P<P:g01:aP;Ccp=YP9P@PAPAPBP:P;K0`p={g017ARHP9P:P;CPp=0g00KNRIg02iYS0174;p=[P=P<P<P<P2P2P3P0P8P9P:P;M<rp>0HP<P<P5P3P5P0P?P?P8P9P:P;M<Lp>0CP<P=P<P<P7P0P2P8g02BjP9P:P;M<rp>0;PEP3P0Q00CPPHP8P9P:CP<05;p=8P=P<P1P2P6P>P3P01F<8P9P:P;M<Lp=<P9P@PAPAPBP<1h<:PDP;CcPCFop==1Z08P9P:P;CXp=7PFPEP3P0B0589:P;EKp=9P=P<P1P2P6P>g01L7S02P?P8P9P:P;M<Lp>08PHP9P:P;CP,18p=:g00F^R>#@S03#@S04#@S05#@S06#@S07#@$07$0RR2#i%iHS08Q08p,1ER1%n980[:Q02#5RC#5RD#5R7#5R5#5RJ#5RK#5RL#5RM#5RN#5RO#5RP#5RQ#5RR#5RS#5RT#5RU#5RV#5RW#5RX#5RY#5RZ#5S09#5S0:#5S0;#5S0<#5S0=#5S0>#5S0?#5S0@#5S0A#5R[,Z;S0BP9Q03#JS0C$07R\%5:S0D#?'QR]O1P2%n3/v]P11\0]CMP2%nE%59R]#?,Q\R^'vP2P;P1%58R_#?,Q\,\ECMX42P;1p]C=22ER`204C]Ra204][Rb'A%>>Rc%?9Rd/DcRe'ERf%J>S0E#JS0F#JS0G#NRg,EeRh'APaPbPfPhPCPc%TcS0HP]Pe1D;cRhX6<S0IP9Pd%TdRfCmRbJ00P]PePbP[Pg%TgRbJ00E|1Z9[13dgReP9PdPfP[PgPbE`P:CqPe%d8%?8Re#Gg00H<Rf$0FRd%ifRa1t<:S0J&0><Ri&0=<Rj1h<?Rk1z<>Rl'O,CjRm&09ARnPj%sgRo9ajlS0KPn%scS0LQ0L:06<lRp'O,Cj1Opo,Cj5UjCHCH20]jBRqP;P9g00KnRr,FI20\;9=4IrdB0Z<?:H0YRrb1b2b3X5<%G;Rs13:gS0M1D9cRt,Ec1Etg'A[[^5<P;%?3RuP:P9O3b0b9b8CX:0XE]J0WP2P`P11\3^CM1p_CR^,W8R`1DecR]/Vc#IRv,Be&03=S0N&03<Rw%?:%?;S0O'B1W:;20U:;40TX7=X6=S0PP8Pe%TeRxP^Pv1V:;#IXG<XB<P_P]Q0IP8PePxCmPCPcQ0HK0SN9021Z8[13egR]P8PePxP[PgPbE`P9CqP]%d0%?0#G1Duc/VcRu-01?13?u%IuR]/Bu'A1Eu?%R]'A'_%?ER]/DcRu/Vc#IP<p-0Rx1b<7&0Q>-0P<1b<DR>60O<Q02,b<Re5^<R_5^<g02E:Rv'l1b<C=^<e9^<>/lv1l_v=jfdS0Q5jf5jfPaP<1t<9P:&0N<RfH0MS0RPiPj1~j0S0SQ03,z<RvQ0L:0L<pR_'Y,Cj5Uj1O_k,Cj1Yvk,Cj5Uj5{jPnPjPmPn1Ylv,CjCHCHPqPrb1b2b3X5<X<<W;1VhcRh,B:,A91Eh?%R:S0T'A'_%G:1B98[[^5<^<<^;xP;%?GRh/DcR_/Vc,3?P:PhP9P8O5b0bCb@b9b8CXP`P=%50R`/pCf9Rh922;%53S0U#?,Q\R>,\G,11S0V542XB=P:P0P;EKP2A220GP1%?`,Q\,\FCMP2Q0VP2P;P1%5ER`&0K?Re70hS0WCMX42P41k:;#[1B9:#SR4[1B:;R^#S1k9:#[[Ry1k89#[\420J:;P;n2001000000120000000X7<X6<Py^7<^6<P;%?`Ry,Q\R4,y\S0Xg01l<S0Y9w\?Rz,y\R{P<20I\yR|1B;{#SX><P<Py%R;#SX><%RyS0Z#S%RuR}#SQ0ZP<P<PwP;X6<R~Pw%e^X7<X6<PyPuP~P~Q0O#TX6=P`PuQ0IPEP]%T]S0ICmS0OJ0HR^P?P?1F<?S0[M<L80G}1ZE[13]gR}PEP]Q0IP[PgPbE`P3CqS0IP}%dFR]%?F#GREPdPaQ0JPiPjPmPnPjP@PAPAPB1Ypk,CjJ0ECHPqPrb1b2b3X5<1D:cRB#Rg02PI[\s^5<P;%?hRAP:O2b0b9b8CXQ07#>R@-0DyS07%GyS0Z13y@S0\'A%GuS0]13u@S0^'AQ0ZQ0\Q0]Q0^P~1E:;#eX7<X6<Q0[PyPuP^J0CP<P<P6P~P613:;#eX7<X6<PyPuP^P@P@%T@M<LE|Q0IP}P]PEPdPaQ0JPiPjPmPnPjQ0KPn1Okp,Cj%s@9ajp5UjCHCHPqPrb1b2b3X5<Q0M%Gt13t@'A[\s^5<P;PAP:P9O3b0b9b8CX:0@y@R@EK1B|{#SeQ0X20?\yR{EKO3b?Ag\>z#[eQ0Y20A\?d9w\?9g\>#[PIQ01P2PIPHP;Pe%5FRF#?,Q\#uf:R>;0en0100000020000,11P1A0F>eCMX4IPHP2&0B1RIPI%u4R>?0heQ0WP2\H/FIPHPHA}H>hA}H`hPePeQ08PH\HRI1xH>1xH`PhPhP=Q08PI[RI&0<HRsPsP>P`PI\=/FsP<P|%f;/WFX><RFP<PyPF%fyRF/W`%IuRs/BuQ0NPwQ0PPFPsP~%I;X6<PyPuP^I0;P`PuQ0ON902Q0IP}P]PE201?_13?_%I_RE/B_'A1E_?%RE'A'_1DAc#IP<Q0QPaQ0RPiPjQ0SQ0L:06<vRA,Yl,CjRl5Uj1OAk,Cj1~j35Uj5{jPnPj1Okv,CjPnPlCHCHPqPrb1b2b3X5<X<<X;xXAx1B;B,A91EB?/A8'_%G91D8c,B9[[^5<^<<^;x^AxP;Q0Tf;#?Rx/Dc,3?PxP:P9P8O6b0bCb@b9b8CXQ07P@EK%f|/W`eQ0XP{EK1W>`eG]Q08/FhG]1FHeG]G]Ag\4zP;EKbFP2Q0VP1Q0U?0GeCMeA223hP;EKb:b?b:b:WEX==Q0BP2A22:3P1Q0D?00eCM[^==P2A0C9eS0B,11S0D20:\2R\A0C8eS0U,11RhA0D8eS0V,11RGA078eS0X,11RzA058eS07,11R4A0J8eS0T,11RHA0K8eS0S,11R>A0L8eS0R,11R`A0M8eS0Q,11R{A0N8eS0I,11R|A0O8eS0O,11R@A0P8eS0P,11RxA0Q8eS0N,11R<A0R8eS0W,11RBA0S8eS01,11RlA0T8eS0Y,11RnA0U8eS0M,11RvA0V8eS0K,11RAA0W8eS0J,11S0^A0X8eS0],11S0\A0Y8eS0Z,11S0_A0Z8eS0`,11S0aQ09?08eS0b,11S0cQ0:?08eS0d,11S0eQ0;?08eS0f,11S0gQ0<?08eS0h,11S0iQ0=?08eS0j,11S0kQ0>?08eS0l,11S0mQ0??08eS0n,11S0oQ0@?08eS0p,11S0qQ0A?08eS0r,11S0sA0[8eS0t,11MO6REP;P2PCP3PDP0PeQ0VF8P2PDP3P7P0PeQ0XF8S0uP2P7P3P5P0PeQ07F8S0vP2P5P3PJP0PeQ0TF8S0wP2PJP3PKP0PeQ0SF8S0xP2PKP3PLP0PeQ0RF8S0yP2PLP3PMP0PeQ0QF8S0zP2PMP3PNP0PeQ0IF8S0{P2PNP3POP0PeQ0OF8S0|P2POP3PPP0PeQ0PF8S0}P2PPP3PQP0PeQ0NF8S0~P2PQP3PRP0PeQ0WF8S10P2PRP3PSP0PeQ01F8S11P2PSP3PTP0PeQ0YF8S12P2PTP3PUP0PeQ0MF8R_P2PUP3PVP0PeQ0KF8R]P2PVP3PWP0PeQ0JF8R}P2PWP3PXP0PeQ0]F8RuP2PXP3PYP0PeQ0ZF8R^P2PYP3PZP0PeQ0`F8RyP2PZP3Q09P0PeQ0bF8R~P2Q09P3Q0:P0PeQ0dF8RsP2Q0:P3Q0;P0PeQ0fF8RFP2Q0;P3Q0<P0PeQ0hF8RwP2Q0<P3Q0=P0PeQ0jF8RIP2Q0=P3Q0>P0PeQ0lF8RtP2Q0>P3Q0?P0PeQ0nF8RpP2Q0?P3Q0@P0PeQ0pF8RmP2Q0@P3Q0AP0PeQ0rF8R6P2Q0AP3P[P0PeQ0tF8R3MO634X42P2A0D9eS13,11S14PhP;Q0uQ0vQ0wQ0xQ0yQ0zQ0{Q0|Q0}Q0~Q10Q11Q12P_P]P}PuP^PyP~PsPFPwPIPtPpPmP6P3MO694\EX42P2A079eS0u,11S15PhPGP;Q0vQ0wQ0xQ0yQ0zQ0{Q0|Q0}Q0~Q10Q11Q12P_P]P}PuP^PyP~PsPFPwPIPtPpPmP6P3MO694\EX42P2A059eS0v,11S16PhPGPzP;Q0wQ0xQ0yQ0zQ0{Q0|Q0}Q0~Q10Q11Q12P_P]P}PuP^PyP~PsPFPwPIPtPpPmP6P3MO694\EX42P2A0J9eS0w,11S17PhPGPzP4P;Q0xQ0yQ0zQ0{Q0|Q0}Q0~Q10Q11Q12P_P]P}PuP^PyP~PsPFPwPIPtPpPmP6P3MO694\EX42P2A0K9eS0x,11S18PhPGPzP4PHP;Q0yQ0zQ0{Q0|Q0}Q0~Q10Q11Q12P_P]P}PuP^PyP~PsPFPwPIPtPpPmP6P3MO694\EX42P2A0L9eS0y,11S19PhPGPzP4PHP>P;Q0zQ0{Q0|Q0}Q0~Q10Q11Q12P_P]P}PuP^PyP~PsPFPwPIPtPpPmP6P3MO694\EX42P2A0M9eS0z,11S1:PhPGPzP4PHP>P`P;Q0{Q0|Q0}Q0~Q10Q11Q12P_P]P}PuP^PyP~PsPFPwPIPtPpPmP6P3MO694\EX42P2A0N9eS0{,11S1;PhPGPzP4PHP>P`P{P;Q0|Q0}Q0~Q10Q11Q12P_P]P}PuP^PyP~PsPFPwPIPtPpPmP6P3MO694\EX42P2A0O9eS0|,11S1<PhPGPzP4PHP>P`P{P|P;Q0}Q0~Q10Q11Q12P_P]P}PuP^PyP~PsPFPwPIPtPpPmP6P3MO694\EX42P2A0P9eS0},11S1=PhPGPzP4PHP>P`P{P|P@P;Q0~Q10Q11Q12P_P]P}PuP^PyP~PsPFPwPIPtPpPmP6P3MO694\EX42P2A0Q9eS0~,11S1>PhPGPzP4PHP>P`P{P|P@PxP;Q10Q11Q12P_P]P}PuP^PyP~PsPFPwPIPtPpPmP6P3MO694\EX42P2A0R9eS10,11S1?PhPGPzP4PHP>P`P{P|P@PxP<P;Q11Q12P_P]P}PuP^PyP~PsPFPwPIPtPpPmP6P3MO694\EX42P2A0S9eS11,11S1@PhPGPzP4PHP>P`P{P|P@PxP<PBP;Q12P_P]P}PuP^PyP~PsPFPwPIPtPpPmP6P3MO694\EX42P2A0T9eS12,11S1APhPGPzP4PHP>P`P{P|P@PxP<PBPlP;P_P]P}PuP^PyP~PsPFPwPIPtPpPmP6P3MO694\EX42P2A0U9eR_,11S1BPhPGPzP4PHP>P`P{P|P@PxP<PBPlPnP;P]P}PuP^PyP~PsPFPwPIPtPpPmP6P3MO694\EX42P2A0V9eR],11S1CPhPGPzP4PHP>P`P{P|P@PxP<PBPlPnPvP;P}PuP^PyP~PsPFPwPIPtPpPmP6P3MO694\EX42P2A0W9eR},11S1DPhPGPzP4PHP>P`P{P|P@PxP<PBPlPnPvPAP;PuP^PyP~PsPFPwPIPtPpPmP6P3MO694\EX42P2A0X9eRu,11S1EPhPGPzP4PHP>P`P{P|P@PxP<PBPlPnPvPAQ0^P;P^PyP~PsPFPwPIPtPpPmP6P3MO694\EX42P2A0Y9eR^,11S1FPhPGPzP4PHP>P`P{P|P@PxP<PBPlPnPvPAQ0^Q0\P;PyP~PsPFPwPIPtPpPmP6P3MO694\EX42P2A0Z9eRy,11S1GPhPGPzP4PHP>P`P{P|P@PxP<PBPlPnPvPAQ0^Q0\Q0_P;P~PsPFPwPIPtPpPmP6P3MO694\EX42P2Q09?09eR~,11S1HPhPGPzP4PHP>P`P{P|P@PxP<PBPlPnPvPAQ0^Q0\Q0_Q0aP;PsPFPwPIPtPpPmP6P3MO694\EX42P2Q0:?09eRs,11S1IPhPGPzP4PHP>P`P{P|P@PxP<PBPlPnPvPAQ0^Q0\Q0_Q0aQ0cP;PFPwPIPtPpPmP6P3MO694\EX42P2Q0;?09eRF,11S1JPhPGPzP4PHP>P`P{P|P@PxP<PBPlPnPvPAQ0^Q0\Q0_Q0aQ0cQ0eP;PwPIPtPpPmP6P3MO694\EX42P2Q0<?09eRw,11S1KPhPGPzP4PHP>P`P{P|P@PxP<PBPlPnPvPAQ0^Q0\Q0_Q0aQ0cQ0eQ0gP;PIPtPpPmP6P3MO694\EX42P2Q0=?09eRI,11S1LPhPGPzP4PHP>P`P{P|P@PxP<PBPlPnPvPAQ0^Q0\Q0_Q0aQ0cQ0eQ0gQ0iP;PtPpPmP6P3MO694\EX42P2Q0>?09eRt,11S1MPhPGPzP4PHP>P`P{P|P@PxP<PBPlPnPvPAQ0^Q0\Q0_Q0aQ0cQ0eQ0gQ0iQ0kP;PpPmP6P3MO694\EX42P2Q0??09eRp,11S1NPhPGPzP4PHP>P`P{P|P@PxP<PBPlPnPvPAQ0^Q0\Q0_Q0aQ0cQ0eQ0gQ0iQ0kQ0mP;PmP6P3MO694\EX42P2Q0@?09eRm,11S1OPhPGPzP4PHP>P`P{P|P@PxP<PBPlPnPvPAQ0^Q0\Q0_Q0aQ0cQ0eQ0gQ0iQ0kQ0mQ0oP;P6P3MO694\EX42P2Q0A?09eR6,11S1PPhPGPzP4PHP>P`P{P|P@PxP<PBPlPnPvPAQ0^Q0\Q0_Q0aQ0cQ0eQ0gQ0iQ0kQ0mQ0oQ0qP;P3MO694\EX42P2A0[9eR3,11S1QPhPGPzP4PHP>P`P{P|P@PxP<PBPlPnPvPAQ0^Q0\Q0_Q0aQ0cQ0eQ0gQ0iQ0kQ0mQ0oQ0qQ0sP;MO694\EX42Q0DQ14Q15Q16Q17Q18Q19Q1:Q1;Q1<Q1=Q1>Q1?Q1@Q1AQ1BQ1CQ1DQ1EQ1FQ1GQ1HQ1IQ1JQ1KQ1LQ1MQ1NQ1OQ1PQ1QMO6,F\Q0A=220REQ0tP3PEQ0tP3P;Q0AQ0AP[Q0G#@#>R3/3gREQ0AP3P3P[PgPbE<PdPaPfPiA=j3oPqPrb1b2b3PEP;b0D7O2C;G9Q0@=220REQ0rP6PEQ0rP6P;Q0@Q0@P[Q0F#@R6#NRE/3gR3Q0@PEPEP[PgPbE<PdPaPfPiA=jEoPqPrb1b2b3P3P;b0D7O2C;G9Q0?=220R3Q0pPmP3Q0pPmP;Q0?Q0?P[%@6#>Rm/3gR3Q0?PmPmP[PgPbE<PdPaPfPiA=jmoPqPrb1b2b3P3P;b0D7O2C;G9Q0>=220R3Q0nPpP3Q0nPpP;Q0>Q0>P[Q0E#@Rp#JR3#NRm/3gREQ0>PmPmP[PgPbE<PdPaPfPiA=jmoPqPrb1b2b3PEP;b0D7O2C;G9Q0==220REQ0lPtPEQ0lPtP;Q0=Q0=P[%@3#>Rt/3gREQ0=PtPtP[PgPbE<PdPaPfPiA=jtoPqPrb1b2b3PEP;b0D7O2C;G9Q0<=220REQ0jPIPEQ0jPIP;Q0<Q0<P[%@pRI#NRE/3gRtQ0<PEPEP[PgPbE<PdPaPfPiA=jEoPqPrb1b2b3PtP;b0D7O2C;G9Q0;=220RtQ0hPwPtQ0hPwP;Q0;Q0;P[%@I#>Rw/3gRtQ0;PwPwP[PgPbE<PdPaPfPiA=jwoPqPrb1b2b3PtP;b0D7O2C;G9Q0:=220RtQ0fPFPtQ0fPFP;Q0:Q0:P[Q0C#JRF#NRt/3gRwQ0:PtPtP[PgPbE<PdPaPfPiA=jtoPqPrb1b2b3PwP;b0D7O2C;G9Q09=220RwQ0dPsPwQ0dPsP;Q09Q09P[%@F#>Rs/3gRwQ09PsPsP[PgPbE<PdPaPfPiA=jsoPqPrb1b2b3PwP;b0D7O2C;G9A22Z0RwQ0bP~PwQ0bP~P;PZPZP[Q0C#@R~#NRw/3gRsPZPwPwP[PgPbE<PdPaPfPiA=jwoPqPrb1b2b3PsP;b0D7O2C;G9A22Y0RsQ0`PyPsQ0`PyP;PYPYP[%@~#>Ry/3gRsPYPyPyP[PgPbE<PdPaPfPiA=jyoPqPrb1b2b3PsP;b0D7O2C;G9A22X0RsQ0ZP^PsQ0ZP^P;PXPXP[Q04#JR^#NRs/3gRyPXPsPsP[PgPbE<PdPaPfPiA=jsoPqPrb1b2b3PyP;b0D7O2C;G9A22W0RyQ0]PuPyQ0]PuP;PWPWP[%@^#>Ru/3gRyPWPuPuP[PgPbE<PdPaPfPiA=juoPqPrb1b2b3PyP;b0D7O2C;G9A22V0RyQ0JP}PyQ0JP}P;PVPVP[Q05#NR}/3gRyPVP}P}P[PgPbE<PdPaPfPiA=j}oPqPrb1b2b3PyP;b0D7O2C;G9A22U0RyQ0KP]PyQ0KP]P;PUPUP[Q06#>R]/3gRyPUP]P]P[PgPbE<PdPaPfPiA=j]oPqPrb1b2b3PyP;b0D7O2C;G9A22T0RyQ0MP_PyQ0MP_P;PTPTP[Q0G#>R_/3gRyPTP_P_P[PgPbE<PdPaPfPiA=j_oPqPrb1b2b3PyP;b0D7O2C;G9A22S0RyQ0YQ12PyQ0YQ12P;PSPSP[%>6R6/3gRyPSP6P6P[PgPbE<PdPaPfPiA=j6oPqPrb1b2b3PyP;b0D7O2C;G9A22R0RyQ01Q11PyQ01Q11P;PRPRP[%>3R3/3gRyPRP3P3P[PgPbE<PdPaPfPiA=j3oPqPrb1b2b3PyP;b0D7O2C;G9A22Q0RyQ0WQ10PyQ0WQ10P;PQPQP[%>IRI/3gRyPQPIPIP[PgPbE<PdPaPfPiA=jIoPqPrb1b2b3PyP;b0D7O2C;G9A22P0RyQ0NQ0~PyQ0NQ0~P;PPPPP[%>FRF/3gRyPPPFPFP[PgPbE<PdPaPfPiA=jFoPqPrb1b2b3PyP;b0D7O2C;G9A22O0RyQ0PQ0}PyQ0PQ0}P;POPOP[%>~R~/3gRyPOP~P~P[PgPbE<PdPaPfPiA=j~oPqPrb1b2b3PyP;b0D7O2C;G9A22N0RyQ0OQ0|PyQ0OQ0|P;PNPNP[%>^R^/3gRyPNP^P^P[PgPbE<PdPaPfPiA=j^oPqPrb1b2b3PyP;b0D7O2C;G9A22M0RyQ0IQ0{PyQ0IQ0{P;PMPMP[Q05#>Ry/3gR^PMPyPyP[PgPbE<PdPaPfPiA=jyoPqPrb1b2b3P^P;b0D7O2C;G9A22L0R^Q0QQ0zP^Q0QQ0zP;PLPLP[Q0F#>R^/3gRyPLP^P^P[PgPbE<PdPaPfPiA=j^oPqPrb1b2b3PyP;b0D7O2C;G9A22K0RyQ0RQ0yPyQ0RQ0yP;PKPKP[%>pRp/3gRyPKPpPpP[PgPbE<PdPaPfPiA=jpoPqPrb1b2b3PyP;b0D7O2C;G9A22J0RyQ0SQ0xPyQ0SQ0xP;PJPJP[Q0C#>Ry/3gRpPJPyPyP[PgPbE<PdPaPfPiA=jyoPqPrb1b2b3PpP;b0D7O2C;G9A2250RpQ0TQ0wPpQ0TQ0wP;P5P5P[Q04#>Rp/3gRyP5PpPpP[PgPbE<PdPaPfPiA=jpoPqPrb1b2b3PyP;b0D7O2C;G9A2270RyQ07Q0vPyQ07Q0vP;P7P7P[Q0E#>Ry/3gRpP7PyPyP[PgPbE<PdPaPfPiA=jyoPqPrb1b2b3PpP;b0D7O2C;G9A22D0RpQ0XQ0uPpQ0XQ0uP;PDPDP[Q03#>Rp/3gRyPDPpPpP[PgPbE<PdPaPfPiA=jpoPqPrb1b2b3PyP;b0D7O2C;G9A22C0RyQ0VQ13PyQ0VQ13P;PCPCP[13cgRyPCPcQ0HP[PgPbE`PdPaPfPiQ0L=ajoPqPrb1b2b3PyP;b0D7O2C;G9P2Q02P0Q00CPRyQ0UQ0BPyQ0UQ0BP;Q02Q02P[13?gR?Q0[P[PgPbH08PdPaPfPiAajkoPqPrb1b2b3P?P;b0D7O2C;G9bDP1PCP:PeC:P1PDP:PeC:P1P7P:PeC:P1P5P:PeC:P1PJP:PeC:P1PKP:PeC:P1PLP:PeC:P1PMP:PeC:P1PNP:PeC:P1POP:PeC:P1PPP:PeC:P1PQP:PeC:P1PRP:PeC:P1PSP:PeC:P1PTP:PeC:P1PUP:PeC:P1PVP:PeC:P1PWP:PeC:P1PXP:PeC:P1PYP:PeC:P1PZP:PeC:P1Q09P:PeC:P1Q0:P:PeC:P1Q0;P:PeC:P1Q0<P:PeC:P1Q0=P:PeC:P1Q0>P:PeC:P1Q0?P:PeC:P1Q0@P:PeC:P1Q0AP:PeC:P1P[P:PeC:MO6P2Q02P=P2P2P;P0%5;R;P8PeA0;9eF8X==Q0200V[H0fR[Q00CPA22C[A22D[A227[A225[A22J[A22K[A22L[A22M[A22N[A22O[A22P[A22Q[A22R[A22S[A22T[A22U[A22V[A22W[A22X[A22Y[A22Z[Q09=22[Q0:=22[Q0;=22[Q0<=22[Q0==22[Q0>=22[Q0?=22[Q0@=22[Q0A=22[MO654\e20e1:B0d89:54\eW:WIWHWJo"). Qed.
End Keep.

(* [comment removed for export] *)
Ltac kx_post_regs_keep :=
  lazymatch goal with
  | KXR : regs_ok ?E ?sr (mkRl ?xl) |- context [MS (kx_regs ?E ?sr') ?F ?pc ?fc ?rv ?mm ?rom] =>
      let b := eval unfold E in E in
      lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
        rewrite (kx_regs_keep_ok zv E (kE_atoms zv xs) xl sr sr' KXR);
        let na := eval vm_compute in (length zv) in
        let sre := eval vm_compute in sr in
        change sr with sre;
        cbv [kx_regs_keep seq map s_regs s_pc s_log]; cbn [nth];
        cbv [kx_pick expr_eqb aluop_eqb mulop_eqb Nat.eqb Z.eqb Pos.eqb andb Bool.eqb ez];
        change (length zv) with na; cbv [nth Nat.ltb Nat.leb mkRl];
        rewrite ?Z_to_bv_bv_unsigned; kx_norm_m1
      end
  end.

(* [comment removed for export] *)
Section FrameZ.
Variable segs : list Segment.

(* [comment removed for export] *)
Lemma estart_ez_kE : forall zv xs a, 0 <= ez zv (kE zv xs) (a_base a) < 2^64 ->
  estart (kE zv xs) a = ez zv (kE zv xs) (a_base a) + a_off a.
Proof.
ltac2:(KReplay.run1 (kr_t_KXPost ()) ["FrameZ"] "h01Rh11ah22xsh32zvp;1p;2p;3p;5g00<@j11Tg000ij10Tg001Nj16Tg001lj14Tg02Qfj23Tg01LVj1<Tg00TAj3;Tg00:]j25Tg003lj12Tg004Jj27Tg00:Aj28Tg00Gaj29Tg01T3j2:Tg02daj5=Tg00F@#1g00F^#0R0#0#0#0#0#0R1#6#4#1g01S5g00GCf2R2f1R3,32f0R4#<3;R5'5%20%21'7,85'9f3R513521:52P3P4D=W0W1W2W3o"). Qed.

Fixpoint log_apart_ez (zv : list Z) (E : env) (log : list sentry) (A n : Z) : Prop :=
  match log with
  | [] => True
  | SE a w _ :: rest =>
      (0 <= ez zv E (a_base a) < 2^64 /\
       (ez zv E (a_base a) + a_off a + Z.of_nat w <= A \/ A + n <= ez zv E (a_base a) + a_off a))
      /\ log_apart_ez zv E rest A n
  end.

Lemma log_apart_ez_ok : forall zv xs log A n, log_apart_ez zv (kE zv xs) log A n -> log_apart (kE zv xs) log A n.
Proof.
ltac2:(KReplay.run1 (kr_t_KXPost ()) ["FrameZ"] "p'0h01Hh12H0h23logh31Ah41Dh52IHh61Rh71ah82a0h91lh:1nh;4resth<1vh=1wh>2xsh?1zh@2zvi006e_addri015e_vali027e_widthi031sp;1p;2p;5p;4p;3p;6g00<@j1=Tg000ij1:Tg001Nj1ETg001lj1ATg02Qfj20Tg03=3j52Tg01dEj43Tg00;`j1DTg01iDj3<Tg01LVj17Tg00TAj36Tg00:]j28Tg003lj1?Tg004Jj2JTg00:Aj2;Tg00GaR0j21Tg01NQj19Tg00U6j25Tg01MSj2>Tg03>2j4ITg00CAj6HTg01gJj4CTg01`Fj3@Tg01gej5FTg01Tlj1BTg01idj2GTf5R1f4R2#B'5f3R3'8f2R4f1R5'5f0R6'8'Gp=4g00F@R7#=g00F^#:R8#:#:#:#:#:R9#E#A#=g01j>R:#=R;P:P11012R<P6P4P5D2f6R=/01P5P3P4C3[X2;g01;Hg01l<W0P21023%D:R>P5P6D2P<P>P4P5C3[eP:f7R>10>=P6P2P3D2f8R</0>R?P5P1P2C3[P<P?A<:45P1P2D2f9R?/0<A<:34P=P1C3[[^9;P6g01S5g018>g017Af<R@f;RA,0@P6P?P<D2f=RB/0@RCP5f:RDP?C3[g00GCRE%7296BCRF'8%?8%?9'JR9,;F'1%92,5FRFP3PDPDP?PFE4'1PBPCP5PDP?D2'1P0f>RF10FBR8%7136RG,8E1;G9'1%91,5GRGP2PAPAPDPGE4'1PFP8P4PAPDD2f?RG/0FRH/>=RIP1P@P@PAPIE4PHP3P@PAC3'1P6f@RH10HG%7>36RI,8E1;I9'1%9>,5IRIP=PBPBP@PIE4'1P0fAR0100H%7<36RI,8E1;I9'1%9<,5IRIP>PFPFPBPIE4fBRI10I0P=PGPFD2fCRF/0IR=/>DR<P?PHPHPGP<E4P=P>PHPGC3'1[P6%7D96F=R=,8E1;=9'1fDR=10=F%7A36%9A'5R9PDP0P0PHP9E4fER9109=P?PIP0D2fFR0/09RH/>BREP@PFPFPIPEE4PHPDPFPIC3P7%7B960H%9B'5P6PBP=P=PFP6E4X?7P5PEP0P9PBP4CIEHP?P6O1CCW0W4W6P5P6O2n2001000000120000000W1P5P6O2n2001000000121000000W1PBPCA@234=<:5PDP?D2P8A@123=<:4PAPDC3[eW5X;;W<W=W7P4P5P6O3n01103000131100102101X8:P4DFX:7X37W2W>W@o"). Qed.

Fixpoint log_inside_ez (zv : list Z) (E : env) (log : list sentry) (W : list ivl) : Prop :=
  match log with
  | [] => True
  | SE a w _ :: rest =>
      (0 <= ez zv E (a_base a) < 2^64 /\ inside W (ez zv E (a_base a) + a_off a) (Z.of_nat w))
      /\ log_inside_ez zv E rest W
  end.

Lemma log_inside_ez_ok : forall zv xs log W, log_inside_ez zv (kE zv xs) log W -> log_inside (kE zv xs) log W.
Proof.
ltac2:(KReplay.run1 (kr_t_KXPost ()) ["FrameZ"] "p'0h01Hh12H0h23logh31Dh42IHh51Rh61Wh71ah82a0h91lh:4resth;1vh<1wh=2xsh>1zh?2zvi006e_addri015e_vali027e_widthi031sp;1p;2p;4p;3p;6p;5g00<@j1=Tg000ij19Tg001Nj1ETg001lj1ATg02Qfj20Tg03?1j42Tg02GDj33Tg00;`j1DTg01iDj3<Tg01LVj16Tg00TAj35Tg00:]j2:Tg003lj1?Tg004Jj2JTg00:Aj2;Tg00GaR0j21Tg01NQj18Tg00U6j27Tg01MSj2>Tg03>2j4ITg00CAj6HTg01gJj4CTg01`Fj3@Tg01gej5FTg01Tlj1BTg02NBj3GTf2R1f1R2f0R3#B3Gp=4g00F@R4#=g00F^#9R5#9#9#9#9#9R6#E#A#=g01j>R7#=R8g02OW#=P7f4R9f3R:,09R;P3P2C2f5R</09?321[X28g01;Hg01l<W0P:10:1%D7R=P3C2A3;=2[eP7f6R=10=<P3P:C2f7R;/0=R>?329[P;P>A<712P9C2f8R>/0;A<7:1;3<[[^98P3g01S5g018>g017Af;R?f:R@,0?P3P>C2f<RA/0?RBf9RC732[g00GCRD%6995ABRE':%?5%?6'JR6,;E'1%89,7E=4C:'1PAPBP2PCC2'1P0f=RE10EAR5%6<35RF,:D1;F6'1%8<,7F=4@9'1PEP5P1P@C2f>RF/0ERG/>==4?<A3G:?'1P3f?RG10GF%6;35RH,:D1;H6'1%8;,7H=4A='1P0f@R0100G%6>35RH,:D1;H6'1%8>,7H=4E;fARH10H0P=PFC2fBRF/0HR=/>@=4GCA3=;G'1[P3%6@95F=R=,:D1;=6'1fCR=10=F%6?35%8?'7=40@fDR0100=PCPHC2fERH/00R?/>ER6=4FAA3?@FP4%6E95H?%8E'7A4=3EX>4P2P6PHP0PEP1CIEHPCP3O1CCW0W3W5P2P3O2n2001000000120000000W1P2P3O2n2001000000121000000W1PAPBA@9:1=<72PCC2A@<9:=<71=35@[eW4X:8W;W<W7P1P2P3O3n01103000131100102101X87P2DFW6W2W=W?o"). Qed.
End FrameZ.

(* [comment removed for export] *)
Ltac kx_log_z zv :=
  let na := eval vm_compute in (length zv) in
  cbn [log_apart_ez log_inside_ez inside]; cbv [ez a_base a_off]; change (length zv) with na; cbv [nth Nat.ltb Nat.leb];
  repeat (first [exact I | split]); try lia.

(* [comment removed for export] *)
Ltac kx_frame H :=
  lazymatch goal with
  | KXLF : log_flat ?E ?log, HK : know_ok ?segs ?E ?m ?kn |- context [MS _ _ _ _ _ (mem_denot ?E ?m ?log) _] =>
    let b := eval unfold E in E in
    lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
      lazymatch type of H with
      | bytes_at _ m ?A ?bs =>
          apply (kx_bytes_at_log segs E m log A bs) in H; [ | exact KXLF | change E with (kE zv xs); apply log_apart_ez_ok; kx_log_z zv ]
      | rw_cells _ m ?A ?cs =>
          apply (kx_rw_cells_log segs E m log A cs) in H; [ | exact KXLF | change E with (kE zv xs); apply log_apart_ez_ok; kx_log_z zv ]
      | ro_cells _ m ?A ?cs =>
          apply (kx_ro_cells_log segs E m log A cs) in H; [ | exact KXLF | change E with (kE zv xs); apply log_apart_ez_ok; kx_log_z zv ]
      end
    end
  end.

(* [comment removed for export] *)
Ltac kx_munch H :=
  lazymatch goal with
  | KXLF : log_flat ?E ?log, HK : know_ok ?segs ?E ?m ?kn |- context [MS _ _ _ _ _ (mem_denot ?E ?m ?log) _] =>
    let b := eval unfold E in E in
    lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
      lazymatch type of H with
      | munch ?W ?m0 m =>
          apply (kx_munch_log E W m0 m log) in H; [ | exact KXLF | change E with (kE zv xs); apply log_inside_ez_ok; kx_log_z zv ]
      end
    end
  end.

Ltac kx_munch_wins H WINS :=
  lazymatch goal with
  | KXLF : log_flat ?E ?log, HK : know_ok ?segs ?E ?m0' ?kn |- context [MS _ _ _ _ _ (mem_denot ?E ?m ?log) _] =>
    let b := eval unfold E in E in
    lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
      lazymatch type of H with
      | munch ?W ?m0 m =>
          let wz0 := kx_wins_reify WINS zv in
          let wz := eval vm_compute in wz0 in
          let LI := fresh "LI" in
          assert (LI : log_inside E log (map (win_ivl E) wz))
            by exact (kx_log_in_ok segs E m0' kn wz log HK ltac:(vm_compute; reflexivity));
          apply (kx_munch_log E W m0 m log) in H; [ | exact KXLF | apply (log_inside_mono E log _ W LI) ];
          [ clear LI
          | clear LI; intros ? ?; cbn [map inside win_ivl fst snd];
            let na := eval vm_compute in (length zv) in
            change E with (kE zv xs);
            repeat match goal with
            | |- context [estart (kE zv xs) ?a] =>
                rewrite (estart_ez_kE zv xs a);
                [ | cbv [ez a_base a_off]; change (length zv) with na; cbv [nth Nat.ltb Nat.leb]; lia ]
            end;
            rewrite ?elenZ_lit by lia;
            cbv [ez a_base a_off]; change (length zv) with na; cbv [nth Nat.ltb Nat.leb]; lia ]
      end
    end
  end.

(* [comment removed for export] *)
Lemma kx_srl_tl : forall E x s tl, edenot E s = Z_to_bv 64 (64 - tl) -> 1 <= tl <= 63 ->
  0 <= bv_unsigned (edenot E (EAlu ALU_SRL x s)) < 2 ^ tl.
Proof.
ltac2:(KReplay.run1 (kr_t_KXPost ()) [] "h04__x1h17__arithh24__ffh38__varmaph45__with54__p1h64__x2h71zh81Hh94__x3h:1bh;2H0h<2Hah=6__sat1h>6__sat2h?1ah@1nhA1DhB1EhC2H1hD2H2hE2H3hF2H4hG2HshH3HtlhI1PhJ1QhK1RhL6__sat0hM1shN2tlhO1xhP2zhp%0p&0p;1p;2p;3p;4p;6p;8p;5p;7g000ij14Tg001Nj1}Tg001lj1gTg00SDj29Tg003lj1LTg00USj28Tg002Oj2UTg005dj3ITg00:]j26Tg008?j1JTg00GaR0j2<Tg00ejj3[Tg006>j25Tg004Jj23j1~Tg00:Aj20Tg01Q1j1fTg03@1j2dTg00D_j3cTg0035k208Tg004gj27Tg006hj2OTg01PKj2BTg00;`j1wTg00<@j1uTg00\Sj2VTg00=>j1sTg00=\j1qTg00>Gj2GTg00]Oj2RTg00_Vj3eTg00@9j2kTg007Hj2NTg00@[j2jTg00AGj3iTg00Afj4hTg01VXk10DTg01W:k30CTg0357j3YTg00`9k20Bk402Tg00`ak30ATg00aEk20@Tg03@dk20?Tg022\k10>Tg005Gj2=Tg007bj2KTg00U6j2QTg00;9k20=Tg03AEk20<Tg03Alk20;Tg03BRk20:Tg03C8k207Tg00b6j2]Tg00^2k106Tg030ak201Tg01GJj1FTg02<=j2DTg031Bj3|Tg03D4j2zTg03D]j3yTg02=Oj2_Tg03EFj2xTg01iDj3^Tg00]1j4PTg034Sj6vTg00^Pj3WTg00_3j3ZTg009dj8tTg03F2k500Tg00cXj6\Tg00<`j1rTg03FUk503Tg03GAk404Tg03Gbk505Tg01gJj4aTg00BXj3pTg01RFj2bTg00EGk209Tg00CAj6TTg00>jj4STg00?Uj7XTg01W]j7oTg01[<j8nTg02<fj3mTg02BFj6lTf0R1#4#4#4#4p>0Eg00GCR2/61p=1g00F@R3f1R4;I1p=:P3P4g01:aP1CSp=MP4g00HhR5g00IGR6P6g00IgR7P1g00JnR8FXp=Hf2R9P5P6P6P7P3P4g01]>P1CSP8FXp=;P9P5P6P6P7P4P1Fop=@P9P5P6P6P7P3P4g00JGP1CSP8FXp=?f3R8P5P6P6P7P9P4P1Gnp=21041,<9p=>P3f4R:P8P9P4P1ETp=EAm341p=C%41#4p={%41#4#4#4#4#4#4#4p=AP4P5P6P6P7P1Elp=`g01\Bg017AR;g00F^R<#4R=#4R>$0ER?#}R@#gRA1984%L?RB/81RC,U@3I%L<RD/64%J<RE#J#J#J#J#LRF,64'<f5RGg00LNRH?[:8'9,5@RI#1%L=RJ/39RK,0IS00g03HIRI%g1RLP01541R0#1RM%f4,001594#11d41P4n2001000000120000000W:W@PM^:L^@IP1P@f6RIA[HG:'9O2b8PA18B9RL,U@RM19IGR0=cH1,5@13J8RN'0X:APA19G:RO008MRP15@1/0NX:A15@O15@MS01/7B'ORA,B@101NX731B@LRQ15@0RR171B'O,B@/0NX7313JBRN,7LRS18B8RT/:1X73RUPLPUg00H<RU#wRV%uURW1V34RX%s3RY%q3RZ1G3BR[1R3<R\5e3R]/M]'H1kZ7R^P1P9g00KNR_g00KnR`'N1j19=I_`dAi324ChR`b2b3b4X031:CC^03P1P8O1b1PSPVPWPXPYPZ1G3DR_=;Z\Ra1G3FRb9;Z\Rc5@Z&0D6Rd1G32Re=;Z]S021G3JRf>0C3@Rg9?Z]5@ZC2P^P`b2b3b4X0316D1Rh161FRi'<18B4Rj#1S03?>jN[^03P1P8P4O2b19YLNDE17SB20BJB102JRj%1B102NRk[Rl[%1JRmg01;HRnB0AJB4UW<%1NRo\n^<m18B:Rp00@N%1p18BIRq/7NRr#1\o[18BGRs00?NAI3N2Rt$0>1=qN,KN/Qr,:q[20=qNf7Rr,8BRu/7NRv#1?>vN\k20<uN10N2f8Rv,8BRw/7NRx,0N16x2'<[20;wNf9Rx,8BRy/=N=I32\t20:yNf:Rz,8BR{/7N/:{\tg01l<207{NR{eP{P:g01;dR{1]2N'NPkeO1f;Rk,8B/7NR|#1R}?>|NP4PnPzP1P4O2X?mPo^?mPk1]2J,N{PjeO1Plp-0Rl&06<-013g01L7R<#FR{#FRm#F#FRn,D35|31D3mRm1D3<R<'C'C%{?#A#A#A#A#A#A#A#L,z3=y3<%FnRn#F,D31D3n/Cm'C'Cg02E:Rn'_'x=^UVPWP31V39R?P41V38CPS04PYPZ1`ZGA?Z\gS055@ZR~PdPZPZPZP5P6P6P71Mge,HZEvPd1R3=R=9e3[R71R3ERE9W3g=Z3\'M,HZC2PdPZPZA;Ze7PdPZA;ZegPdA;Ze\R7C2C2PdPZA;Z_=A;Z=b5@ZPdA?Z\[9@Z7C2C2C2C2P^P`b2b3b4X03X63X93W5A>81Ng02PI\t1KN:/Q9,:T[%1T%1:Rt\o[16D:16:F'<A>t:B[[[[^03^63^93^5lP1f@Rt,8BRo/7NRb#11=oNPtPbP:PzPkf>O8b1b>b=bPb;A>}|BebFbEbDbCb;b8bLb=b>9YSBDE17QB,:LRQePQP3PT19rI,5@RQ/O1,B@13J:RS'0X731d@0%1R%f@7>R13JpRR,=Q1B@113JG'0X73P31Q:pR0,3J1:N1X73P3P3%~JR}P}PBP0P3\3/N}PVPWPXPYAZ3\],M[,HZP^P`b2b3b4X031Q1C,:B^03P1PGO1b1Gt1KSRRRPJP:PpPVPWPXPYPZ1`Z8RS9@ZaPdP7C2P^P`b2b3b4X03X5l1<h4%14Rh[^03^5lP116GFPGP8O3b1PVPWPXPYPZA@ZScRcPdQ02C2P^P`b2b3b4X03X5lRF1<4iRiQ03[^03^5lRaP116DGPGP8O3b1RCI00E\1:NRPJPsPVPW%r3RRPYA?ZefP^P`b2b3b4PjP1b1RjPFPaP116DIPIP:O3b1H0213Js,0219xv,5@Rs13JqRq13JIRaPVPWPXPYPZA?Ze\RePdPeC2P^P`b2b3b4X03Re10211024[^03R2P113JuRuP4O2b11D3{/C<,Cm/_n=^UVRUPWQ04PYPZAW3E=,Mg,HZPdPZP~PdAW3=E9?Z\C2C2P^P`b2b3b4X03X63X93X5l1K94,:NA>:4N1K8:,09[[^03^63^93^5lP119zx,5@RE#113JrR~PuPEP9P8O6b1I031=sq/0a1=EuRa13JvRq,01X73PVPWP3P?P4PRCPPYPZA?Z\=R=PdP=C2P^P`b2b3b4X03X6310141049R=[^03^63P1Pq19kz,5@Rz13JwRw'=P4O3b117aN%1a10aNPEPuPVPWPXPYPZA@Z7SPdP7C2P^P`b2b3b4X03X5l%11/<4Ph[^03^5lP110zNPzP:O3b1PeP2P1PwP9O2b1H04PJPrPBPjPVPWPXPYPZPcPdA;Z\[C2P^P`b2b3b4X03X5l164B\i^03^5lP116DvPvPIO3b1I0516~NPUPWP3P3P?P9PRCPP4PRCPPYPZ1R3>R>=;ZgPdPZA?Z\>PdQ05C2C2P^P`b2b3b4X03X63164N109N\=[^03^63P113Jxf</9k,5@13Jy'=P4P9O4b1b8Ca9YaNDE1B@a/0~ebAbJbI1OQpApQpCDEbK1B@T/7BP1E\b8Q011b@LDE1U@A,5@1b@ADE15@P/0KeAcHOM209OMET19G8P4ETQ00eCaWHWGXN3XM;WOWBo"). Qed.

(* [comment removed for export] *)
Ltac kx_tbl_idx tl :=
  repeat match goal with
  | |- context [edenot (kE ?zv ?xs) (EAlu ALU_SRL ?x ?s)] =>
      lazymatch goal with _ : 0 <= bv_unsigned (edenot (kE zv xs) (EAlu ALU_SRL x s)) < 2 ^ tl |- _ => fail | _ => idtac end;
      let na := eval vm_compute in (length zv) in
      let IDX := fresh "IDX" in
      assert (IDX : 0 <= bv_unsigned (edenot (kE zv xs) (EAlu ALU_SRL x s)) < 2 ^ tl)
        by (apply kx_srl_tl; [ rewrite (ez_ok zv (kE zv xs) (kE_atom zv xs));
                               cbv [ez]; change (length zv) with na; cbv [nth Nat.ltb Nat.leb]; f_equal; lia
                             | lia ])
  end.

(* [comment removed for export] *)
Ltac kx_flat_hook hook :=
  lazymatch goal with
  | |- flat ?E ?a ?len =>
      let b := eval unfold E in E in
      lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
        let na := eval vm_compute in (length zv) in
        change E with (kE zv xs); unfold flat;
        rewrite (estart_ez_kE zv xs a);
        [ | cbv [ez a_base a_off]; change (length zv) with na; cbv [nth Nat.ltb Nat.leb]; hook; kx_abstract; lia ];
        unfold elenZ; cbn [edenot]; rewrite ?Z_to_bv_unsigned;
        cbv [ez a_base a_off]; change (length zv) with na; cbv [nth Nat.ltb Nat.leb];
        unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 64) with (2^64); rewrite ?Z.mod_small by lia; hook; kx_abstract; lia
      end
  end.
Ltac kx_flat := kx_flat_hook idtac.

(* [comment removed for export] *)
Lemma elenZ_lit : forall E z, 0 <= z < 2^64 -> elenZ E (ELit z) = z.
Proof.
ltac2:(KReplay.run1 (kr_t_KXPost ()) [] "h04__x1h11zh21Eh31Hh47__arithh54__ffh68__varmaph75__witp;2p;1p;3p;4p;7p;8p;6g00:]j2:Tg000ij10Tg003lj14Tg004Jj25Tg00:Aj23Tg00Gaj22Tg001Nj1MTg01PKj2BTg005dj31Tg00;`j1?Tg00<@j1>Tg00\Sj2<Tg00=>j1;Tg00=\j1UTg00>Gj29Tg00]Oj2TTg00>jj48Tg01W:j3STg01W]j7LTg01VXj1KTg01[<j8ETg00@9j2ATg007Hj2CTg00@[j2DTg00AGj3@Tg00Afj4FTg01XAj1GTg01Q1j1HTg01QZj3ITg002Oj2JTg006>j27Tg01RFj2=Tg00CAj6NTg00M:j1OTg00SDj2PTg01YZj2QTg00?Uj7RTf1R0g00HhR1g00IGR2P2g00IgR3f0R4g00JnFRp=6g01\Bg00F@R5g00GCR6/:4g00F^R7#0R8#4R9%08#0#0#0#0R8#4'5R:,34'2R;P5%M8R8/B0f2R<9154X15g00H<R=#?%>=1<50%;5%U5R=P1P2P2P3P=P1P2P2P3P51956g01]>1T57R7C8,6=P5P7g00JG1959=S58C8,6=FLR7%K2P7GE1A=3P4P<g00KNR=g00KnR3'C1D4<=1=3dA@560CFb5b6b7X051:60R6130:'2\;^05P4P<P0O2b4%G8,59,30,26e%H8,30,26e9I801J80,781=80EN%O0R6,P<,78=150e1Q<6=150eW3W1W2o"). Qed.

Ltac kx_z hook :=
  lazymatch goal with
  | |- context [kx_env (map (Z_to_bv 64) ?zv) ?xs] => fail
  | _ => idtac
  end;
  let E := lazymatch goal with
           | |- context [flat ?E _ _] => E | |- context [estart ?E _] => E | |- context [elenZ ?E _] => E end in
  let b := eval unfold E in E in
  lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
    let na := eval vm_compute in (length zv) in
    change E with (kE zv xs); unfold flat;
    repeat match goal with |- _ /\ _ => split end;
    repeat match goal with
    | |- context [estart (kE zv xs) ?a] =>
        rewrite (estart_ez_kE zv xs a); [ | cbv [ez a_base a_off]; change (length zv) with na; cbv [nth Nat.ltb Nat.leb]; hook; kx_abstract; lia ]
    end;
    rewrite ?elenZ_lit by lia;
    cbv [ez a_base a_off]; change (length zv) with na; cbv [nth Nat.ltb Nat.leb]; hook; kx_abstract; lia
  end.
