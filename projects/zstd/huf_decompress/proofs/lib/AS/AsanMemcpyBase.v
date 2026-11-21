(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (26 recorded proofs replaced by written proofs (lenZ, memk_0, memk_n and 23 more)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.zstd.huf_decompress.images Require Import Asan.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim RefMemcpyLib.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AsanMemcpyBase () := "C47Corelib7Program6Basics4flipC46Stdlib5Lists4List:firstn_nilC47Corelib4Init5Logic8eq_ind_rC56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3maxI47Corelib4Init5Logic2eq00C47Corelib4Init5Logic8iff_reflK47Corelib4Init5Logic2eq01C46Stdlib9micromega;ZifyClasses5mkrelK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z8max_specC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib9micromega;ZifyClasses5mkappK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqK47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init9Datatypes6option00C47Corelib5Lists7ListDef6firstnC59OSSVerify5KrLib2AS7CatExec6wbytesC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:firstn_allC47Corelib4Init5Logic6eq_indc59OSSVerify5KrLib2AS>AsanMemcpyBase4memkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS<RefMemcpyLib9skipn_addC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS<RefMemcpyLib9sub_splitC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC47Corelib4Init3Nat3addI47Corelib4Init5Peano2le00K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr03C59OSSVerify5KrLib2AS<RefMemcpyLib:sub_lengthC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS>AsanMemcpyBase3sb_C1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6mkapp2C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_leC59OSSVerify5KrLib2AS8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC59OSSVerify5KrLib2AS5Hoare3at_C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec3rdnC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS<RefMemcpyLib3subC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C47Corelib5Lists7ListDef5skipnC46Stdlib9micromega;ZifyClasses3injC35stdpp7tactics<f_equal_helpC59OSSVerify5KrLib2AS<RefMemcpyLib7rdn_subC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3minC56Stdlib6ZArith6BinInt1Z3minC46Stdlib9micromega;ZifyClasses8or_morphC56Stdlib6ZArith6BinInt1Z8min_specK46Stdlib9micromega7EnvRing5PExpr07C59OSSVerify5KrLib2AS<RefMemcpyLib4at_uC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List=length_firstnC59OSSVerify5KrLib2AS7CatExec>rdn_wbytes_outC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z8inj_succK46Stdlib9micromega=RingMicromega3Op205C56Stdlib5Arith8PeanoNat3Nat3minC56Stdlib6ZArith4Znat5Nat2Z7inj_minC59OSSVerify5KrImgGTgt_huf_decompress_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst7Inj_Z_Zc59OSSVerify5KrLib2AS>AsanMemcpyBase2b_C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC47Corelib5Lists7ListDef3nthC47Corelib4Init5Peano2ltC59OSSVerify5KrLib2AS<RefMemcpyLib7sub_nthC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS>AsanMemcpyBase6rd_srcC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z6inj_ltC59OSSVerify5KrLib2AS<RefMemcpyLib;store_ok_atC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okc59OSSVerify5KrLib2AS>AsanMemcpyBase4lenZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS<RefMemcpyLib>wbytes_extend'C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS>AsanMemcpyBase;memk_extendC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3subC56Stdlib6ZArith6BinInt1Z3subK46Stdlib9micromega7EnvRing5PExpr04C47Corelib7Classes?RelationClasses=eq_TransitiveC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9Morphisms@reflexive_properC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC47Corelib7Classes?RelationClasses<eq_SymmetricC47Corelib7Classes?RelationClasses8symmetryC47Corelib4Init9Datatypes3appC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxC46Stdlib5Lists4ListAskipn_firstn_commC46Stdlib5Lists4List=firstn_firstnC59OSSVerify5KrLib2AS<RefMemcpyLib3LWvC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC59OSSVerify5KrLib2AS8PropExec6v_slliC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec7v_srliwC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec4v_orC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses9and_morphc59OSSVerify5KrLib2AS>AsanMemcpyBase9sb4_splitC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS>AsanMemcpyBase9firstn_sbC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS>AsanMemcpyBase8skipn_sbC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesc59OSSVerify5KrLib2AS>AsanMemcpyBase6sb_lenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS<RefMemcpyLib>sw_bytes_mergeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z8lor_commc59OSSVerify5KrLib2AS>AsanMemcpyBase8merge_sbC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallI47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyK4ELinuxProcessSemantics5Riscv5Instr5instr06K47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib2AS8PropExec4getrC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions9bv_signedC59OSSVerify5KrLib2AS8PropExec6v_addiC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS>AsanMemcpyBase7rd_src1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS5Hoare7at_addiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec8step_lbuC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00K4ELinuxProcessSemantics5Riscv5Instr5msize01c59OSSVerify5KrLib2AS>AsanMemcpyBase>asanreflect_fxC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=bytes_le_to_ZC59OSSVerify5KrLib2AS<RefMemcpyLib6u_lez4C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC59OSSVerify5KrLib2AS8PropExec7step_lwC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5msize03K4ELinuxProcessSemantics5Riscv5Instr5instr07I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C59OSSVerify5KrLib2AS8PropExec4mkstC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01c59OSSVerify5KrLib2AS>AsanMemcpyBase6wr_dstC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7MmapSim:step_sb_atC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS>AsanMemcpyBase<memk_extend1C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C59OSSVerify5KrLib2AS7SeqExec:step_sw_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS<RefMemcpyLib<sw_bytes_LWvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS<RefMemcpyLib;sb_byte_LBvC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3ltbC56Stdlib5Arith8PeanoNat3Nat6ltb_ltC46Stdlib5Lists4List9nth_skipnC46Stdlib5Lists4List:nth_firstnC59OSSVerify5KrLib2AS8PropExec6v_srliC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS<RefMemcpyLib@sb_byte_srli_LWvC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS>AsanMemcpyBase;sb_val_srliC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7add_0_rC56Stdlib6ZArith6BinInt1Z6shiftrC45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedC56Stdlib6ZArith6BinInt1Z:shiftr_0_rC56Stdlib6ZArith6BinInt1Z7mul_0_rc59OSSVerify5KrLib2AS>AsanMemcpyBase<sb_val_word0C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z4landC45stdpp9bitvector;definitions=bv_wrap_smallC59OSSVerify5KrLib2AS8PropExec<Z_land_rangeC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions@Z_to_bv_unsignedC59OSSVerify5KrLib2AS8PropExec6v_andiC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z9land_onesK47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01I47Corelib4Init5Logic2ex00K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init5Logic7and_ind".
(* [comment removed for export] *)
Unset Lia Cache.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

Abbreviation ASEGS := Asan.M.loaded_segments.

(* [comment removed for export] *)
Record mcH (mem0 : word -> option byte) (dst src : word) (n : Z) (bs : list byte) : Prop := MCH {
  Hn : (0 <= n < 2 ^ 64)%Z;
  Hlen : length bs = Z.to_nat n;
  Hsrc : rdn ASEGS mem0 src (length bs) = Some bs;
  Hdst : store_ok ASEGS mem0 dst (length bs) = true;
  Hdisj : (bv_unsigned dst + n <= bv_unsigned src \/ bv_unsigned src + n <= bv_unsigned dst)%Z;
  Hnws : (bv_unsigned src + n < 2 ^ 64)%Z;
  Hnwd : (bv_unsigned dst + n < 2 ^ 64)%Z }.

Section MC.
  Variable mem0 : word -> option byte.
  Variables dst src : word.
  Variable n : Z.
  Variable bs : list byte.
  Hypothesis HOK : mcH mem0 dst src n bs.

  Let Hn := Hn _ _ _ _ _ HOK.
  Let Hlen := Hlen _ _ _ _ _ HOK.
  Let Hsrc := Hsrc _ _ _ _ _ HOK.
  Let Hdst := Hdst _ _ _ _ _ HOK.
  Let Hdisj := Hdisj _ _ _ _ _ HOK.
  Let Hnws := Hnws _ _ _ _ _ HOK.
  Let Hnwd := Hnwd _ _ _ _ _ HOK.

  (* [comment removed for export] *)
  Definition memk (k : Z) : word -> option byte := wbytes mem0 dst (firstn (Z.to_nat k) bs).
  (* [comment removed for export] *)
  Definition sb_ (j : Z) (m : nat) : list byte := sub bs (Z.to_nat j) m.
  (* [comment removed for export] *)
  Definition b_ (j : Z) : byte := nth (Z.to_nat j) bs (Z_to_bv 8 0).

  Lemma lenZ : Z.of_nat (length bs) = n.
  Proof. rewrite Hlen. lia. Qed.

  Lemma memk_0 : memk 0 = mem0.
  Proof. reflexivity. Qed.

  Lemma memk_n : memk n = wbytes mem0 dst bs.
  Proof. unfold memk. rewrite <- Hlen, firstn_all. reflexivity. Qed.

  Lemma sb_len : forall j m, (0 <= j)%Z -> (j + Z.of_nat m <= n)%Z -> length (sb_ j m) = m.
  Proof. intros j m Hj Hm. unfold sb_. apply sub_length. rewrite Hlen. lia. Qed.

  (* [comment removed for export] *)
  Lemma rd_src : forall k j m,
      (0 <= k <= n)%Z -> (0 <= j)%Z -> (j + Z.of_nat m <= n)%Z ->
      rdn ASEGS (memk k) (at_ src j) m = Some (sb_ j m).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemcpyBase ()) ["MC"] "p'0h04__x1h14__x2h24__x3h34__x4h44__x5h51Hh62H0h72H1h84__p1h92H2h:2H3h;2H4h<2H5h=5Hlen0h>3Hm0h?7__arithh@4__ffhA8__varmaphB5__withC1ahD4cstrhE5cstr0hF1xhG2z1hH4__p2hI1ni001nhJ6__sat3hK2H6hL2HmhM6__sat4hN4__x6hO2z2hP6__sat2hQ1yhR2H7hS2HahT4__p3hU6__sat5hV4__x7hW4__x8hX4__x9hY1mhZ1zh[2z3h\2Hjh]2Hkh^1bh_1jh`1kha2m'hb1op%0p&0p;2p;1p;3p;4p;<p;8p;6p;9p;Bp;7g00:JR0j21Tg009oR1j27Tg001kR2j12Tg00cUk10@Tg004_j1MTg005Dk10=Tg00dOj2iTg00;@j1tTg00<Fk20LTg009Sj26Tg005bk108Tg00BLk10CTg00WRk10fTg001KR3j1aTg00X4j3pTg00XSj3xTg00e9j2Vk10XTg00ejj4]Tg00f^j4kTg00gVj2UTg002hj38k103Tg00h8k30ZTg003`j2jTg00ALk10;Tg00>FR4j1:Tg003Bk102Tg004:l<nTg00];R5j20Tg00hVk40GTg007ej4}Tg006Ek20BTg006ek20eTg007Hk30dTg008Lk100Tg0091j2yTg00;^k20aTg00<ck30`Tg00>ek20?Tg00=Gk10_Tg00=ek20^Tg00?Nj3wTg00CJk10]Tg00DFk10\Tg00Ddk10[Tg00EOj2vTg00F2k20<Tg00G@k10YTg00^Ij1hTg00Hjk20WTg00ILk20VTg00J8k30RTg00JWk40QTg00KIj4cTg00i9k80PTg00]Xk204Tg00]oR6k207Tg000mj6NTg00iVm90KTg00Yhk60JTg00jRj2eTg00:fj2YTg00jiR7j2qTg00kFk60HTg00knk20MTg00lPk30STg00m3k40DTg00mlk30TTg00nNm90UTg00ZDk10jTg00`Pk20iTg002Kk20hTg00L4l<uTg00aJlB~Tg00@7j3lTg00@`j2|Tg00Alj3oTg00Blk20gTg00Chj4{Tg00FUj4^Tg00LYj7_Tg00M=j7zTg00^nk30cTg00Maj8dTg00HFk70ATg00Gbk60bTg00OoR8f0R9'1p=3f2R:f1R;'0/19p=9g00NER<?8;9p=?20h89p=L1j<9p==P<g00NcR=P<P<P3f4R3P2f3R>g00OBP:P;P9M<up=rP=P<P<P<P2P2f5R?P3P>P:P;P9M<up=bP=P=P<P<P4P2P2P>g00oLP:P;P9M<up>0:P<P<P<P<P<P<P5P9P;P:P5P>P3P?f6R4f7R@f8RAf9RBMB~p=gP<P<P0P@P0P4P?P3P>P:P;P9M<np=Z1689p=H1198p=GA8<98p=QA8<:;,7>/Y9p=C20?<9p=AAl<;9p=5g00TXRC,|9p>0>Al<;9/|Cp=Rg00SMRD1|;C;o9p=<AoD;99oD:p=P20g<9p=SP<P:P;P9C{p=[P<P<P3P>P:C{P;P9C{p=J20<<9p=EP<P;g0100RCP9C^p=OP:g00PMREg00PlRFPFg00QLRGP<P;g00UkRHP9C^g00QlRIF_p=\P>PEPFPFPGP:PEPFPFPGP;PIF_P9Fzp=FP<P;g00UDRJP9C^p=>B0c<;9p=4P:PEPFPFPGP<P;PJP9C^PIF_p=;P>PEPFPFPGP:P;P9Gdp>09P3PEPFPFPGP>PEPFPFPGP:PIF_P;P9Gdp=BP?PEPFPFPGP3PEPFPFPGP>P:K0AP;P9Gdp=DP=P=P=P<P<P<g00b0P2P2P2P5g00bPP?P3P>P:P;P9MB~p>0OP=P<P6P2P0g00c3P?P3P>P:P;P9M<np>0N10:;,0>/19p=@Al<;99l<:p=IAoD;9p=sP;PEPFPFPGP9J0bp=mP:PEPFPFPGP;P9Fzp>01P<P;PHP9C^p=TP>PEPFPFPGP:P;PEPFPFPGP9PIF_Fzp=WP4PEPFPFPGP?P3P>PEPFPFPGP:P;P9GdGdp=X11;9,Y:p=KP=P=P=P<P<P<g010WP2P2P2P7g0117P?P3P>P:P;P9MB~p>0IA8<;9,7:p=f10;9,0:p>0FP:PEPFPFPGP<P;PCP9C^PIF_p=`P:PEPFPFPGP;P9K0Ap>0617;9,Y:p>0517>:17;9'Yp>0E%3:S00p,1nRE,1:'7Q00%2:RI=9>Ep,3srcRC$0@g00RLR7#MRH#MS01#MS02#M#M#MR0$0=R6/iCR5#3RJ%tHRK%t0R0+0LRL,65RM'7p,3dstRN$0@1i6NRO#3RP16OLRQ'7P=%29RR=9@EQ02$0=$08RS$0CRT$0fRUg011ZRVp,4mem0RW%aBRXp,2bsRY5pS7xN1VCAP;C]PSPY%aARZP;Ck,UT38]LP?g00T9R[#2=94E%a@R\>0ZSY9pS[,UTR],jU&0;S,UTR^=8U]ePSPYP\P[Ck,UTR\98U^ePVApSZY9xWN1VC@P[C]=8U\eWL%:9#2=9AEPUPVPW1VCBR\%:;RZC]PSPYf:R^#aR]%::R_Ck,UT98U9XbUP<&086R`&0XCRaPa%2XRbPBP`\</ja1?bB%LBRa/?BP<P<&03<RcP9XF<RdPc1?;9$02XQ<XF<PbPaPdPd%=RXF=S03PXPaPd%L9XF<S04PBPB%=BRaDrEbPBPBPaM<n%2ZS05,0BRX/1E%2;Re%t7Rf'0S06=9BES07Pd11;9$02XQ<XF<S08PXPd109fXF<S09PeO1RXO1Rg,0BPdPdPdP<P<g012i10;9H0G#=XY<XI<S0:PBPBPaQ05PgPdPdQ03PZPXQ09P;Pe%=eH0:S0;EbM:gPEPE%=ES0<GZP9C}S0=Q0720BSYRX%aERg58=%2XRa%LERh'?RiP=P<&03=P2Pc1?eRA8=;920e;940dXQ=XF=PXPa%=aPgQ04PEO1PdQ04PEPEQ0<DrS0>M<np,4HlenS0?C}S0@Pi&00XS0A%3aS0B&003S0C%23#3S0Df=Ra,y8%Ha%LaRePa%Ga%Qe'7CCf>Re#LP<1y8ES0E%HES0FPhPE%GES0G%Qh'7CCS0HPhP<20aK0S0I%HK%30%HL[[Rc%3KR2g00S1RjB0`K0;UWSR0%3L\j^S2R2P1PPPQfDS0J,??PaP1PJPMfH,?BfBRjp,2HnRk%3ERl16ELRm'7RnP1PlPmfM,?eP9%:[Ro#:S0K#:S0L#:Rp#ARq%AoS0M20?<[R['5S0N'5S0O$0>S0P%:pS0Q#ARp&0_7-0^<S0R=w<qRo/5[Rr'R&0;DRs,<r3P&0CDRD%S>S0SP:&0]<RrP;%S3Rt9[r3DJ&0\<Ru&0[<RvPvPvPv1v<8Rw%EHRx'O20<<7Ry=\vxRzCFPvPv1>xwA\vywS0TCF&0YFRFPvPv%h7S0U#h#ER7,>wPFPvPv1v<fR{,47,4xQ01#ER|'>PFPvA;vwxS0VPFPzH09DBDBED20WvGRGP9P:g00VRRzg00W2R}'j20V9:=8z}dB0R<8;H0QR}b@bAbBX0<X1<X2<X3<%H;P9P;%G;%Q9S0W'7CC%33Rz10?fS0X=9>31?3?\z[[[^0<^1<^2<^3<P9fIS0Y#2PEfQPjfCS0ZQ0JfGS0[fNO8b?XKmX<lP;P9O2n2001000000121000000bCX;MX5JP;P9O2n2001000000121000000X:QX6PP;P9O2n2001000000121000000bJbMbOb9bGb7bEbDb=b>CcL0P1VCb=8`\P`%2],VCPVPWP9%:>S0\C]PSPYf;Rb#aR~Q0\Ck,UT58UX^`PVPWPXPCPYP]P_p,4HsrcP=PgQ0\-04~0079XI=204]_S0\007g%L^S0]10IfR`'0S0^/1hQ0\Q0^P]Q0]PdQ04P^P^%=^S04DrS0^P_P`Q09P:PI%=IH0:S0\J0OPgPhQ0>J0N%2_S0_,0^S0`/1EA9^`ES0aPdQ08Q0`PdQ09PIO1RIO1R`,0^PdPdPdQ0:P^P^Q04Q0_P`PdPdQ03P_PIQ0\EbM:gPEPEQ0<GZP;C}Q0aQ0@PiQ0AQ0B&00?%2?#3Q0EQ0HPhP<f@RI,y8S0a%HI%LIR8PI%GI%Q8'7CCS0<fAR8#LS0\P<Q0IPcP0P2P1PPPQP>%2aPfP?C@PeP1PJPMP@%28PfPBC@Q0ZPkPnP1PlPmf<S04fFS09#2PfPeC@P9p-0RaQ0L#AR_Q0K#AR`Q0M'5S0K'5,RqS0LQ0N,5`S0`,5o,Rp15`[S0b9IpoQ0L/ss'<3PPD%S?S0L?[?rP:PrP;A[t>rDJPuPvPvPvPvQ02#ERo,OwA\vyoCF1mv@S02Q0T601vPFPvPvPv1mvAS0TPvQ0U#ER`%hHS0c#ERH'TCWPvPv1>Hw1mvBS0dCFPFPvQ0VPFPv14x{S0e,4o=;vHPFPvPv1>woPFQ0e,4y=;v`DBFXEDEDPGP}b@bAbBX0<X1<X2<X3<X4<X8aXHaWT%H3P9P3Q0W,7?CCP@P>P3%G3/7ACC%3>P@P3PfP4C@%3A104fS0W=9?@[[[[[^0<^1<^2<^3<^4<^8a^Ha^TaP9%QjQ0FfRRo#GPoPEPjfJS0e#2PIP8Q0ZQ0JQ0[fORoO=b?XKmX<lP;P9O2n2001000000121000000bCX;MX5JP;P9O2n2001000000121000000X:QX6PP;P9O2n2001000000121000000bJbMbOb9bGb7bEbDb=b>CcPXQ0?ENN90K1VC^S0fP9J0Jb7PVApS]YS0g9xWNP\PZC]PVQ0gPWPNP\PZP=1e]XS0hQ0f,i6RNQ0_;9ORW10ORS0f;KNXI=P=Pg1e~9#2,0OS0i=KWNXI=P<105BRWQ0_,09S0_/1O1e~g#2,0O;K9XZ<Q05,0WS0j/1OS0k1e]gS0l#2S0m,0OS0n/1WS0o'YQ06,0WS0p/1OR~Q0]/qhRN,0OS0q/1WRR'YQ0kQ0oP~PRPdQ08Q0jQ0pPdPdPdQ0:PWPW%=WRRQ05Q06PdPdQ03PZQ06Q0;EbM:gS0;POPO%=ORZGZPdQ08Q0nQ0qPdPdPdQ0:POPOPZQ0mPNPdPdQ03Q0lPNP]Q0]Q0^PgPhQ0>J0IEbM:gS0>PWPWPRGZJ0HQ0=Q07Q0@PiQ0AQ0BQ0CQ0DQ0EQ0HPhP<Q0aQ0<Q0\P<20M9:S0^169:1q9:RRP911:9?fR:CCS0]1q;>S0lP<Q0IPcP0P2P1PPPQQ09,05RR%2e<0FfS09/1O10O>S03;KRf?S0mP1PJPMQ0e,05Re%2jPfPOC@10O@S0e;KeQ0JPkPnP1PlPm105oReQ0[#2S0[PfPOC@Q04,0OS04;KeP9Q0Q#:Re#:RN#:RZ#AR~%AeReQ0N9Iq_7IpS0N'RS0QQ0Q%:ZS0:#ARZ%ANS06Q0R=w<p7Ie'RS05Q05Q0K,RqRNQ0b9Ip_S0K,5ZS0o$0>Q0N,RZS0NQ0NQ0:#:#AS0:Q0RQ065w</5pS06,5~'RQ0:Q0o'5Q0K9IZ~Q06,5Z1sNs'<'<9PNN'<5PN3P3P3P3PPDPtP:%SB?[4rP;%SAP?PrP>%S@DJDJPuPvPvPvQ0c#M#ERNQ01#h#ERZ5`vS01Pv1THNCWPvA;vZNS0cPv1THZCWPFPvPvPvPv1Ow7A\vN7CFPv1mvbPv1TNwCWPFPvPvPvPvQ0U#M#ER7,OwA\vZ7CFPvPv1>7wA\vZwS0UCFPFPvPv14`{S0Q,4xS05/>7PFPvQ0VPFPv14|7=;vy14y7=;v|606vPF14yxR~Q0Q'4S0Q=;v|14|HS0N=;v~606vFXDBEDEDEDPGP}b@bAbBX0<X1<X2<X3<X4<XN<XV<XW<XX<X8a16A@P3PA11@A?f3@CC%H@?fB@S06%QBS0K805^Q06%G@Q0K405Q0X=93A%3?S0KA9A^?10?^;KA104@S06PAPfPBC@10B^Q063K[[[[[[^0<^1<^2<^3<^4<^N<^V<^W<^X<^8aP9fTS0:#GPjQ0JQ0:PEPIPOfKS0:#2fSP5P8Q0ZfES0oQ0YfPp,5HdisjO@b?XRmXKlP;P9O2n2001000000121000000bCX<MX5JP;P9O2n2001000000121000000X;QX6PP;P9O2n2001000000121000000bMbUb[b:bOb9bGb7bEbDb=b>Cc1i6\S0YPCPBQ0=Q07Q0@PiQ0AQ0BQ0CQ0DQ0EQ0HPhP<Q0IPcP0P2P1PPPQ105jRB#3PbP1PJPM%3RPIPkPnP1PlPmQ0:,05R\#3P9Q0M,5q9IepQ0`/<s'<PDPtP:Q0LP;Q0SDJS0SPuPvPvPvPv1Ow|Q02CFPvPv1>|wQ0TCFPFPvA;vw7S02PFPv147{,4x=;v|R7PFPvPv1>w`PFPvPv1>wyPFPvQ0VPFA;vw~H09DBDBFXEDPGP}b@bAbBX0<X1<X2<X3<X4<X8aXHa%H>P?%G>P4H0EQ0KQ0W=9>?Q0K%34Q06#3[\z[[[[^0<^1<^2<^3<^4<^8a^HaP9%QI1?IEQ0[PEPOPoP5P8PjQ0oPbP@fLO=b?X<mX;lP;P9O2n2001000000121000000bCX:MX5JP;P9O2n2001000000121000000X9QX6PP;P9O2n2001000000121000000bPbJbGb7bEbDb=b>Q0=Q07Q0@PiQ0AQ0BQ0CQ0DQ0EQ0HPhP<Q0IPcP0P2P1PPPQ16BLPbP1PJPM16RLPIPkPnP1PlPm16\LP9Q0O,5p/<sPDQ0SPuPvQ02PFPvP7PFPv1v<K>0S<6R69`vyRKPFPv14`|=`v6PFPvPv14y|/O6PFA`v~6DBFXFXPGP}b@bAbBX0<X1<X2<X3<X4<Q0X=9:316:LR710?4RR/6LRw103@/6LPw[[[[\z^0<^1<^2<^3<^4<P9Q0[PEPOPoP5PjQ0oP4p,4HnwdRzp,4HnwsR{O:b?X<mX;lP;P9O2n2001000000121000000bCX:MX5JP;P9O2n2001000000121000000X9QX6PP;P9O2n2001000000121000000bPbJbGb7bEbDb=b>H0DS0XENPXQ0?ENQ0g-0BSS0gB0TS]YR]ENP<PWQ0_/1LXZ<Q0j/1LQ0p/1LPdQ08Q0jQ0pQ0;PLPL%=LRWGZQ0=Q07Q0@PiQ0AQ0BQ0CQ0DQ0EQ0HPhP<Q0IPcP0P2P1PPPQPB%2^PfPLC@PbP1PJPMQ09/1LPIPkPnP1PlPmP\Q0Z#2PfPLC@P9Q0P/ssPDPtP:PrP;Q0L?[>rDJPuPvPvQ05/>HPFPvPKPFPvQ0N=`v6PFPvPv14yH/O6PFQ0Q=;v6DBFXDBPGP}b@bAbBX0<X1<X2<X3<X4<P;P:PfP3C@16;L10>@/6L103?Q0W;9L[\w[[^0<^1<^2<^3<^4<P9PEPOQ0[PoP5Q0oP4PzP{O9b?X<mX;lP;P9O2n2001000000121000000bCX:MX5JP;P9O2n2001000000121000000X9QX6PP;P9O2n2001000000121000000bPbJbGb7bEbDb=b>CcQ0YQ0XENP=Q0hQ0f/1LXI=P=PgQ0i/1LXI=Q0n/1LQ0q/1LPdQ08Q0nQ0qQ0>PLPLPWGZQ0=Q07Q0@PiQ0AQ0BQ0CQ0DQ0EQ0HPhP<Q0aQ0<Q0\P<Q0^Q0]Q0lP<Q0IPcP0P2P1PPPQQ03/1LQ0mP1PJPMQ0e/1LQ0JPkPnP1PlPmQ04/1LP915_[9IpqR_Q0b9IpqRp15ep15e_/<s'<'<'<PDPtP:%S4?[4rP;Q0LP4PrP>PrDJDJPuPvPvPvQ01Pv1TxNCWPvQ0cPv1TxZCWPFPvPvPvQ0TPv1TZ`CWQ0dQ0U601vPFPvPKPFPv14y`=`v6PFPvPv14|`/O6PFA;v~6DBFXEDEDPGP}b@bAbBX0<X1<X2<X3<X4<XN<X8aXHa16?3P;P?113??f;3CCP@P?P>%Q?,7ACC10>?/6L10@4/6L11RL[[\7[[^0<^1<^2<^3<^4<^N<^8a^HaP9Q0GQ0FPjQ0JP5PEPIPOP8Q0oP^PzP{O=b?XRmXKlP;P9O2n2001000000121000000bCX<MX5JP;P9O2n2001000000121000000X;QX6PP;P9O2n2001000000121000000bMbUb[b:bOb9bGb7bEbDb=b>CcPXQ0?ENQ0gP]ENN90UENWLXa=P9O1n0110000020111100P:O1b6b5PV&0j?1VC3P>C]20i3>,UT58UeWLW\W]XY=X_<X`<o"). Qed.

  Lemma rd_src1 : forall k j,
      (0 <= k <= n)%Z -> (0 <= j)%Z -> (j + 1 <= n)%Z ->
      rdn ASEGS (memk k) (at_ src j) 1 = Some [b_ j].
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemcpyBase ()) ["MC"] "h04__x1h14__x2h21xh31Hh42H0h52H2h65Hlen0h77__arithh84__ffh96__sat4h:8__varmaph;5__with<1ah=4cstrh>2z2h?6__sat3h@2HahA4__p1hB4__p2hC4__x3hD4__x4hE1nhF1yhG2H1hH2H3hI2HjhJ2HkhK6__sat5hL1jhM1khN1lhO1mhP1ohQ2z3p&0p;2p;1p;3p;4p;<p;6p;7p;8p;Bg00:JR0j20Tg009oR1j21Tg00;@j1KTg00];R2j26Tg004_j1?Tg005Dj1uTg005bj1qTg00BLj1[Tg00WRj1hTg00>Fj1BTg00`Pj2cTg00gVj2=Tg013Mj1`Tg00ALj1]Tg00Alj37Tg002hj35j1STg001KR3j1ITg014Fj2xTg014lj4XTg003`j2NTg00f^j4sTg015HR4j2^Tg002Kj2ATg009SR5j24Tg006Ej2gTg001kR6j1FTg006ej2eTg007Hj3dTg004:l<JTg007ej4bTg008Lj1aTg0091j2RTg00:fj2HTg00;^k20;Tg00<Fk20:Tg00<ck309Tg00>ej2<Tg00@`j2QTg00=Gk108Tg00=ek207Tg00?Nk304Tg00Blj2ETg00CJj1|Tg00Chj4GTg00DFj1{Tg00Ddj1zTg00EOj2ZTg00^Ij1YTg00F2j2CTg00G@j1tTg00^nj3VTg00Hjj2pTg00ILj2oTg00J8j3rTg00JWj4nTg00KIj4TTg000mj6LTg015`j3mTg00ZDj1vTg00e9j2wTg00ejj4lTg003Bj1kTg00hVj4yTg016\j6~Tg00L4l<\Tg00@7k300Tg00FUj4PTg00LYk701Tg00M=k702Tg00Gbk603Tg00HFj7fTg00Mak805Tg00aJmB06Tg00OoR7f0R8'0p=3g00NER9/N8p=;P9g00NcR:P9P9P3f4R3P6f3R;g00OBf2R<f1R=P8M<\p=_P:P9P4P6P5g017Yf5R5P3P;P<P=P8M<Jp=iA59=8p=:A5987p=DB009=8p=8P9P=g0100P8CPp=MP=g00PMR4g00PlR>P>g00QLR?P8g00QlK01p=2P9P=g00UkP8CPp=OP<P4P>P>P?P=P8K02p=@P=P4P>P>P?P8J03p=WP<P4P>P>P?P=P8Ffp=UP9P=g00UDP8CPp=>P;P4P>P>P?P<P=P8L05p=9P:P9P9P9P6P6P5P3P;P<P=P8M<\p=jP9P9P9P9P9P9P2P8P=P<P2P;P3P5f6R2f7R4f8R@f9RANB06p=}%3=RBp,1nRC,0='1g00RLRD#KRE,6</0C%?DRF#?RG#?RH#uRI#qRJ#[RK#hRLg00T9RM#BRN,c;,=KRO%`3%]JRP57J,=K95L8XPLPKPJ%I;RQp,2bsRR1xI7RICX=7JPRS1=K8PJ%I3RTPRPICX=7JP,=K55LXNK1=KS,NLPJPRPQPNCsP:%ICRS1^T8XE:1^QS1A7;RT1A7CRI'4PQPTP8X29RT1A78X29RUP;P;%;;RVD_PSPIPTPUPCPC%;CRWD_RXEi1gJRRY=5:S%FYRZ/:IR[P:P9%S:P6%S9%F=%F8R6':A5:=81e=83dXF:X2:PYPZ%;ZPSPUPCO1PXM<Jp,4HlenRXCbRUP[%aYRS%3ZRZ1R7CR\147C1:IC'110C7%DI'1'HR]PIP91R7414741A74R^/:4'11047%D^'1'H1A7@P9%KFR^%?H#?#?#KRH+0;R_147^%3H20:^HR`,47[[Ra%3^Rbg00S1RcB09^H=UW@RH%3`\c^@bRbp,2HnRc%3CR^14C`R`'1RdP1P^P`1432P8p-0Reg00SMRf%BNRg#BRh,<9Ri1<9gRg1<9N'8'8g00TXRj'QRk%BhRh#B,<9Rl1<9h&08D-079>049iRi1<9MRM'8'8'8/Qj18gM,8i,8l/Qj%]fRj97fk57f57f37%[fRfP9P91E9;P<%|9RkCGP=P9PkP31E93CGCG%{9Rl%z9Ri1Z97RM%YD#Y,C9Rg'M,2i1C9DRD/Og,2i5@i1Wi21ODM,2i5@i5Ui%t>R>Pi1C9GRG,MM,2i1C9FRF/OG,2i5@i1>GM,2i1Wi45@i5UiP>Pi1Z9ER49V9g/>G,2iP>Pi1>Mg,2iP>1MDF,2iC9C9C9C91pi?R?P8P<g00VRRgg00W2RG'N1o8<=5gGdAr97=CnRGb8b:b;X09X19XC9XD9XAeWB147;Rg1:8;'1%D8,13'H1:<;,1g10;7/12'H165E/03%321435[[[[^09^19^C9^D9^Ae^BeP8f:Re#DfAR5/07P5PCPeP@PAf;RAf>R@f?ReO:b7X4`X3^P=P8O2n2001000000121000000b<b9bKbQbHb>b5b=b6CTPYPXEL9mRQEL%`;=7JP,=K95LOeg011Z%v3p,3src/w;PNClP3P;PNPUP[PSPZP\P]PIP9P_PaPHPbPcPdP1P^P`f<R3#3103C'1P8PjPfP91E9<P=PkCGRkPlPi1>MD,2iRM1>DF,2i5@iROP>POC9P?PGb8b:b;X09X19%38RO108='110=<,1B[^09^19P8PCf@P@O3b7X4`X3^P=P8O2n2001000000120000000b<b?b9b>b5b=b6PUP[PSPZP\P]PIP9P_PaPHPbPcPdP1P^P`%3AP8PjPf1E9=PlPiPMP>PMC9P?PGb8b:b;X09PB\O^09P8Pef=O2b7X4`X3^P=P8O2n2001000000120000000b<b?b9b>b5b=b6%FNRO,6;RM/0C16;ER@/0CP9P9P0PTP010=8#kXF9X29PMP@PTPTPTP9P9g012i16=8Cy#;XO9XE9P;P;PVPOPEPTPT%;6X2:PNPE%;EEjM:}PCPCPWM<JPUP[PSPZP\P]PIP9P_PaPHPbPcPdP1P^P`16AE/0CP8PjPfPkPlPiAV9D4/>F,2iRiP>PiC9P?PGb8b:b;X09X19168E/0=16=E/0<[^09^19P8PCPeP3O3b7X4`X3^P=P8O2n2001000000120000000b<b?b9b>b5b=b6CTE~ELWGXIBWJXL9XM9o"). Qed.

  (* [comment removed for export] *)
  Lemma wr_dst : forall k j m,
      (0 <= j)%Z -> (j + Z.of_nat m <= n)%Z ->
      store_ok ASEGS (memk k) (at_ dst j) m = true.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemcpyBase ()) ["MC"] "h04__x1h14__x2h21xh31Hh42H0h52H1h62Hah75Hlen0h87__arithh94__ffh:6__sat2h;6__sat3h<8__varmaph=5__with>4__x3h?1ah@4cstrhA5cstr0hB1zhC2z1hD2HjhE2HmhF1jhG1khH1mhI1yp;1p;2p;3p;<p;4p;6p;;p;7p;8g001kR0j13Tg00];j22Tg00:Jj20Tg004_j15Tg005Dj1ATg005bj1YTg006Ej2RTg001KR1j1=Tg00X4j3MTg00dOj2ITg00;@j1>Tg00<Fj2FTg002hj31j1CTg002Kj2DTg006ej2]Tg007Hj3[Tg003`j29Tg004:l<WTg007ej4VTg008Lj1?Tg0091j2QTg009Sj26Tg009oR2j27Tg00:fj2OTg00;^j2NTg00<cj3LTg00ALj1KTg00BLj1JTg00Blj2<Tg00CJj1HTg00Chj4BTg00DFj1GTg00Ddj1PTg00F2j2:Tg00^nj3STg00EOj2TTg00lPj3UTg00FUj4;Tg00G@j1hTg00Hjj2gTg00ILj2fTg00J8j3eTg00JWj4dTg000mj6@Tg00^Ij1\Tg018;l;^Tg00ZDj1_Tg00e9j2`Tg019;j4aTg00L4l<bTg00LYj7ZTg00Maj8cTg00OoR3f0R4'0p=4g00NER5g00NcR6P5P5P1f4R1P0f3R7g00OBf2R8f1R9P4M<bp=XP9g00PMR:g00PlR;P;g00QLR<P4g00QlFZp=8P7P:P;P;P<P8P9P4Gcp=E%49%39R:,28p,1nR='0g011ZR>p,4mem0p,3dstR?g00RLR@#5RA#5#5RB#A#YRCp,2bsRD'RRE%=1=MCDP7P8P5P=%5B#5#5RB#ARD/I?RC/24%>ARF%>BRB'FRG'0XB5%==RH916E%3ERI1D3=RJ515RKP6P5%C6P0%C5%34915:A16941]943[XI6X26PEPI195IPH1D34X25RHP=O1P4X25PHP=P=195=DXM<Wp,4HlenCVRHPK%?ERE%4IR:%?1R0%31#4RL1Q3=RM163=A15J='710=3A15J3'7'ORNPJP51NFBRO163F%4B163G[[RP%4FRQg00S1RRALFB9UW6RB%4G\R^6QRQp,2HnRR%4=RS16=GRT'7RUP2PSPT12C=/0GP4g00SMRV#KRW%JVRVP51<58RXP9%H5CB%G5RY%P5RZP51:5@1:5A5S5RAg01001T5F=U5DRDC;,8Z%h;R;P5PAg00UDRFPDC;,8ZCE1gZ<R<P4P8g00VRRDg00W2R['91f48=1D[dAe539CdR3b9b<b=X05X151249R\/6G1298R]/0G[^05^15P4P=PCp,4HnwdO3b8X4TX3SP9P4O2n2001000000120000000b?b:b;bCb5bAb@b7PIg01:;RCE@p,4HdstP9P5P=%37,21/04XB5PHPKPEP:P0PLPMPNPJP5POPPPBPQPRPUP2PSPTf<f;#3'2/0=P4PWPVP5PXP91<57CBPYPZP5PAPF%\@,:5C;,8ZRZP;PZCEP<P3b9b<b=X05X15X>510\810]7[^05^15^>5P4P=f?#3f@f=O4b8X4TX3SP9P4O2n2001000000120000000b?b:b;bCb5bAb@b7PIPCE@M;^P>%_11`?7P8Ca=1D[eWEWDXH6XF5XG5o"). Qed.

  (* [comment removed for export] *)
  Lemma memk_extend : forall k l m,
      (0 <= k)%Z -> (k + Z.of_nat m <= n)%Z -> l = sb_ k m ->
      wbytes (memk k) (at_ dst k) l = memk (k + Z.of_nat m).
  Proof.
    intros k l m Hk Hm ->. unfold memk, sb_.
    replace (at_ dst k) with (at_ dst (Z.of_nat (Z.to_nat k))) by (f_equal; lia).
    rewrite wbytes_extend' by (rewrite Hlen; lia). f_equal. f_equal. lia.
  Qed.

  Lemma memk_extend1 : forall k (b : byte),
      (0 <= k)%Z -> (k + 1 <= n)%Z -> b = b_ k ->
      wbytes (memk k) (at_ dst k) [b] = memk (k + 1).
  Proof.
    intros k b Hk H1 ->.
    replace (k + 1)%Z with (k + Z.of_nat 1)%Z by lia.
    rewrite <- (memk_extend k (sb_ k 1) 1); try lia; [|reflexivity].
    unfold sb_, b_. rewrite sub_nth by (rewrite Hlen; lia). reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma sb4_split : forall j (q : nat), (0 <= j)%Z -> (q <= 4)%nat ->
      sb_ j 4 = sb_ j q ++ sb_ (j + Z.of_nat q) (4 - q).
  Proof.
    intros j q Hj Hq. unfold sb_.
    replace 4%nat with (q + (4 - q))%nat at 1 by lia. rewrite sub_split. f_equal. f_equal. lia.
  Qed.

  Lemma skipn_sb : forall j (q m : nat), (0 <= j)%Z ->
      skipn q (sb_ j m) = sb_ (j + Z.of_nat q) (m - q).
  Proof.
    intros j q m Hj. unfold sb_, sub. rewrite skipn_firstn_comm, <- skipn_add. f_equal. f_equal. lia.
  Qed.

  Lemma firstn_sb : forall j (q m : nat), (q <= m)%nat -> firstn q (sb_ j m) = sb_ j q.
  Proof. intros j q m Hq. unfold sb_, sub. rewrite firstn_firstn. f_equal. lia. Qed.

  (* [comment removed for export] *)
  Lemma merge_sb : forall j (q : nat) (v : word),
      (0 <= j)%Z -> (j + 8 <= n)%Z -> (1 <= q <= 3)%nat ->
      v = v_or (v_slli (LWv (sb_ (j + 4) 4)) (32 - 8 * Z.of_nat q)) (v_srliw (LWv (sb_ j 4)) (8 * Z.of_nat q)) ->
      word_to_le_bytes 4 v = sb_ (j + Z.of_nat q) 4.
  Proof.
    intros j q v Hj H8 Hq Hv.
    rewrite (sw_bytes_merge (sb_ j 4) (sb_ (j + 4) 4) q v); try (apply sb_len; lia); try assumption.
    rewrite skipn_sb, firstn_sb by lia.
    rewrite (sb4_split (j + Z.of_nat q) (4 - q)) by lia.
    f_equal. f_equal; lia.
  Qed.

  Lemma merge_sb' : forall j (q : nat) (v : word),
      (0 <= j)%Z -> (j + 8 <= n)%Z -> (1 <= q <= 3)%nat ->
      v = v_or (v_srliw (LWv (sb_ j 4)) (8 * Z.of_nat q)) (v_slli (LWv (sb_ (j + 4) 4)) (32 - 8 * Z.of_nat q)) ->
      word_to_le_bytes 4 v = sb_ (j + Z.of_nat q) 4.
  Proof.
    intros j q v Hj H8 Hq ->. apply merge_sb; try lia. unfold v_or. f_equal. apply Z.lor_comm.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma mc_lbu : forall regs pc rom w rd rs (imm : bv 12) k j0 j,
    fetch_word ASEGS pc = Some w -> is_ecall w = false ->
    decode_any w = Some (Load SZ1 false rd rs imm, 4%Z) ->
    getr regs rs = at_ src j0 -> (j0 + bv_signed imm = j)%Z ->
    (0 <= k <= n)%Z -> (0 <= j)%Z -> (j + 1 <= n)%Z ->
    RiscvSemantics.step ASEGS (mkst regs pc (memk k) rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (LBv (b_ j))) (v_addi pc 4) (memk k) rom).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemcpyBase ()) ["MC"] "h04__x1h14__x2h23romh31Hh42H0h52H2h65Hlen0h77__arithh84__ffh96__sat3h:6__sat4h;8__varmaph<5__with=1ah>4cstrh?1xh@2z2hA2HahB1bhC2HdhD2HehE2HfhF2HjhG3Hj0hH3Hj1hI2HkhJ3HrshK3immhL1jhM2j0hN1khO2pchP2rdhQ4regshR2rshS1whT1yhU1zp;1p;2p;3p;5p;4p;<p;7p;6p;?p;8g004_j13Tg00^Ij1PTg005Dj17Tg005bj16Tg01V@j2xTg00WRj19Tg01Vlj2dTg00gVj2BTg002hj30j1ETg01Wnj1[Tg01Xnj2XTg01YNj1VTg01Z?j5QTg00;@j1;Tg01Zkj4rTg01[Kj2MTg00e9j28Tg01\@j2ATg00];j25Tg00:Jj22Tg009oR0j24Tg00ZDj1NTg013Mj1OTg00BLj1ITg01\hj2HTg00>Fj1\Tg00ejj4=Tg00ALj1GTg00Alj3ZTg006Ej2YTg001KR1j1WTg001kR2j1<Tg002Kj2FTg006ej2UTg007Hj3TTg003`j2DTg004:l<STg007ej4wTg008Lj1vTg0091j2uTg009Sj2:Tg00:fj2qTg00;^j2pTg00<Fj2oTg00<cj3nTg00Blj2JTg00CJj1jTg00Chj4iTg00DFj1hTg00Ddj1fTg00EOj2LTg00F2j2KTg00M=j7eTg00G@j1cTg00Hjj2gTg00ILj2bTg00J8j3kTg00JWj4lTg00^nj3aTg01]_j5mTg000mj6>Tg01^]j3`Tg01_Rl?_Tg00L4l<^Tg00FUj4]Tg00LYj7sTg00Maj8tTg00OoR3f0R4'2p=1g00NER5g00NcR6P5P5P1f4R1P2f3R7g00OBf2R8f1R9P4M<^p=RP5P9g00UDP4C]p=@P9g00PMR:g00PlR;P;g00QLR<P4g00QlFsp=?P7P:P;P;P<P8P9P4Gtp=Cg00RLR=#3R>#P#7R?%3>R@#3RA#3#3RB#3RC#7#6RD'x%7A#6RA#9RE\D%7B#6RB%6?R?%P=#3#3#7RF#6%9Bg011ZRGf8RH'df6RI,BB30g00VRRBf7RJ#[g01`KRK30g01`kRL/X5RM#9%VHPLP5g01aWPKPJPIf5RKDQ%;@Cr,BM30f<RM/MJp,3srcR@/8150D1AFJ,5K=051%1Jp,1nRL,2J'4%1I%;=RN,5J/2Lg01bCPGfAROf@RPf:RQ#Nf?RRf>RSf=RTPMf;RU%OHPJPIPKPDf9RK,8@RI%IARJ#9RVPG%NURW1AFM,H4g00T9#\RXC=%OK%GA5ZA,BJRJ30XBDPD1AFURU,5KRF,8@PGPWP4PXC==0VJXBDP5PHPGPW18@4PXC==0VJXU5PQPHp,2bs,YARA%WLRH506%<ARQ1F3LRJ505RVP6P5%E6P2%E5%<9%<4505A06941U943TXT6X?6PAPQ1D5QPH1F34X?5RHPLO1P4X?5PHPLPL1D5LDRM<Sp,4HlenCwRHPV%vARA%1QRQ1u3LR61:3LA05JL'412L3A05J3'4'qR2PJP5%;>RX%;CRC'pRW1:3X%1C1oXCRG,:3[[RY%1XRZg00S1R[AnXC9UWARC%1G\[^AZRZp,2HnR[%1LRX1:LGRG'4R\P0PXPGfBR]#112]L'4P4fJfKO1R]PEg00SMR^#GR_%I^R^P51J58P9%j5CiR`%h5Ra%f5RbPbP:P;P;P<1L531K5=R='@,?bR:1K5>R>,@=,?bFeRc%c;R;PcCC1gb<R<P4P8g00W2Rc,DB1b48=0BcdAk539ClR3b8b;b<X05X15%14Rc1249'4%19RB1298'4[^05^15P4PLfGPRO3b7b2X4GX3XP9P4O2n2001000000120000000b=b9b:b@b5b>b6PHPVPAPQP6P2PJP5PWPYPCPZP[P\P0PXPG%1PP4P]PEP_P^1J59PaPbP:P;P:CCP<P3b8b;b<X05PB\c^05P4fERcPSO2b7b2X4GX3XP9P4O2n2001000000120000000b=b9b:b@b5b>b6PHPVPAPQP6P2PJP5PWPYPCPZP[P\P0PXPG15PN/2LP4P]PEP_P^P`PaPb1L5N9a5=/@>,?bRbP;PbCCP<P3b8b;b<X05X15154N/29159N/28[^05^15P4PLPcPTO3b7b2X4GX3XP9P4O2n2001000000120000000b=b9b:b@b5b>b6DmPFP7E>1HIUA`@KUE>1MOMP1E>M?_WHWGWIWFWJWCWDWEXL5XM5XN5WKXR?WPWSW2XODWQo"). Qed.

  (* [comment removed for export] *)
  Lemma mc_lw : forall regs pc rom w rd rs (imm : bv 12) k j0 j,
    fetch_word ASEGS pc = Some w -> is_ecall w = false ->
    decode_any w = Some (Load SZ4 true rd rs imm, 4%Z) ->
    getr regs rs = at_ src j0 -> (j0 + bv_signed imm = j)%Z ->
    (0 <= k <= n)%Z -> (0 <= j)%Z -> (j + 4 <= n)%Z ->
    RiscvSemantics.step ASEGS (mkst regs pc (memk k) rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (LWv (sb_ j 4))) (v_addi pc 4) (memk k) rom).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemcpyBase ()) ["MC"] "h04__x1h11xh24__x2h33romh41Hh52H0h62H5h75Hlen0h87__arithh94__ffh:6__sat6h;6__sat7h<8__varmaph=5__with>1ah?4cstrh@2z5hA2HahB1bhC1yhD2HdhE2HehF2HfhG2HjhH3Hj0hI3Hj4hJ2HkhK3HrshL3immhM1jhN2j0hO1khP1mhQ1nhR2pchS2rdhT4regshU2rshV1whW1zp&0p;1p;2p;3p;5p;4p;<p;7p;6p;Ap;8p;Bg004_j14Tg00^Ij1STg005Dj18Tg005bj17Tg01V@k205Tg00WRj1<Tg01Vlj2jTg00gVj2DTg002hj30j1GTg01Wnj1\Tg01Xnj2ZTg01YNj1XTg01Z?j5UTg00;@j1ETg01Zkj4~Tg01[Kj2PTg00e9j29Tg01\@j2?Tg00];R0j23Tg00:JR1j21Tg009oR2j25Tg00ZDj1NTg00>Fj1;Tg00`Pj2JTg01cHj1`Tg014Fj2^Tg00BLj1RTg01\hj2ITg00ejj4CTg006Ej2[Tg001KR3j1YTg001kR4j1:Tg002Kj2HTg006ej2WTg007Hj3VTg004:l<FTg007ek404Tg008Lk103Tg0091k202Tg009Sj2=Tg00:fj2}Tg00;^j2{Tg00<Fj2vTg00<cj3uTg00ALj1tTg00Blj2OTg00CJj1qTg00Chj4pTg00DFj1oTg00Ddj1nTg00EOj2MTg00F2j2LTg00M=j7iTg00G@j1hTg00Hjj2gTg003`j2KTg00ILj2kTg00J8j3fTg00JWj4lTg003Bj1mTg00hVj4eTg00^nj3bTg00KIj4rTg016\j6sTg000mj6>Tg01^]j3aTg00dOj2wTg01RBj4_Tg01dEj2xTg01e@j4yTg01e\lAzTg00L4l<QTg00FUj4|Tg00LYj7]Tg00Mak800Tg00aJmB01Tg00OoR5f0R6'1p=2g00NER7/K6p=6P7g00NcR8P7P7P3f4R3P4f3R9g00OBf2R:f1R;P6M<Qp=TP7P;g00UDP6C|p=@P;g00PMR<g00PlR=P=g00QLR>P6g00QlF]p=BP9P<P=P=P>P:P;P6L00p=AP8P7P7P7P4P4f5R?P3P9P:P;P6M<Qp=dP7P7P7P7P7P7P0P6P;P:P0P9P3P?f6R0f7R@f8RAf9RBNB01p=cg00RLRC#4RD#S#8RE%4DRF#4RG#4#4RH#4RI#8RJ#7RK+05%8G#7RG#<RL\K%8H#7RH%7ERE%SC#4#4#8RM#7%<Hg011ZRN/jA1DH030g00VRRH%\@g01`K30g01`kRO/Z7RP#<%XAPOP7g01fTg00W2ROP@P0P?DU%EFRFC~,DP30f<RP/P@p,3srcRQ/9350K1?M@,3?=073%2@p,1nRR,1@'5%2013@F/1Rg01bCPNfARSf@RTf:RU#Nf?RVf>RWf=RXPPf;RYg00T9#;#;#;#;RZ,JAR[%`[R\,^JR]P@P0P?PK19QBR?%RGR0#<R@PN%NYR^1?MP,I6PZCC1JBZ,D0R030XBKPK1?MYRY,3BRM,9QPNP^P6PZCC=0@0XBKP7PAPNP^19Q6PZCC=0@0XW7PUPAPZp,2bs,[GRG%YRRU508%:GR01H5RR@507R^P8P7%G8P4%G7%:;%:6R4507A08;61W;63VXC8X18PGP0%60PU1H56X17RUPRO1P6X17RNPUPRPR%6RRUDTM<Fp,4HlenH04R_P^&03GRG%20R02025RR`1=5RA07@R'511R5A07@5'5'}RaP@P7%EDRb%EIRI'{Rc1=5b%2I1vbIRd,=5[[Re%2bRfg00S1RgAubI;UWARI%2d\g^AfRfp,2HnRg%2RRb1=RdRd'5RhP2PbPdfBRi#211iR'5P6fJfKO1RiPLg00SMRj#tRk%RjRjP71O7:P;%q7CpRl%o7Rm%n7RnPnP<P=P=P>1M751L7CRC'@,BnR<1L7DRD,@C,BnFiRo%h=R=PoCA1gn>R>P6P:1KHO1k6:=0HOdAf75;ClR5b9b<b=X07X27%26RO116;'5%2;RH11;:'5[^07^27P6PRfGPVO3b8b3X5dX4bP;P6O2n2001000000120000000b>b:b;b@b6b?b7P_P^PGP0P`PaP@P7PcPePIPfPgPhP2PbPd%2TP6PiPLPkPj1O7;PmPnP<P=P<CAP>P5b9b<b=X07PH\O^07P6fEROPWO2b8b3X5dX4bP;P6O2n2001000000120000000b>b:b;b@b6b?b7RW%:ZRH,3AR</1R13AFRV/1RP7P7P1PNP111;6#mXC7X17P<PVPNPNPNP7P7g012i13;6Ce#6XP7XQ7PAPA%6APHPFPNPN%64X18PZPF%6FEdM:cPRPRPUM<FP_P^PGP0P`PaP@P7PcPePIPfPgPhP2PbPd13TF/1RP6PiPLPkPjPlPmPn1M7F9b7C/@D,BnRnP=PnCAP>P5b9b<b=X07X27136F/1;13;F/1:[^07^27P6PRPOPXO3b8b3X5dX4bP;P6O2n2001000000120000000b>b:b;b@b6b?b7CrR6EsPMP9E>1I?YAaQBYE>1PSPP3E>P71wJ]P\PAPZPWP6C_,x[CyMAzWIWHWJWGWKWDWEWFXM7XN7XO7WLXUEWSWVW3XRKWTo"). Qed.

  (* [comment removed for export] *)
  Lemma mc_sb : forall regs pc rom w rs1 rs2 (imm : bv 12) k k0 (v : word),
    fetch_word ASEGS pc = Some w -> is_ecall w = false ->
    decode_any w = Some (Store SZ1 rs1 rs2 imm, 4%Z) ->
    getr regs rs1 = at_ dst k0 -> (k0 + bv_signed imm = k)%Z ->
    getr regs rs2 = v -> Z_to_bv 8 (bv_unsigned v) = b_ k ->
    (0 <= k)%Z -> (k + 1 <= n)%Z ->
    RiscvSemantics.step ASEGS (mkst regs pc (memk k) rom) =
    MachineOk (mkst regs (v_addi pc 4) (memk (k + 1)) rom).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemcpyBase ()) ["MC"] "h01xh14__x1h23romh31Hh42H0h52H3h62Hah75Hlen0h87__arithh94__ffh:6__sat4h;6__sat5h<8__varmaph=5__with>4__x2h?1ah@1bhA4cstrhB1yhC2z3hD2HbhE2HdhF2HehG2HfhH2HkhI3Hk0hJ3Hk1hK4Hrs1hL4Hrs2hM3immhN1khO2k0hP1mhQ1nhR1ohS2pchT4regshU3rs1hV3rs2hW1vhX1whY1zp&0p;1p;2p;3p;4p;5p;6p;<p;Dp;7p;8p;Bg004_j14Tg00^Ij1RTg005Dj17Tg005bj18Tg01V@k206Tg00WRj1CTg01Vlj2lTg00gVj2MTg002hj30j1PTg01Wnj1]Tg01Xnj2ZTg01YNj1XTg01g@j4UTg00;@j1<Tg01Zkk404Tg01[Kj2ATg00e9j26Tg01\@j2@Tg00];R0j22Tg00dOj2kTg014Fj2hTg013Mj1DTg00:JR1j21Tg00ZDj1BTg00ALj1FTg00Alj3_Tg00XSj3^Tg01glj1\Tg01i4j5ETg01iij2[Tg01\hj2>Tg01jej2YTg003`j2;Tg000mj6=Tg01^]j3WTg00>Fj1VTg006Ej2TTg001KR2j1STg001kR3j1:Tg002Kj2QTg006ek205Tg007Hk303Tg004:l<NTg007ej4yTg008Lj1xTg0091j2sTg009Sj29Tg009oR4j2?Tg00:fj2rTg00;^j2qTg00<Fj2pTg00<cj3oTg00BLj1nTg00Blj2ITg00DFj1jTg00Ddj1iTg00EOj2GTg00F2j2HTg00FUj4JTg00G@j1gTg00Hjj2mTg00ILj2fTg00J8j3eTg00JWj4dTg003Bj1cTg00hVj4tTg00CJj1vTg00Chj4wTg00^nj3aTg00KIj4`Tg01kmj5zTg01ljlD{Tg01mdj5|Tg00Yhj6}Tg00L4l<OTg00LYj7~Tg00Mak800Tg00aJmB01Tg00OoR5f0R6'1p=3g00NER7/;6p=5P7g00NcR8P7P7P2f4R2P3f3R9g00OBf2R:f1R;P6M<Op>02P;g00PMR<g00PlR=P=g00QLR>P6g00QlF~p=LP9P<P=P=P>P:P;P6L00p=KP8P7P7P7P3P3f5R<P2P9P:P;P6M<Op=uP7P7P7P7P7P7P0P6P;P:P0P9P2P<f6R0f7R?f8R@f9RANB01p=bg00RLRB#4RC#R#7RD%4CRE#4RF#4#4RG#4RH#7RI#8RJ+06%7FRF#8RK#CRL\JRM%7G#8RG%8DRD%RB#4#4#7RN#8%CGg011ZRO/l@1MG030g00VRRG%]?g01`K30g01`kRP/Z7RQ#C%X@PPP7g01aWP?P0P<CU%<EREH04,MQ30f<RQ/A@p,3dstRP/6250J1@N?,2<=070f>RR/AA=0J<1kI0,hF%D@50K%3Af:RF%<BRI'2p,1nRS'1PMf;RT#BRU16PTRV%DTRW%FK5_K3^g01ngRX#\g01bCRYfCRZfBR[%BQfAR\DE,[OPYPZ1>[EP6P\DE,YX30XRMPYPOP[P\PUf@f?PRf=RUPQPVPAPWP@P?P0PJ16PFR01@NU,>616PQR?50JX@JPJ1@NQRQ,2FRN,6PA0J6?X@JP7PT16P6=0J?XY71;JVPNP2E=1>0QAWPFQE=1A[RP<E=P9P:PTPTg00T9#VR9p,2bs,TKR<%SSR[508%:<RQ1Q5SRF507RPP8P7%P8P3%P7%:;%:6R3507A08;6205;6403XB8X08P<PQ%5QP[1Q56X07R[PSO1P6X07R0P[PSPS%5SR[I02M<Np,4HlenCyR2PP%x<R<%3QRQ1s5SRN195SA07FS'?11S5A07F5'?'rRVPFP7%<CR?%<HRH'qR@195?%3H1p?HRA,95[[R\%3?ROg00S1RYAo?H;UW6RH%3A\Y^6OROp,2HnRY%3SR?19SARA'?RMP4P?PA%3ZP6fKfDO1RXPLg00SMRE#FR]%nERE1I7;%j7R^%i7R_P71G75g00UDR`1H7BRBCJ,L_Ra%g=R=PaCK1m_>R>P6P:g00W2Ra,;G1f6:=0GadAe75;CdR5b9b<b=X17%36%3;[^17P6fHRaPRO2b8b2X4AX3?P;P6O2n2001000000120000000b?b:b;bCb5bAb7RR%:9RG,2TRb/1S12TIRc/1SP7P7P1P0P111;6#cXB7X07PbPcP0P0P0P7P7g012i12;6Ct#5XP7XQ7PTPT%5TPGPIP0P0%53X08P9PI%5IEuM:bPSPSP[M<NP2PPP<PQPNPVPFP7P@P\PHPOPYPMP4P?PA12ZI/1SP6PXPLP]PEP71I7:P;%v7CwP^P_P71G7I9a7BP`1H7CCJ,L_R_P=P_CKP>P5b9b<b=X17X>7126I/1;12;I/1:[^17^>7P6PSPaPUO3b8b2X4AX3?P;P6O2n2001000000120000000b?b:b;bCb5bAb7R6C`DzMD{%BcPTPWPRP61;KWD|E}WJWIWDWLWHWKWEWFWGXWJXO7XN7WMXVDWUWXW2XSJWTo"). Qed.

  (* [comment removed for export] *)
  Lemma mc_sw : forall regs pc rom w rs1 rs2 (imm : bv 12) k k0 (v : word),
    fetch_word ASEGS pc = Some w -> is_ecall w = false ->
    decode_any w = Some (Store SZ4 rs1 rs2 imm, 4%Z) ->
    getr regs rs1 = at_ dst k0 -> (k0 + bv_signed imm = k)%Z ->
    getr regs rs2 = v -> word_to_le_bytes 4 v = sb_ k 4 ->
    (0 <= k)%Z -> (k + 4 <= n)%Z ->
    RiscvSemantics.step ASEGS (mkst regs pc (memk k) rom) =
    MachineOk (mkst regs (v_addi pc 4) (memk (k + 4)) rom).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemcpyBase ()) ["MC"] "h04__x1h11xh21Hh33romh42H0h52H5h65Hlen0h77__arithh84__ffh96__sat6h:6__sat7h;8__varmaph<5__with=1ah>4cstrh?1yh@2z5hA2HahB4__x2hC1bhD1zhE2HbhF2HdhG2HehH2HfhI2HkhJ3Hk0hK3Hk4hL4Hrs1hM4Hrs2hN3immhO1khP2k0hQ1lhR1mhS1nhT1ohU2pchV4regshW3rs1hX3rs2hY1vhZ1wp&0p;1p;2p;3p;4p;<p;5p;6p;Bp;7p;8g004_j16Tg00^Ij1[Tg005Dj19Tg005bj18Tg01V@k205Tg00WRj1HTg01Vlj2sTg00gVj2RTg002hj30j1ZTg01Wnj1fTg01Xnj2dTg01YNj1bTg01g@j4_Tg00;@j1KTg01Zkj4~Tg01[Kj2ITg00e9j27Tg01\@j2DTg00];R0j21Tg00BLj1TTg00>Fj1=Tg01Q:j2STg00`Pj2MTg00:JR1j22Tg001kR2j1:Tg003Bj1OTg00hVj4eTg004:l<@Tg006Ej2aTg001KR3j1`Tg002Kj2LTg006ej2^Tg007Hj3]Tg007ek404Tg008Lk103Tg0091k202Tg009Sj2?Tg009oR4j2JTg00:fj2}Tg00;^j2|Tg00<Fj2{Tg00<cj3zTg00ALj1wTg00Blj2VTg00DFj1vTg00Ddj1uTg00F2j2UTg00EOj2PTg00^nj3tTg00FUj4GTg00Hjj2rTg003`j2;Tg00ILj2qTg00J8j3pTg00JWj4oTg00KIj4XTg01glj1nTg00ZDj1>Tg01i4j5<Tg01iij2mTg01\hj2CTg01jej2ETg00XSj3QTg000mj6BTg01^]j3lTg00G@j1kTg00CJj1xTg00Chj4jTg01kmj5iTg01onlByTg00Yhj6ATg01<9j6hTg00L4l<WTg00aJlBgTg00LYk700Tg00Mak801Tg00NER5f1R6f0R730p=3g00OoR8/27p=41;57p=5g00NcR9P5P5P5P2P2f5R:f4R;f3R<f2R=P6P7M<Wp=cP5P5P5P5P5P5P0P7P6P=P0P<P;P:f6R0f7R>f8R?f9R@MBgp=NP5P9P5P5P3P;P2P<g00OBP=P6P7M<Wp=\P6g00PMR3g00PlRAPAg00QLRBP7g00QlK00p=FP<P3PAPAPBP=P6P7L01p=Yg00RLR3#6RC#[#9RD%6CRE#6RF#6#6RG#6RH#9#8RI+05%9F#8RF#HRJ\IRK%9G#8RG%8DRD%[3#6#6#9RL#8%HGg011ZRM/s?1RG030g00VRRG%f>g01`K30g01`kRN/d5RO#H%b?PNP5g01fTP>P0P:C_%KEREC~,RO30f<RO/I?p,3dstRN/7;50I1DL>,1:/30f>RP/I@=0I:%TFRQg00T9#=#=#=#=RR/S01M?R30%4@f:RS/1Ep,1nRT'2f;RU%:RRV'1RW11UERX'3RY13XXP5P5%Z5RZP7X15R[PZ1367#OX?5X15PWPXP[P[P[P5P5g012i1167Ce#5XR5XS5RWPUPU%5UPVPEP[P[%:7R\#5X19PRPE%5EEcR]M:NPXPX%5XM<@p,2bs,aFRF%`TRX509%:FR^1L8TR_'3R`P9P5%Z9P2PZ%:6/3\A09671^673]X?9X19PFP^%5^PX1L87X15RXPTO1P[PXPTPT%5TRXD\M<@p,4HlenH04R9P`&03FRF%4^R^2028TR\1?8T13_T'J12T8A05_8'J'}RZP_P5%KCR2%KHRH'|Ra1?82%4H1{2HRb,?8[[Rc%42Rdg00S1ReAz2H6UWARH%4b\e^AdRdp,2HnRe%4TR21?TbRb'JRfP4P2PbfCRg/1ERh/3hP7fKfDRhO1PJg00SMRi#wRj%TiRi1V56Rk%v5Rl%u5RmP51U53R31P5E5t5Rng00UkPnCG'F1rmBRBP7P=g00W2Ro,;G1q7==0GodAp586CoRob8b;b<X05117ERG/3G^05P7fHO1b7b3X4bX22P6P7O2n2001000000120000000b=b9b:b@b5b>b6CXPYP511OVRYg01ngRp#nRqg01bCRrPhPgf=Rs#>RtfBRuD<,mMRvPrPh1CgERw%>7PuD<,Ep30XD5PK%>ORx17NORy1MORRz3QPrPhPwP7PuD<,Ep90qvXTKPQ1SRSPrPhPw17NsRw=Qt7PuD<,Ep90qvXQQPrPMPgPuPxfAf@f?RxPPPsPyPSP@P?P>PI17NUR>1DLP,C7=0IwXCIPI1DLsRs,1URL,7NA0I7wXCIP5PO17N7=0IwXD51;IyPLP:EB1C>sAlNUsEB1IgxP0EBP;POPOPRP9P`PFP^P\PZP_P5PaPcPHPdPePfP4P2Pb%4hP7fLfEO1R;PJPjPiPkPlPmP51P58g00UDR8P3CG,FmR3%kARAP3CYPBPob8b;b<X05%47%46[^05P7fIR3PxO2b7b3X4bX22P6P7O2n2001000000120000000b=b9b:b@b5b>b6Rx12YT11OERk/2TP5P5P1P[P11267#OX?5X15PYPkP[P[P[PWPOPO%5OPVPEP]M:NPTPTPXM<@P9P`PFP^P\PZP_P5PaPcPHPdPePfP4P2Pb11hE/2TP7P;PJPjPiP51V5=P6%x5CjPlPmP5PnP81U5CCG,FmRmPAPmCYPBPob8b;b<X05XB512G6116E/2=[^05^B5P7PTP3PPO3b7b3X4bX22P6P7O2n2001000000120000000b=b9b:b@b5b>b6CXR6DiMByPzP<EA%>YPOPzPRPxP61;QzEhEAPkP7EAb2WKWJWEWMWIWLWFWGWHXYIXP5XO5WNXXDWWWZW3XUIWVo"). Qed.

  (* [comment removed for export] *)
  Lemma sw_val_plain : forall k, (0 <= k)%Z -> (k + 4 <= n)%Z ->
    word_to_le_bytes 4 (LWv (sb_ k 4)) = sb_ k 4.
  Proof. intros k Hk H4. apply sw_bytes_LWv. apply sb_len; lia. Qed.

  (* [comment removed for export] *)
  Lemma sb_val_plain : forall k, Z_to_bv 8 (bv_unsigned (LBv (b_ k))) = b_ k.
  Proof. intros k. apply sb_byte_LBv. Qed.

  Lemma sb_val_srli : forall j (q : nat), (0 <= j)%Z -> (j + 4 <= n)%Z -> (q <= 3)%nat ->
    Z_to_bv 8 (bv_unsigned (v_srli (LWv (sb_ j 4)) (8 * Z.of_nat q))) = b_ (j + Z.of_nat q).
  Proof.
    intros j q Hj H4 Hq. rewrite sb_byte_srli_LWv; [| apply sb_len; lia | exact Hq].
    unfold sb_, b_, sub.
    rewrite nth_firstn. replace (q <? 4)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
    rewrite nth_skipn. f_equal. lia.
  Qed.

  Lemma sb_val_word0 : forall j, (0 <= j)%Z -> (j + 4 <= n)%Z ->
    Z_to_bv 8 (bv_unsigned (LWv (sb_ j 4))) = b_ j.
  Proof.
    intros j Hj H4.
    pose proof (sb_val_srli j 0 Hj H4 ltac:(lia)) as E.
    rewrite Z.add_0_r in E. rewrite <- E. f_equal. f_equal.
    unfold v_srli. rewrite Z.mul_0_r, Z.shiftr_0_r. symmetry. apply Z_to_bv_bv_unsigned.
  Qed.

  (* [comment removed for export] *)
  Lemma merge_s16 : forall (v : word) j1 j2 k,
      v = v_or (v_slli (LWv (sb_ j2 4)) 16) (v_srliw (LWv (sb_ j1 4)) 16) ->
      (j2 = j1 + 4)%Z -> (k = j1 + 2)%Z -> (0 <= j1)%Z -> (j1 + 8 <= n)%Z ->
      word_to_le_bytes 4 v = sb_ k 4.
  Proof.
    intros v j1 j2 k -> -> -> Hj H8.
    replace (j1 + 2)%Z with (j1 + Z.of_nat 2)%Z by lia. apply merge_sb; try lia. reflexivity.
  Qed.

  Lemma merge_s8 : forall (v : word) j1 j2 k,
      v = v_or (v_slli (LWv (sb_ j2 4)) 24) (v_srliw (LWv (sb_ j1 4)) 8) ->
      (j2 = j1 + 4)%Z -> (k = j1 + 1)%Z -> (0 <= j1)%Z -> (j1 + 8 <= n)%Z ->
      word_to_le_bytes 4 v = sb_ k 4.
  Proof.
    intros v j1 j2 k -> -> -> Hj H8.
    replace (j1 + 1)%Z with (j1 + Z.of_nat 1)%Z by lia. apply merge_sb; try lia. reflexivity.
  Qed.

  Lemma merge_s24 : forall (v : word) j1 j2 k,
      v = v_or (v_slli (LWv (sb_ j2 4)) 8) (v_srliw (LWv (sb_ j1 4)) 24) ->
      (j2 = j1 + 4)%Z -> (k = j1 + 3)%Z -> (0 <= j1)%Z -> (j1 + 8 <= n)%Z ->
      word_to_le_bytes 4 v = sb_ k 4.
  Proof.
    intros v j1 j2 k -> -> -> Hj H8.
    replace (j1 + 3)%Z with (j1 + Z.of_nat 3)%Z by lia. apply merge_sb; try lia. reflexivity.
  Qed.

  Lemma sb_val_srli8 : forall j k, (0 <= j)%Z -> (j + 4 <= n)%Z -> (k = j + 1)%Z ->
    Z_to_bv 8 (bv_unsigned (v_srli (LWv (sb_ j 4)) 8)) = b_ k.
  Proof.
    intros j k Hj H4 ->. replace (j + 1)%Z with (j + Z.of_nat 1)%Z by lia.
    rewrite <- (sb_val_srli j 1) by lia. reflexivity.
  Qed.

  Lemma sb_val_srli16 : forall j k, (0 <= j)%Z -> (j + 4 <= n)%Z -> (k = j + 2)%Z ->
    Z_to_bv 8 (bv_unsigned (v_srli (LWv (sb_ j 4)) 16)) = b_ k.
  Proof.
    intros j k Hj H4 ->. replace (j + 2)%Z with (j + Z.of_nat 2)%Z by lia.
    rewrite <- (sb_val_srli j 2) by lia. reflexivity.
  Qed.

  Lemma sb_val_word0' : forall j k, (0 <= j)%Z -> (j + 4 <= n)%Z -> (k = j)%Z ->
    Z_to_bv 8 (bv_unsigned (LWv (sb_ j 4))) = b_ k.
  Proof. intros j k Hj H4 ->. apply sb_val_word0; lia. Qed.

End MC.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac rwH :=
  repeat match goal with
         | H : getr ?rg ?i = _ |- context [getr ?rg ?i] => rewrite !H
         end.

(* [comment removed for export] *)
Ltac unorm :=
  repeat match goal with
         | |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
             lazymatch z with context [Z_to_bv 64 _] => fail | _ => rewrite (u_Z2bv z) by lia end
         end.

(* [comment removed for export] *)
Ltac mnorm := gres; imm_norm; rewrite ?v_addi_0; rwH; rewrite ?at_addi; vals_lit.

(* [comment removed for export] *)
Ltac cond_lia :=
  rwH; unfold c_ltu, c_eq, bv_ltu, bv_eqb; imm_norm; unorm;
  first [ apply Z.ltb_lt | apply Z.ltb_ge | apply Z.eqb_eq | apply Z.eqb_neq ]; lia.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma u_andi : forall (x : word) imm, (0 <= imm < 2 ^ 64)%Z ->
  bv_unsigned (v_andi x imm) = Z.land (bv_unsigned x) imm.
Proof.
  intros x imm Hi. unfold v_andi. rewrite Z_to_bv_unsigned.
  replace (bv_wrap 64 imm) with imm by (symmetry; apply bv_wrap_small; change (bv_modulus 64) with (2^64)%Z; lia).
  apply bv_wrap_small. change (bv_modulus 64) with (2^64)%Z. apply Z_land_range; [apply u64_range|lia].
Qed.

Lemma land_3 : forall a, (0 <= a)%Z -> Z.land a 3 = (a mod 4)%Z.
Proof. intros a Ha. change 3%Z with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma land_1 : forall a, (0 <= a)%Z -> Z.land a 1 = (a mod 2)%Z.
Proof. intros a Ha. change 1%Z with (Z.ones 1). rewrite Z.land_ones by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma bits_lt32 : forall m, (0 <= m < 32)%Z ->
  (Z.land m 16 = 0 \/ Z.land m 16 = 16)%Z /\ (Z.land m 8 = 0 \/ Z.land m 8 = 8)%Z /\
  (Z.land m 4 = 0 \/ Z.land m 4 = 4)%Z /\ (Z.land m 2 = 0 \/ Z.land m 2 = 2)%Z /\
  (Z.land m 1 = 0 \/ Z.land m 1 = 1)%Z /\
  (m = Z.land m 16 + Z.land m 8 + Z.land m 4 + Z.land m 2 + Z.land m 1)%Z.
Proof.
  intros m Hm.
  assert (E : exists k : nat, m = Z.of_nat k /\ (k < 32)%nat).
  { exists (Z.to_nat m). split; lia. }
  destruct E as (k & -> & Hk).
  do 32 (destruct k as [|k]; [vm_compute; intuition lia|]). lia.
Qed.

Lemma at_mod4 : forall (a : word) d, (0 <= bv_unsigned a + d < 2^64)%Z ->
  ((bv_unsigned (at_ a d)) mod 4 = (bv_unsigned a + d) mod 4)%Z.
Proof. intros a d H. rewrite at_u by lia. reflexivity. Qed.
