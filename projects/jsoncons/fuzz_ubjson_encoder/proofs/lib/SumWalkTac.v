(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_SumWalkTac () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions;bv_unsignedK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltK47Corelib4Init9Datatypes3nat02C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z6moduloI47Corelib4Init5Logic2eq00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec9u64_rangeC13~~~I47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula03K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr07C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z9mod_smallC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=bytes_le_to_ZC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec:bytes_le_NC13~~~C47Corelib4Init5Logic8eq_ind_rC56Stdlib6ZArith6BinInt1Z2leK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00K47Corelib4Init9Datatypes3nat01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions8bv_swrapK46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z3oppC45stdpp9bitvector;definitions>bv_swrap_smallC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7StepTac6u_Z2bvC13~~~C35stdpp7tactics<f_equal_helpC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec4v_lwC13~~~C45stdpp9bitvector;definitions5bv_eqK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z03I47Corelib7Numbers7BinNums1N00C56Stdlib6ZArith6BinInt1Z3eqbC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec4c_eqC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec;bv_eqb_reflC13~~~I47Corelib4Init9Datatypes6option00C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega7EnvRing5PExpr03C45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedC47Corelib4Init5Logic6eq_indC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7rdn_extC13~~~K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega6VarMap1t03I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I47Corelib4Init9Datatypes3nat00K46Stdlib9micromega:ZMicromega;ZArithProof01".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bytes_le_to_Z_4 : forall v : word, (bv_unsigned v < 2^32)%Z ->
  bytes_le_to_Z (word_to_le_bytes 4 v) = bv_unsigned v.
Proof.
ltac2:(KReplay.run1 (kr_t_SumWalkTac ()) ["FPX_1"] "h02Hah14__p1h24__x1h31Hh42Hvh57__arithh64__ffh76__sat0h86__sat1h96__sat2h:6__sat3h;8__varmaph<5__with=1vh>1zp;1p;2p;3p;4p;6p;7p;8g0000j12Tg000Uj1@Tg0013j1ITg001Vj23Tg002@j15Tg002^j26Tg003;j21Tg003Wj14Tg0046j1FTg004Vj2ETg0053j2DTg005Sj3<Tg005mj1ATg007:j27Tg007Uj2?Tg008=j3=Tg008aj1WTg009Aj1VTg009aj2UTg00:?j1TTg00:]j1NTg00;Hj2;Tg00;kj2HTg00<Nj49Tg00=9j6GTg00=]j1JTg00>?j3KTg00>bj2CTg00?Dj2LTg00?^j2MTg00@Jj3BTg00@ij4OTg00A[j3PTg00B>j2QTg00CFj1RTg00DCj2STg00EQj6\Tg00Eoj2[Tg00FKj7ZTg00Foj7YTg00GSj8XTg00H7R0f0R1'[p=0f1R2g00HUR3g00I4R4P4g00ITR5P1g00J4FZp=:f2R6P3P4P4P5P2P1FYp=>f3R7P3P4P4P5P6P2P1GXp=8g00JTR8#2R9#2#2R:#2#2R;#2R<#@R=#I13=1%59R9%5;R>'6R?'1g00K9R@13=2RA%5:g00KW#4#4#4#4R:#F'E,69'D13=69<@1X>@%A2%0A%5<R<,69RB,1A'71?9>1109RC%0>110?[[%09RDg00L6REA=9>2UW0%0?\E^0D1?9<%0<110B[\CA=9<2VEX0D%0B\E^0Dp-0RDg00LRRE#W%VE1U@2%T@%N@REP@1;@0g00M>1H@8R8C9,:ER<PEP3P4P4P5P7EG5>E%J4R4PEP@P8g00Me1;@9%@;5K@C9,:ER;P4A>E<;C8C81CE5P1P6g00NLREg00NlR5'L1M16=<E5dAB@02COb6b;b<X2@W1%01/72112?%06116?'7[[^2@^1DP1f7,3=R=/1BP=f5f6O4b5b7b8b9b:b39PA?1Q:2#R1S:2E\W4W=o"). Qed.

Lemma v_lw_small : forall z, (0 <= z < 2147483648)%Z -> v_lw (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
ltac2:(KReplay.run1 (kr_t_SumWalkTac ()) ["FPX_1"] "h04__x1h14__p1h27__arithh34__ffh48__varmaph55__with62Hah71zh82Hzh96__sat0h:6__sat1p;1p;2p;3p;4p;6p;8p;7g0000j10Tg002@j18Tg003;j22Tg007:j27Tg000Uj1=Tg0013j1HTg00OLj1Ej2DTg001Vj2CTg00P2j2<Tg00?Dj2?Tg005Sj3;Tg008aj1ZTg009Aj1VTg009aj2UTg00:?j1TTg00:]j1QTg00;Hj29Tg00;kj2MTg00<Nj45Tg00=]j1GTg00PYj2FTg00>bj2ITg00?^j2JTg00@Jj3KTg00@ij4LTg00Q<j1BTg00Eoj2>Tg00QYj3NTg00=9j6ATg007Uj2OTg002^j2PTg008=j3@Tg00>?j3RTg00RFj3STg00EQj6]Tg00SOj8\Tg00Slj1[Tg00FKj7YTg00Foj7WTg00GSj8XTg00H7R0f0R1'>p=3%01#0#0#0p=1f1R2g00HUR3g00I4R4P4g00ITR5P1g00J4FYp=4f2R6P3P4P4P5P2P1FWp=6f3R7P3P4P4P5P6P2P1GXp=:g00K9R8%31R9g00JTR:#0R;#1R<#0R=#0#1#1#1#1#1#1#8R>,21R?'7R@P8%==RA#HRB%EARCPC%=<R<1DA2RD,CARE'<P2PB\8/?CP8P21<<1=;86X78g00LRRC#ZRF%VCRC1U82RG%T8RH%Q8RIP81980g00M>RJ1M8:R:C5,4IRKP8P:g00MeRL198>RMC5,4IRN56I%G4ROP81F8MPJP:C5,4I=6INC:1II5RJP1P6g00NLRMg00NlRP'?1J16=;MPdAK802CLRPb3b4b5X08%B>/>2122>'7\@^08P1P6P2O2b29N<2PEp-0REPFPCPGPHPIPIP3P4P4P5P7EAR596IKPOPKC:PJPPb3b4b5X08W11792%32[^08^1EP1126>P6P2O3b2%8;R;%8=R='O120;%3=1P;=R6,20[[%3;R0g00L6R>A@;=2UW6%36\>^60PFPCPGPHPIA6I5NPOP8P:PL198;=R8AC5,4IC:PJPPb3b4b5X08X1E172?1226[^08^1EP1f4R1#3P1P7O3b2b9b:5S2E]G\%[D=;BDeW8W7o"). Qed.

(* [comment removed for export] *)
Lemma v_lw_m1 : v_lw (Z_to_bv 64 4294967295) = Z_to_bv 64 (-1).
Proof.
ltac2:(KReplay.run1 (kr_t_SumWalkTac ()) ["FPX_1"] "h02b1h12b2h21nh31Hp;1p;3p;2g0013j15Tg005Sj33Tg001Vj22Tg00U4j38Tg0000j14Tg000Uj1<Tg00UXj10Tg002@j16Tg00OLj27Tg00Slj19Tg00V=j1>Tg00?Dj2=Tf0R0#0#0p=;%00#0#0#0p=:%00#0#0#0#0#0#0#0p=1g00V[R1%50R2f1R3#5R4g007:f2R5#5?330g00K9R6f3R7/25127333R8[12531250536%57?353[R9f4#5?375\8A8530P0n2001000000120000000W1W0W2P9^14^02^21P0g00JTR0#4#4#4#4#4#4#<R1%00#;#:#1#1#1R2#6,71#9R4%>0,71R0%12#1#1#1#6,=612141210536dO4b3o"). Qed.

Lemma c_eq_Z : forall a b : Z, (0 <= a < 2^64)%Z -> (0 <= b < 2^64)%Z ->
  c_eq (Z_to_bv 64 a) (Z_to_bv 64 b) = Z.eqb a b.
Proof.
ltac2:(KReplay.run1 (kr_t_SumWalkTac ()) ["FPX_1"] "h07__arithh14__p1h26__sat0h36__sat1h44__x1h52Hah64__ffh78__varmaph85__with91zh:2Hbh;1ah<1bp;1p;2p;3p;4p;6p;7p;8g0000j12Tg002@j1<Tg002^j2DTg003;j21Tg007:j25Tg000Uj1LTg00OLj28Tg001Vj2?Tg00W9j23Tg005Sj34Tg00?Dj2@Tg007Uj2ATg008=j3VTg008aj1UTg009Aj1TTg009aj2OTg00:?j1NTg00:]j1MTg00;Hj2=Tg00;kj2KTg00<Nj46Tg00=9j6GTg00=]j1FTg00>bj2HTg00?^j2ETg00@Jj3ITg00@ij4JTg00>?j3CTg00RFj37Tg00EQj6>Tg00WVj2BTg00Eoj2PTg00FKj7QTg00Foj7RTg00GSj8STg00H7R0f0R1'Pp=0f1R2g00HUR3g00I4R4P4g00ITR5P1g00J4FQp=;f2R6P3P4P4P5P2P1FRp=:f3R7P3P4P4P5P6P2P1GSp=9g00K9R8%02R9g00JTR:#2R;#<R<%2;#2#2#2#2R;#<R='DR>,12R?'5R@P8P7g00NLRA%L;R;18;7RB'?RC,31f4RD/37RE34X98P8P613D1=4AEX981376RE,@A18;6RF,?;1A<=RG110<%0=110>[[RH%0<RIg00L6RJAV<=2UW5R=%0>\J^5IRIp-0RJg00LRRK#URL%TKRK1O82RM%N8RN%M8ROP81=80g00M>1K8:R:C6,;ORPPOP3P4P4P5P7EGR35:O%F4R4PPC91HO5R5P1P6g00NlRP,@A1E16=4APdAI802CJR0b6b7b8X48W1RP%01/52P9[^48^1JR9P1f5RQ/1>PQP7O3b0b2b3PGPHP=PIPLPKPMPNPOP8P:g00Me1=8<=C8;C6,;OR;9:O3P4P;C9P5P0b6b7b8X48X1JR0111>,52P?[^48^1JRJP1%0QPQP7O3b0b2b3576E>PCPGPHP=PIPPP9P1f6R9/1>P9PDO3b0b2b3PGPHP=PIP0PJP1%09P9PDO3b0b2b3577E>1BBF=4AEeX:@W5X<8W;o"). Qed.

Lemma c_eq_refl : forall x : word, c_eq x x = true.
Proof.
ltac2:(KReplay.run1 (kr_t_SumWalkTac ()) ["FPX_1"] "h01xp;1p;2p;3g0000j10Tg000Uj15Tg0013j12Tg00X^j21Tg00WVj24Tg005Sj33Tg00JT#0#0#0#0#0#0#5R0#2f0R1,10g00NL1411g00Nl33eW0o"). Qed.
End FPX_1.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac zsimp := rewrite ?length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ length]; u_norm.

(* [comment removed for export] *)
Ltac sok_stack SOK :=
  store_ok_peel;
  eapply (store_ok_sub _ _ _ _ 144%nat); [ | exact SOK | | ]; zsimp; lia.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac clear_disj := repeat match goal with H : _ \/ _ |- _ => clear H end.
Ltac lia_fast := first [ solve [ clear_disj; lia ] | lia ].
Ltac rdn_peel1 := rewrite rdn_wbytes_out by (zsimp; lia_fast).  (* [comment removed for export] *)
Ltac rdn_by H := repeat rdn_peel1; exact H.
(* [comment removed for export] *)
Ltac rdn_hyp :=
  match goal with
  | H : rdn _ _ ?a ?n = Some _ |- rdn _ _ ?a ?n = Some _ => exact H
  end.
Ltac rdn_solve :=
  lazymatch goal with
  | |- rdn _ (wbytes _ ?a _) ?b _ = _ =>
      tryif constr_eq a b then (apply rdn_wbytes_hit8; zsimp; lia)
      else (rdn_peel1; rdn_solve)
  | |- _ => rdn_hyp
  end.

(* [comment removed for export] *)
Ltac zbv_target x i :=
  lazymatch x with
  | Z_to_bv 64 (?a - ?b)%Z => let d := eval cbv in (b - i)%Z in constr:(Z_to_bv 64 (a - d))
  | Z_to_bv 64 (?a + ?b)%Z => let d := eval cbv in (b + i)%Z in constr:(Z_to_bv 64 (a + d))
  | Z_to_bv 64 ?a =>
      lazymatch i with
      | Zneg _ => let d := eval cbv in (- i)%Z in constr:(Z_to_bv 64 (a - d))
      | _ => constr:(Z_to_bv 64 (a + i))
      end
  | _ =>
      lazymatch i with
      | Zneg _ => let d := eval cbv in (- i)%Z in constr:(Z_to_bv 64 (bv_unsigned x - d))
      | _ => constr:(Z_to_bv 64 (bv_unsigned x + i))
      end
  end.

(* [comment removed for export] *)
Ltac addr_norm :=
  match goal with
  | |- context [v_addi ?x ?i] =>
      let e := constr:(v_addi x i) in
      tryif check_closed_term e then wlit_closed e
      else first
        [ rewrite (v_addi_0 x)
        | let t := zbv_target x i in
          replace e with t by (unfold v_addi; u_norm; first [reflexivity | f_equal; lia]) ]
  | _ => idtac
  end.

(* [comment removed for export] *)
Ltac sp_renorm :=
  match goal with
  | |- context [regupd _ 2 (v_addi ?x ?i)] =>
      let e := constr:(v_addi x i) in
      first
        [ rewrite (v_addi_0 x)
        | let t := zbv_target x i in
          replace e with t by (unfold v_addi; u_norm; first [reflexivity | f_equal; lia]) ]
  end.

(* [comment removed for export] *)
Ltac getr_hyps :=
  repeat match goal with
         | H : getr ?rs ?n = _ |- context [getr ?rs ?n] => rewrite H
         end.
Ltac addr_tac := getr_hyps; unfold v_addi; u_norm; first [reflexivity | f_equal; lia | apply bv_eq; u_norm; lia].
Ltac val_tac := first [reflexivity | assumption | symmetry; assumption].

(* [comment removed for export] *)
Ltac stepST F D aa vv oktac :=
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (Store SZ8 _ _ _, _) =>
        eapply step_sd_at with (a := aa) (v := vv);
        [ exact F | reflexivity | exact D | gres; imm_norm; addr_tac | gres; val_tac | oktac ]
    | decode_any _ = Some (Store SZ4 _ _ _, _) =>
        eapply step_sw_at with (a := aa) (v := vv);
        [ exact F | reflexivity | exact D | gres; imm_norm; addr_tac | gres; val_tac | oktac ]
    | decode_any _ = Some (Store SZ1 _ _ _, _) =>
        eapply MmapSim.step_sb_at with (a := aa) (v := vv);
        [ exact F | reflexivity | exact D | gres; imm_norm; addr_tac | gres; val_tac
        | reflexivity | oktac ]
    end
  | step_simpl ].

(* [comment removed for export] *)
Ltac stepLD F D bsv vv rdtac vtac :=
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (Load SZ8 _ _ _ _, _) => eapply step_ld with (bs := bsv) (v := vv)
    | decode_any _ = Some (Load SZ4 true _ _ _, _) => eapply step_lw with (bs := bsv) (v := vv)
    | decode_any _ = Some (Load SZ4 false _ _ _, _) => eapply step_lwu with (bs := bsv) (v := vv)
    end;
    [ exact F | reflexivity | exact D | gres; imm_norm; getr_hyps; rdtac | vtac ]
  | step_simpl ]; vnorm.

(* [comment removed for export] *)
Ltac stepLD8 F D vv := stepLD F D (word_to_le_bytes 8 vv) vv ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).

(* [comment removed for export] *)
Ltac stepLBU F D bb rdtac :=
  chain_step;
  [ reflexivity
  | eapply step_lbu with (b := bb);
    [ exact F | reflexivity | exact D | gres; imm_norm; getr_hyps; rdtac ]
  | step_simpl ]; vnorm.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac unorm :=
  repeat match goal with
  | |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
      lazymatch z with
      | context [bv_unsigned (Z_to_bv 64 _)] => fail
      | _ => rewrite (u_Z2bv z) by lia
      end
  end.

(* [comment removed for export] *)
Ltac addi_renorm :=
  match goal with
  | |- context [regupd _ _ (v_addi (Z_to_bv 64 ?x) ?i)] =>
      let t := zbv_target (Z_to_bv 64 x) i in
      replace (v_addi (Z_to_bv 64 x) i) with t by (unfold v_addi; unorm; f_equal; lia)
  end.
Section FPX_2. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)



Lemma rdn_img : forall segs mem (a : Z) (n : nat) (lo hi : Z),
  (forall i, (lo <= i < hi)%Z -> mem (Z_to_bv 64 i) = None) ->
  (lo <= a)%Z -> (a + Z.of_nat n <= hi)%Z -> (0 <= lo)%Z -> (hi < 2^64)%Z ->
  rdn segs mem (Z_to_bv 64 a) n = rdn segs (fun _ => None) (Z_to_bv 64 a) n.
Proof.
ltac2:(KReplay.run1 (kr_t_SumWalkTac ()) ["FPX_2"] "h04__x1h14__x2h27__arithh37__sat65h47__sat66h54__x3h64cstrh74__ffh88__varmaph95__with:2Hxh;1xh<2Hah=4__x4h>4__x5h?1zh@2H0hA3H64hB3HhihC4HimghD3HlohE1ahF2hihG1ihH2lohI3memhJ1nhK4segsp;1p;2p;3p;4p;6p;7p;8g009Aj1RTg0000j1;Tg000Uj1KTg0013j1ITg00Ymj1iTg00Eoj20Tg003;j22Tg007:j29Tg00OLj2<Tg00=]j1JTg005Sj3CTg0046j17Tg00ZOj24Tg002@j1PTg002^j2cTg00Zlj1GTg007Uj2[Tg008=j3ZTg003Wj1BTg00[Qj2=Tg00\:j2ATg008aj1YTg00\fj3@Tg009aj2?Tg00]Fj1XTg00:?j1WTg00:]j1VTg00;kj2>Tg00;Hj2HTg00>?j3TTg00]dj3FTg00>bj2STg00?Dj2UTg00?^j2hTg00@Jj3gTg00@ij4fTg001Vj28Tg00UXj1MTg00RFj3LTg00EQj6bj7\Tg00^Gj2aTg00_9j6]Tg00_Uj7^Tg00``j3_Tg00aIj4`Tg00<Nj4OTg00FKj7QTg00GSj8dTg00Foj7eTg00H7R0f0R1'0p=5g00K9R2f1R3;_1p=:P2f2R4P3P1C`p=6P2P3g00MeP1COp=DP3g00HUR5g00I4R6P6g00ITR7P1g00J4R8FQp=EP4P5P6P6P7P2P3g00M>P1COP8FQp=1f3R8P5P6P6P7P4P3P1Gdp=3P4P5P6P6P7P3P1Fep=Ng00ag#Rg00JTR5#;R9#;R:#;R;#;#;#;R<#KR=#IR>%K;#IR;#iR?];g00bf10411213'9f6R@1<=3O1%J;R;5C?[^G2f4RA,04f5RB%7A'4/04%5A%P9RC%P<R<'cRD,2Af:REf7RFf9RGP;V>f8RH,<=RIP2PH%7HRJ,41/0DX?2%GFRK%7F#5RL1[C<RM120C%5<120D[[RN%5CROg00L6RPAZC<3UW<R<%5D\P^<OROg00LRRPg00KWRQ#BRR#BRS,=2RT1=2R1=2QRQ':RR':RUg00cERV'A%YPRW3@RX%RPRY1?28RZ%X2R[764?63[%W2R\%V2R]1>2:R:1H2C=T2=RC'D,E]R^%J6R6P]1>25R_1>29R`5F2Ra=1]:P6A1]aCC3C31S]7R7P1P4g00NLRag00NlRb'U1h14=CabdAg203CfRbb7b8b9X02X12X52124D1434/081448Ra/0D[[^02^12^52P1PGf;Rc#7Rdf<RePAP@O5b2b3b4b618=IPKPLPMPNP<POPXPY1?24RX?63[P\P]1H20R0=1]`P6P]A1]`_P6A1]0_C3C3P7Pbb7b8b9X02X12RI%53Rf1043%54[[^02^12RgP1PEPePBPFO4b2b3b4b6PKPLPMPNP<PO%BSRS,=2RL/:U/AV=@PWPYA6Z8[?63XP\P]%M5,>2R591]0P6P]P^P6P]AF2_5=1]:P61D_C,E]C3C3C3P7Pbb7b8b9X02X12X52RC128DRD10aAPD[[\f^02^12^52RfP1PGPdPeP8PAP@O6b2b3b4b65LHEb1<=G,8=Rd18=1RD'014dJ,2D'9P2PE18=4RD,01%7ERd,41,2D'9f=RJP8O1=C?;]:X?218=3Ra,0E%7GR^,4E,2a'9P>1<=DPJP1O1=C?;X;>PFPD%GE%5dPMPNP<PO1:TQ,:L/AV%BS,=2/:R/AV=@PW5@PPY1?2A?64[1?2B?68[763P\P]A1]:`%M9,>29F2:R9,D`,E]5N]P6P]A1]95P6P]A1]_:P6A1]_`1D`5,E]5N]C3C3C3P7Pbb7b8b9X02X12X52X=2X>21083148A,23'914AB/08104B108A12AB'9[[[^02^12^52^=2^>2P1f>RB#7f?Pe18=@PJPAPGPEO8b2b3b4b6O2P41a=4E]W:1<=E,8=%GGR=%5^R^PMPNP<POPIPgP1PePBPFPGO4b2b3b4b6P=P^PMPNP<POPCPfP1Pc%7JPBP8P@PHO6b2b3b4b65LEP1F\W:X;>F^WAW@WBWDWCXF2XH2WJXE2WIWKo"). Qed.
End FPX_2.


(* [comment removed for export] *)
Ltac img_exists :=
  lazymatch goal with |- exists bs, ?l = Some bs =>
    let v := eval vm_compute in l in
    lazymatch v with Some ?bs => exists bs; vm_compute; reflexivity end
  end.

(* [comment removed for export] *)
Ltac enum_nat k N tac :=
  let rec go n := lazymatch n with
    | O => lia
    | S ?m => destruct k as [|k]; [tac | go m]
    end in go N.


(* [comment removed for export] *)
Ltac zaddr H :=
  repeat match type of H with
  | context [Z_to_bv 64 (?a + ?b)%Z] =>
      let c := eval cbv in (a + b)%Z in change (a + b)%Z with c in H
  end.

(* [comment removed for export] *)
Ltac zaddr_goal :=
  repeat match goal with
  | |- context [Z_to_bv 64 (?a + ?b)%Z] =>
      let c := eval cbv in (a + b)%Z in
      lazymatch c with
      | Zpos _ => change (a + b)%Z with c
      end
  end.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
