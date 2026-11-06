(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Export Tac Bytes.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_Walk () := "C47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes?RelationClasses?Equivalence_PERC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z;lt_ge_casesC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic2or00C56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3ltbI47Corelib4Init5Logic2eq00C47Corelib4Init5Logic3iffC56Stdlib6ZArith6BinInt1Z6ltb_ltC47Corelib7Classes9MorphismsNtrans_sym_co_inv_impl_morphismC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib4Bool4Bool>eq_true_iff_eqK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z9mod_smallC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums1Z03C56Stdlib6ZArith6BinInt1Z3mulK46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z7mod_addC47Corelib4Init5Logic6eq_indK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula09K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C47Corelib7Classes?RelationClasses>iff_TransitiveI47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205K47Corelib7Numbers7BinNums8positive03C47Corelib7Classes?RelationClasses?iff_equivalenceI47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic5False00C56Stdlib6ZArith6BinInt1Z8add_comm".
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma carry_sym : forall x y, (0 <= x < 2^64)%Z -> (0 <= y < 2^64)%Z ->
  ((x + y) mod 18446744073709551616 <? x)%Z = ((x + y) mod 18446744073709551616 <? y)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_Walk ()) [] "h06__sat1h14__p1h24__p2h34__x1h44__x2h57__arithh64__ffh76__sat0h88__varmaph95__with:5lemmah;1Hh<2Hah=2Hxh>2Hyh?1oh@1xhA1yhB1zp;1p;2p;3p;7p;4p;6p;9p;8p-1R0g0000R1p4p710p9P0g000\R2p4p710p9P0p1001NR3p4p710p9P0P3p4p7210p9P0P3p4p73110p9P0g001lR0p4p710p9g002fj18Tg003Kj1PTg003ij2TTg004Fj20Tg004bj23Tg005=j22Tg005Zj2_Tg006?j2<Tg006[R3j2XTg0075j2CTg007Uj21Tg0082j3>Tg008LR4j29TP1j2OTg008ej2?TP2j3fTg009Ej7JTg00:@j2aTg00:hj3`Tg00;Lj2^Tg00;mj2ITg00<Gj1\Tg00<gj1[Tg00=Gj2ZTg00=ej1YTg00>Cj4WTg00>aj1VTg00??j1UTg00?jj2@Tg00@Mj2ETg00A0j1STg00ARj3GTg00B5j2tTg00BWj2sTg00CCj3rTg00Cbj4qTg00DTj3HTg00E6j1FTg00EUj2ATg00F>j3NTg00Fgj2mTg00GSj3lTg00H3j1hTg00HQj3gTg00I4j3LTg00IWj6KTg00J5j1eTg00JSj2dTg00K0j3cTg00KSj4BTg00L>j6bTg00Lbj4iTg00MCj6jTP0l9kTg00M_j7QTg00NCj6nTg00Ngj7oTg00OKj7]Tg00Ooj8pTg00PSR0f0R2'<p=5g00Q1R1g00QQR57>2p=6p-0R6P4g00R1f5R7f4R8f3R9f2R:f1R;P2M9kp=Mg00RbR<P;g00S@P2CBp==P;g00SgR=g00TFR>P>g00TfR?P2g00UFR@FQp=;P;P=P>P>P?P2Enp=DP:P=P>P>P?P;P2Fop=:P:P=P>P>P?P<P;g00UfP2CBP@FQp=7P:P=P>P>P?P;P2F]p=RP9P=P>P>P?P:P;P2Gpp=4%5;R@g00VMRA#8RB#PRC%8B#8#8#8#8RD#PRE'TRF,0;RG'3RH129:RI/_F10IF1<FI'XP31289R3/0F1<F31278R3/CFRI/1711I85>1P2103FP<f6RI/27RJf7RK,12112I5>1XB<RL11JIRM11J7RN%6M10JI'912KIRM/1K#610MKROP211MI#6RPPP1O6PEMW:1?JI%6N10J7'9P6P4g00W29f64RNPOPP10MIP2FJW:1?J71aCERP100CRO%5E100F[RQ[RR%5CRSg00WdRTA`CE;UW<RE%5F\T^<SRSP;g00X@1^0C'IPOeO1ROPQg00XfRT#\RU%[TRVP<1Z<:P;%Y<RWCWRX%V<RY%U<RZ1@<0R[1E<BRB'=,;Z1DZ8R\5:ZR]%S>R^PZ1E<AR_,=[,;Z1DZ7R`5:ZRaP^AG<_BRb=7Z_A7ZbB5RZC4C41tZ?RcP2P:1I151s2:#6dAr<0;CqR5b6b8b9X3<X4<X16X2613@:13@812:9R@/0:10@9'9[[^3<^4<^16^26P2f:R1/0FRdf9Re/0FRfPeP1PKf8RgO6b5b0b7b0O2O23H1CJFRhPPPRPEPSPOPQg00YRRi#FRj#F,A<1A<j1A<i5N<5N<g00Z1'm=lTURTPVPXPYPZ1@<C%hD5g<RD97ZbRCP^PZP]P^PZPaP^1=[b,;Z=:ZCC4C4C4PcP5b6b8b9X3<X4<X16X26122;R;/0F%5:RC/3913C71298RC#510CF'3[[[^3<^4<^16^26P2PdPfPeP1P8PKPgO7b5b0b7b09LJFEKW;P2O11<F3P<%eARA/dFR3,2JRf/CFRdPLP<PfPL11fIRL11f7Ra%6L10fI'912M3RM/1K#610MKRLP211MI#6R]P]1O6]EMW:1?fI%6a10f7'9P6P4PNPLP]10MIP2FJW:1?f7PPPRPEPSPOPQPUPVPXPYPZA7ZBD9:Z\R\P^PZA7Z_D9:Z`R`P^1@<A=c<D9G<bRM=7Z_A7ZMB5RZC4C4PcP5b6b8b9X3<X4<X16X2613:G138G12@3R@/0:10@9'9[[^3<^4<^16^26P2%51R@%5eRGPeP1PKPgO6b5b0b7b0O2O23HPdPPPRPEPSPOPQPTPVPXPYPZ1=Db,;ZP^PZP\P^PZP`P^1=[M,;ZA7ZMD5:ZC4C4C4PcP5b6b8b9X3<X4<X16X261<F;10:FR:,39137:12C3R3#5103F'3[[[^3<^4<^16^26P2P@PGPeP1P8PKPgO7b5b0b7b09LfFEKPhPJPAPFPPPRPEPSPOPQPUPVPWPYPZP=P>P>P?P<PDg00Z]P[CB,;ZEbPcP5b6b8b9A><F0g00[D[P2b5b0b7b0CiEjW;P2O1n200100000021100011000b?X>HW=XA<X@<o"). Qed.
Lemma carry_sym' : forall x y, (0 <= x < 2^64)%Z -> (0 <= y < 2^64)%Z ->
  ((y + x) mod 18446744073709551616 <? x)%Z = ((x + y) mod 18446744073709551616 <? x)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_Walk ()) [] "h01xh11yh21zp;2p;1p;3p;6g006?j2?Tg002fj10Tg003Kj12Tg003ij2>Tg004Fj2:Tg004bj28Tg005=j23Tg0075j24Tg007Uj25Tg0082j39Tg00;mj2=Tg00[aj2<Tg00IWj6;Tf0R0#0#0#0#0p=6%00#0p=7%00#0#0#0#0#0#0#0p=1g00RbR1g00PSf1R2'?g00VM#0R3#2%03#6R3#2'>,:2'8R2P1f3R4f2R5'3R6g00Q1R7%73#1#1#1#1#1#1#1#2R3,40f4R0'51304/43/5039X211463/54,=713541<54E;V2UX11W0o"). Qed.

(* [comment removed for export] *)
Ltac zeq :=
  first
  [ reflexivity
  | lazymatch goal with
    (* [comment removed for export] *)
    | |- Z.lor ?a ?b = Z.lor _ _ => first [ f_equal; zeq | rewrite (Z.lor_comm a b); f_equal; zeq ]
    | |- Z.land ?a ?b = Z.land _ _ => first [ f_equal; zeq | rewrite (Z.land_comm a b); f_equal; zeq ]
    | |- Z.lxor ?a ?b = Z.lxor _ _ => first [ f_equal; zeq | rewrite (Z.lxor_comm a b); f_equal; zeq ]
    | |- Z.add ?a ?b = Z.add _ _ => first [ f_equal; zeq | rewrite (Z.add_comm a b); f_equal; zeq ]
    | |- Z.mul ?a ?b = Z.mul _ _ => first [ f_equal; zeq | rewrite (Z.mul_comm a b); f_equal; zeq ]
    (* [comment removed for export] *)
    | |- Z.modulo _ ?m = Z.modulo _ ?m => f_equal; zeq
    | |- Z.sub _ _ = Z.sub _ _ => f_equal; zeq
    | |- Z.shiftr _ _ = Z.shiftr _ _ => f_equal; zeq
    | |- Z.shiftl _ _ = Z.shiftl _ _ => f_equal; zeq
    | |- Z.b2z _ = Z.b2z _ => f_equal; zeq
    | |- (if ?c then _ else _) = (if ?d then _ else _) => replace d with c by (symmetry; zeq); f_equal; zeq
    (* [comment removed for export] *)
    | |- Z.ltb ?a ?b = Z.ltb ?c ?d =>
        first [ f_equal; zeq
              | unfold1 a; unfold1 b; unfold1 c; unfold1 d; zeq_boolarith ]
    | |- Z.eqb ?a ?b = Z.eqb ?c ?d =>
        first [ f_equal; zeq | rewrite (Z.eqb_sym a b); f_equal; zeq
              | unfold1 a; unfold1 b; unfold1 c; unfold1 d; zeq_boolarith ]
    | |- Z.leb ?a ?b = Z.leb ?c ?d =>
        first [ f_equal; zeq | unfold1 a; unfold1 b; unfold1 c; unfold1 d; zeq_boolarith ]
    | |- negb _ = negb _ => f_equal; zeq
    | |- @eq bool _ _ => zeq_boolarith
    end
  | lia ]
(* [comment removed for export] *)
with unfold1 a := try (is_var a; cbv delta [a])
(* [comment removed for export] *)
with zeq_boolarith :=
  apply eq_true_iff_eq;
  rewrite ?Bool.negb_true_iff, ?Z.ltb_lt, ?Z.eqb_eq, ?Z.leb_le, ?Z.ltb_ge, ?Z.eqb_neq, ?Z.leb_gt;
  zb_masks; pose_word_ranges; Z.div_mod_to_equations; lia.

(* [comment removed for export] *)
Ltac zeq_fast :=
  first
  [ reflexivity
  | lazymatch goal with
    | |- Z.lor ?a ?b = Z.lor _ _ => first [ f_equal; zeq_fast | rewrite (Z.lor_comm a b); f_equal; zeq_fast ]
    | |- Z.land ?a ?b = Z.land _ _ => first [ f_equal; zeq_fast | rewrite (Z.land_comm a b); f_equal; zeq_fast ]
    | |- Z.lxor ?a ?b = Z.lxor _ _ => first [ f_equal; zeq_fast | rewrite (Z.lxor_comm a b); f_equal; zeq_fast ]
    | |- Z.add ?a ?b = Z.add _ _ => first [ f_equal; zeq_fast | rewrite (Z.add_comm a b); f_equal; zeq_fast ]
    | |- Z.mul ?a ?b = Z.mul _ _ => first [ f_equal; zeq_fast | rewrite (Z.mul_comm a b); f_equal; zeq_fast ]
    | |- Z.modulo _ ?m = Z.modulo _ ?m => f_equal; zeq_fast
    | |- Z.sub _ _ = Z.sub _ _ => f_equal; zeq_fast
    | |- Z.shiftr _ _ = Z.shiftr _ _ => f_equal; zeq_fast
    | |- Z.shiftl _ _ = Z.shiftl _ _ => f_equal; zeq_fast
    | |- Z.b2z _ = Z.b2z _ => f_equal; zeq_fast
    | |- (if ?c then _ else _) = (if ?d then _ else _) => replace d with c by (symmetry; zeq_fast); f_equal; zeq_fast
    | |- Z.ltb ?a ?b = Z.ltb ?c ?d =>
        first [ f_equal; zeq_fast
              | unfold1 a; unfold1 b; unfold1 c; unfold1 d; zeq_boolarith_fast ]
    | |- Z.eqb ?a ?b = Z.eqb ?c ?d =>
        first [ f_equal; zeq_fast | rewrite (Z.eqb_sym a b); f_equal; zeq_fast
              | unfold1 a; unfold1 b; unfold1 c; unfold1 d; zeq_boolarith_fast ]
    | |- Z.leb ?a ?b = Z.leb ?c ?d =>
        first [ f_equal; zeq_fast | unfold1 a; unfold1 b; unfold1 c; unfold1 d; zeq_boolarith_fast ]
    | |- negb _ = negb _ => f_equal; zeq_fast
    | |- @eq bool _ _ => zeq_boolarith_fast
    end
  | slim; lia ]
with zeq_boolarith_fast :=
  apply eq_true_iff_eq;
  rewrite ?Bool.negb_true_iff, ?Z.ltb_lt, ?Z.eqb_eq, ?Z.leb_le, ?Z.ltb_ge, ?Z.eqb_neq, ?Z.leb_gt;
  slim; zb_masks; pose_word_ranges; Z.div_mod_to_equations; lia.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac getreg n :=
  lazymatch goal with
  | |- evt _ _ (MS ?R _ _ _ _ _ _) =>
      let p := eval vm_compute in (bv_key (Z_to_bv 5 n)) in
      let v := eval cbv beta iota delta [tget mkR] in (tget p R) in
      lazymatch v with
      | Some ?w => w
      | _ => fail "getreg: register" n "not concrete"
      end
  end.

(* [comment removed for export] *)
Ltac name_as_tac X e :=
  set (X := e);
  let RX := fresh "R" X in
  first [ assert (RX : (0 <= X < 18446744073709551616)%Z) by (subst X; change (inr64 e); zrange)
        | idtac "note: no range fact for" X ].
Tactic Notation "name_as" ident(X) constr(e) := name_as_tac X e.

(* [comment removed for export] *)
Ltac name_reg_tac n X :=
  let w := getreg n in
  lazymatch w with
  | Z_to_bv 64 ?e => name_as_tac X e
  | _ => fail "name_reg: register" n "holds" w
  end.
Tactic Notation "name_reg" constr(n) ident(X) := name_reg_tac n X.

(* [comment removed for export] *)
Ltac model_reg_tac n X mexpr :=
  let w := getreg n in
  lazymatch w with
  | Z_to_bv 64 ?e =>
      first [ constr_eq e mexpr
            | replace (Z_to_bv 64 e) with (Z_to_bv 64 mexpr)
                by (first [ f_equal; zeq_fast
                          | rewrite Z_to_bv_land64; f_equal; zeq_fast
                          | f_equal; zeq
                          | rewrite Z_to_bv_land64; f_equal; zeq
                          | apply Z_to_bv_eqm; rewrite ?Z.mod_mod by lia; zeq
                          | apply Z_to_bv_eqm; slim; zb_masks; pose_word_ranges; Z.div_mod_to_equations; lia
                          | apply Z_to_bv_eqm; zb_masks; pose_word_ranges; Z.div_mod_to_equations; lia ]) ];
      name_as_tac X mexpr
  | _ => fail "model_reg: register" n "holds" w
  end.
Tactic Notation "model_reg" constr(n) ident(X) constr(mexpr) := model_reg_tac n X mexpr.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma wrap64_lit : forall x, (x mod 2^64 = x mod 18446744073709551616)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_Walk ()) [] "h01xp;1p;2g003Kj14Tg0075j23Tg00;mj22Tg002fj10Tf0R0#0#0#0#0#0#0#0#0p=1g00RbR1g00VM#1#1#1#1#1#1#1#1#4,30,21W0o"). Qed.

(* [comment removed for export] *)
Ltac name_virtual_tac X e :=
  set (X := e);
  let EX := fresh "E" X in assert (EX : X = e) by reflexivity;
  let RX := fresh "R" X in
  first [ assert (RX : (0 <= X < 18446744073709551616)%Z) by (rewrite EX; change (inr64 e); zrange)
        | idtac "note: no range fact for" X ].
Tactic Notation "name_virtual" ident(X) constr(e) := name_virtual_tac X e.
