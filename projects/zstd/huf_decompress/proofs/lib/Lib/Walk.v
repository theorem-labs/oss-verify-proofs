(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Export Tac Bytes.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_Walk () := "C47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes?RelationClasses?Equivalence_PERC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z;lt_ge_casesC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic2or00C56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3ltbI47Corelib4Init5Logic2eq00C47Corelib4Init5Logic3iffC56Stdlib6ZArith6BinInt1Z6ltb_ltC47Corelib7Classes9MorphismsNtrans_sym_co_inv_impl_morphismK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib4Bool4Bool>eq_true_iff_eqK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z9mod_smallC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums1Z03C56Stdlib6ZArith6BinInt1Z3mulK46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z7mod_addC47Corelib4Init5Logic6eq_indK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula09K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C47Corelib7Classes?RelationClasses>iff_TransitiveI47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205K47Corelib7Numbers7BinNums8positive03C47Corelib7Classes?RelationClasses?iff_equivalenceI46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic5False00C56Stdlib6ZArith6BinInt1Z8add_comm".
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma carry_sym : forall x y, (0 <= x < 2^64)%Z -> (0 <= y < 2^64)%Z ->
  ((x + y) mod 18446744073709551616 <? x)%Z = ((x + y) mod 18446744073709551616 <? y)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_Walk ()) [] "h04__p1h14__p2h24__x1h34__x2h47__arithh54__ffh68__varmaph75__with85lemmah91Hh:2Hxh;2Hyh<1oh=1xh>1yh?1zp;1p;2p;3p;7p;4p;6p;9p;8p-1R0g0000R1p4p710p9P0g000\R2p4p710p9P0p1001NR3p4p710p9P0P3p4p7210p9P0P3p4p73110p9P0g001lR0p4p710p9g002fj18Tg003Kj1HTg003ij2TTg004Fj20Tg004bj23Tg005=j22Tg005Zj2\Tg006?j2<Tg006[R3j2VTg0075j2@Tg007Uj21Tg0082j3>Tg008LR4j27TP1j2ITg008ej2?TP2j3aTg009Ej7OTg00:@j1^Tg00:`j1]Tg00;@j2[Tg00;^j1ZTg00<<j4YTg00<Zj1XTg00=8j1WTg00=cj2ATg00>Fj2GTg00>ij1STg00?Kj3ETg00?nj2RTg00@Pj2UTg00@jj2qTg00AVj3pTg00B5j4oTg00Bgj3QTg00CIj1PTg00Chj2BTg00DQj3NTg00E:j2nTg00Efj3mTg00FFj1gTg00Fdj3fTg00GGj3LTg00Gjj6KTg00HHj1dTg00Hfj2cTg00ICj3bTg00Ifj4CTg00JQj6eTg00K5j4`Tg00KVj6_TP0l9hTg00L2j7JTg00LVj6iTg00M:j7jTg00M^j7kTg00NBj8lTg00NfR0f0R2'<p=;g00ODR1g00OdR57>2p=5p-0R6P4g00PDf5R7f4R8f3R9f2R:f1R;P2M9hp=Mg00Q5R<P;g00QSP2CCp==P;g00R:R=g00RYR>P>g00S9R?P2g00SYR@FJp=9P;P=P>P>P?P2Eip=FP:P=P>P>P?P;P2Fjp=:P:P=P>P>P?P<P;g00T9P2CCP@FJp=6P:P=P>P>P?P;P2Fkp=DP9P=P>P>P?P:P;P2Glp=4%;;R@g00T`RA#8RB#HRC%8B#8#8#8#8RD#H'TRE,0;RF'3RG129:RH/\E10HE1<EH'VP31289R3/0E1<E31278R3/@ERH/1711H85>1P2103EP<f6RH/27RIf7RJ,12112H5>1X?<RK11IHRL11I7RM%5L10IH'712JHRL/1J#510LJRNP211LH#5ROPO1I6OEMW81?IH%5M10I7'7P6P4g00UE9a64RMPNPO10LHP2FOW81?I7g00V7RO#^RN%]ORPP<1[<:P;%Z<RQCYRR%X<RS%W<RT1A<0RU1G<BRB'=,9T1FT8RV5:TRW%S>RXPT1G<ARY,=U,9T1FT7RZ5:TR[PXAE<YBR\=6TYA6T\B5DTC4C41RT?R]P2P:1U151q2:#5dAp<0;CoR5b5b6b7X2<X3<X06X1613@:13@812:9R@/0:10@9'7[[^2<^3<^06^16P210JER110HER^PHPJP8P7O6b4O2O23Q1@IER_g00VcR`#PRa#P,B<1B<a1B<`5N<5N<g00WB'n=mONROPPPRPSPT1A<C%gD5f<RD96T\RCPXPTPWPXPTP[PX1=U\,9T=:TCC4C4C4P]P5b5b6b7X2<X3<X06X16122;RC/0E%;:R[/3913[71298R[#;10[E'3[[[^2<^3<^06^16P2P1P^PHPJP;P8P7O7b49LIEEKW9P2O11<E3P<%dARA/cER3,2IR^/@ER1PKP<P^PK11^HRK11^7RW%5K10^H'712L3RL/1J#510LJRKP211LH#5R`P`1I6`EMW81?^H%5W10^7'7P6P4PMPKP`10LHP2FOW81?^7PNPPPRPSPTA6TBD9:TVRVPXPTA6TYD9:TZRZPX1A<A=b<D9E<\RL=6TYA6TLB5DTC4C4P]P5b5b6b7X2<X3<X06X1613:F138F12@3R@/0:10@9'7[[^2<^3<^06^16P2%;JR@%;HRFPHPJP8P7O6b4O2O23QP1POPPPRPSPT1=D\,9TPXPTPVPXPTPZPX1=UL,9TA6TLD5:TC4C4C4P]P5b5b6b7X2<X3<X06X161<EC10:ER:,39137:12[3R3#;103E'3[[[^2<^3<^06^16P2P@PFPHPJP;P8P7O7b49L^EEKP_PIPAPEPNPPPQPSPTP=P>P>P?P<PDg00WnPUCC,9TEeP]P5b5b6b7A><E0g00XU[P2b4C`E_W9P2O1n200100000021100011000b<X;GW:X><X=<o"). Qed.
Lemma carry_sym' : forall x y, (0 <= x < 2^64)%Z -> (0 <= y < 2^64)%Z ->
  ((y + x) mod 18446744073709551616 <? x)%Z = ((x + y) mod 18446744073709551616 <? x)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_Walk ()) [] "h01xh11yh21zp;2p;1p;3p;6g006?j2?Tg002fj10Tg003Kj12Tg003ij2>Tg004Fj2:Tg004bj28Tg005=j23Tg0075j24Tg007Uj25Tg0082j39Tg00@Pj2=Tg00Y2j2<Tg00Gjj6;Tf0R0#0#0#0#0p=6%00#0p=7%00#0#0#0#0#0#0#0p=1g00Q5R1g00Nff1R2'?g00T`#0R3#2%03#6R3#2'>,:2'8R2P1f3R4f2R5'3R6g00ODR7%73#1#1#1#1#1#1#1#2R3,40f4R0'51304/43/5039X211463/54,=713541<54E;V2UX11W0o"). Qed.

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
ltac2:(KReplay.run1 (kr_t_Walk ()) [] "h01xp;1p;2g003Kj14Tg0075j23Tg00@Pj22Tg002fj10Tf0R0#0#0#0#0#0#0#0#0p=1g00Q5R1g00T`#1#1#1#1#1#1#1#1#4,30,21W0o"). Qed.

(* [comment removed for export] *)
Ltac name_virtual_tac X e :=
  set (X := e);
  let EX := fresh "E" X in assert (EX : X = e) by reflexivity;
  let RX := fresh "R" X in
  first [ assert (RX : (0 <= X < 18446744073709551616)%Z) by (rewrite EX; change (inr64 e); zrange)
        | idtac "note: no range fact for" X ].
Tactic Notation "name_virtual" ident(X) constr(e) := name_virtual_tac X e.
