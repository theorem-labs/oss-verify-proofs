(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_HufStats HufPure_HufX1
  HufPure_HufTableX1.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseWalkMem StrFun.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RF_huf_iface RF_huf_bdt_model RF_huf_x1t_model.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RF_huf_x1t_cls () := "C47Corelib7Classes?RelationClasses9ReflexiveK47Corelib4Init5Logic2eq01c5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_x1t_cls7rep_valK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3eqbK47Corelib7Numbers7BinNums8positive01K47Corelib4Init9Datatypes4list01C46Stdlib5Lists4List7forallbC47Corelib4Init9Datatypes4andbC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib5Lists7ListDef3seqI47Corelib4Init5Logic2eq00K47Corelib4Init9Datatypes4list02K47Corelib4Init9Datatypes3nat02C47Corelib5Lists7ListDef3mapI47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith6BinInt1Z6of_natI47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01K47Corelib4Init9Datatypes3nat01C46Stdlib5Lists4List2InC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallI47Corelib4Init9Datatypes4list00I47Corelib4Init5Logic3and00I47Corelib4Init5Logic2ex00C46Stdlib5Lists4List:in_map_iffC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr01K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z2ltC46Stdlib9micromega;ZifyClasses;rew_iff_revI47Corelib4Init5Peano2le00C47Corelib4Init3Nat3addC47Corelib4Init5Peano2ltC46Stdlib5Lists4List6in_seqC56Stdlib6ZArith6BinInt1Z3addC46Stdlib9micromega;ZifyClasses9and_morphK46Stdlib9micromega7EnvRing5PExpr03K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C46Stdlib4Bool4Bool=andb_true_iffC56Stdlib6ZArith6BinInt1Z6eqb_eqC56Stdlib6ZArith6BinInt1Z6ltb_ltC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses5mkappK46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqI46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203C56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega=RingMicromega3Op205c5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_x1t_cls<rep_bytes_okC46Stdlib5Lists4List8map_consK46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions7Z_to_bvc5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_x1t_cls9rep_factsC47Corelib4Init5Logic8eq_ind_rC35stdpp7tactics<f_equal_helpC5ARocqVerifyHarness?AgentSubmission6Common6StrFun<Z_to_bv8_modC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le1C5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit7le1_litC47Corelib4Init5Logic6eq_indK47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C47Corelib4Init5Logic9False_indC47Corelib4Init5Logic6or_indC47Corelib4Init5Logic7and_indc5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_x1t_cls7rep_le1I47Corelib4Init5Logic5False00".
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation fmem := (word -> option byte).

(* [comment removed for export] *)
Ltac xb DT4 ARR q :=
  let SOK := fresh "SOK" in
  pose proof (u8arr_store_ok usegs _ DT4 _ q (wa (DT4 + q)) ARR ltac:(rewrite ?upd_length, ?ox1_length; lia) eq_refl) as SOK;
  zstep;
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ (wa ?E) _) _) => replace E with (DT4 + q) by lia
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ (Z_to_bv 64 ?E) _) _) => replace E with (DT4 + q) by lia
  end;
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?x)) _) =>
    first [ match goal with H : le1 x = [_] |- _ => rewrite H end | rewrite le1_lit ]
  end;
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ [?bb]) _) =>
    let ARR2 := fresh "ARR" in
    pose proof (u8arr_write usegs _ DT4 _ q bb ARR ltac:(rewrite ?upd_length, ?ox1_length; lia)) as ARR2;
    clear ARR; store_done; rename ARR2 into ARR
  end.


(* [comment removed for export] *)
Ltac xc DT4 ARR U k :=
  xb DT4 ARR (2 * Z.of_nat U + 2 * k); xb DT4 ARR (2 * Z.of_nat U + 2 * k + 1);
  replace (Z.to_nat (2 * Z.of_nat U + 2 * k)) with (2 * (U + Z.to_nat k))%nat in ARR by lia;
  replace (Z.to_nat (2 * Z.of_nat U + 2 * k + 1)) with (2 * (U + Z.to_nat k) + 1)%nat in ARR by lia;
  rewrite ox1_store' in ARR by (rewrite ?upd_length; lia).

(* [comment removed for export] *)
Definition x1f_inv (m m1 : fmem) (DT SY : Z) (js jt : list byte) (syms : list (option Z)) (ncells : nat)
    (cells : list (option deltX1)) : Prop :=
  u8arr usegs m1 (DT + 4) (ox1 jt cells) /\ length cells = ncells
  /\ bytes_at usegs m1 SY (omerge js syms)
  /\ munch [(DT + 4, DT + 4 + 2 * Z.of_nat ncells)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1.

(* [comment removed for export] *)
Definition x1_slots (DT : Z) : list cell :=
  [C8 (Z_to_bv 64 (DT + 20)); C8 (Z_to_bv 64 (DT + 5)); C8 (Z_to_bv 64 (DT + 7)); C8 (Z_to_bv 64 (DT + 4));
   C8 (Z_to_bv 64 (DT + 12))].

(* [comment removed for export] *)
Definition X1REP : Z := 281479271743489.     (* [comment removed for export] *)

Definition X1M31 : Z := 2^64 - 2^31 - 1.

Definition x1_fr (DT tl W : Z) (cu cs cw cc : word) : list cell :=
  [C8 (Z_to_bv 64 X1M31); C8 (Z_to_bv 64 (DT + 20)); C8 (Z_to_bv 64 DT); C8 (Z_to_bv 64 (tl + 1));
   C8 (Z_to_bv 64 (2^64 - 1 - W)); C8 (Z_to_bv 64 (tl + 1)); C8 cu; C8 cs; C8 (Z_to_bv 64 W); C8 cw; C8 cc;
   C8 (Z_to_bv 64 X1REP)].

Definition x1w_inv (m m1 : fmem) (SP DT SY : Z) (js jt : list byte) (syms : list (option Z)) (ncells : nat)
    (cells : list (option deltX1)) : Prop :=
  u8arr usegs m1 (DT + 4) (ox1 jt cells) /\ length cells = ncells
  /\ bytes_at usegs m1 SY (omerge js syms)
  /\ munch [(DT + 4, DT + 4 + 2 * Z.of_nat ncells); (SP + -208, SP + -112)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1.

Definition x1cls_stmt (pc : Z) (P : Z -> Prop) : Prop :=
  forall (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32)
         (x5 x6 x7 x8 x10 x11 x14 x15 x17 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
         (m m1 : fmem) (WK DT SY tl w cnt len nb u sym : Z) (syms : list (option Z)) (js jt : list byte) (ncells : nat)
         (cells : list (option deltX1)) (r : list (option deltX1) * Z) (POST : machine_state -> Prop),
  P len -> 1 <= w <= 12 -> len = 2^(w - 1) -> 1 <= nb <= 12 ->
  fill_syms (S (Z.to_nat cnt)) 0 cnt sym len nb syms cells u = Ok r ->
  0 <= cnt <= 256 -> 0 <= u -> 0 <= sym <= 256 ->
  length jt = (2 * ncells)%nat -> length js = length syms -> length syms = 256%nat -> Z.of_nat ncells <= 8192 ->
  (forall i v, nth i syms None = Some v -> 0 <= v < 256) ->
  0 < DT -> DT + 4 + 2 * Z.of_nat ncells <= 2^47 -> 0 < SY -> SY + Z.of_nat (length js) <= 2^47 ->
  (DT + 4 + 2 * Z.of_nat ncells <= SY \/ SY + Z.of_nat (length js) <= DT + 4) ->
  240 <= bv_unsigned sp -> bv_unsigned sp <= 2^47 ->
  (DT + 4 + 2 * Z.of_nat ncells <= bv_unsigned sp + -240 \/ bv_unsigned sp <= DT + 4) ->
  (SY + Z.of_nat (length js) <= bv_unsigned sp + -240 \/ bv_unsigned sp <= SY) ->
  rw_cells usegs m1 (bv_unsigned sp + -208)
    (x1_fr DT tl WK (Z_to_bv 64 u) (Z_to_bv 64 sym) (Z_to_bv 64 w) (Z_to_bv 64 cnt)) ->
  x1w_inv m m1 (bv_unsigned sp) DT SY js jt syms ncells cells ->
  (forall m2 cells' (y5 y6 y7 y8 y10 y11 y12 y14 y15 y17 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 : word),
     r = (cells', u + cnt * len) -> x1w_inv m m2 (bv_unsigned sp) DT SY js jt syms ncells cells' ->
     rw_cells usegs m2 (bv_unsigned sp + -208)
       (x1_fr DT tl WK (Z_to_bv 64 u) (Z_to_bv 64 sym) (Z_to_bv 64 w) (Z_to_bv 64 cnt)) ->
     evt usegs POST (MS (mkR (Z_to_bv 64 len) (Z_to_bv 64 (bv_unsigned sp + -240)) gp tp y5 y6 y7 y8 (Z_to_bv 64 (-9))
                             y10 y11 y12 (Z_to_bv 64 SY) y14 y15 (Z_to_bv 64 (2^64 - 1 - SY)) y17 (Z_to_bv 64 (-17))
                             (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (-25)) y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
                        F (Z_to_bv 64 (PHUF_RDT_X1 + 2912)) fc None m2 (seg_rom usegs))) ->
  evt usegs POST (MS (mkR (Z_to_bv 64 len) (Z_to_bv 64 (bv_unsigned sp + -240)) gp tp x5 x6 x7 x8 (Z_to_bv 64 (-9))
                          x10 x11 (Z_to_bv 64 nb) (Z_to_bv 64 SY) x14 x15 (Z_to_bv 64 (2^64 - 1 - SY)) x17 (Z_to_bv 64 (-17))
                          (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (-25)) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 pc) fc None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition rep_val (b nb : Z) : Z := Z.lor (b ≪ 8 mod 18446744073709551616) nb * X1REP.

Lemma rep_bytes_ok : forallb (fun b => forallb (fun nb =>
    forallb (fun sh => ((rep_val b nb mod 18446744073709551616) ≫ sh) mod 256 =? (if (sh / 8) mod 2 =? 0 then nb else b))
            [8; 16; 24; 32; 40; 48; 56] && (rep_val b nb mod 256 =? nb) && (rep_val b nb <? 18446744073709551616))
    (map Z.of_nat (seq 0 16))) (map Z.of_nat (seq 0 256)) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_x1t_cls ()) [] "h01bh12nbh22shp;2p;1p;3p;4p-1p10000p4p710p9g000\j2GTg0016j2?Tg0027j11Tg002\j12Tg003:j27Tg003Zj2CTg004:j2ATg004Wj29Tg0054j18Tg005Yj1@Tg0069j3:Tg006Uj2>Tg0073j2FTg007Pj2;Tg007lj3ETg008Fj3DTg008fj10Tg009Ej4BTf0R0#1#1p=6%10#1#1#1#1#1#1#1p=5g009aR1f1R2;D0p=4%00#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p==g00:?P1g00:^P0CBp=<%00#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=3g00;>R3g00;^R4'Gf2R5/?2g00<>R6#1R7#6R8#1R9#1R:#1#6R;#5#5#5#5#5#5#5#2R<'7/C0%2;R;'7P3P1%28R8,A0%27'7g00<c'9P2P5n0100000020000'9X21%29%86R6#1#6R9#2%2:%87#1#6#2%19#2%86#1#6#2%@1'4'4'4'4'4'4,485:11?20R2/7;/90'>1F2<'>X11g00=AR2%=2R<';#<5:1X01%=<#3#3#3#3#3#3#3,;2#<5:1=E34do"). Qed.

Lemma rep_facts : forall b nb, 0 <= b < 256 -> 0 <= nb < 16 ->
  (forall sh, In sh [8; 16; 24; 32; 40; 48; 56] ->
     ((rep_val b nb mod 18446744073709551616) ≫ sh) mod 256 = (if (sh / 8) mod 2 =? 0 then nb else b))
  /\ rep_val b nb mod 256 = nb /\ rep_val b nb < 18446744073709551616.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_x1t_cls ()) [] "h02shh11xh21Hh32H0h42nbh54__p1h64__p2h74__x1h84__x2h91nh:7__arithh;1mh<2z0h=4__ffh>8__varmaph?5__with@5lemmahA1yhB1AhC1BhD2H1hE2H2hF2H3hG1bhH2b1hI2b2hJ1fhK1lhL3lenhM5starthN2HbhO2HnhP3HshhQ2IBhR2INp&0p;1p;2p;3p;4p;5p;<p;6p;7p;8p;Bg0027j15Tg002\j1<Tg004:j2mTg0054j1eTg005Yj1tTg0016j23Tg0073j27Tg006Uj2:Tg008fj10Tg007Pj2TTg00=`j38Tg00>7j2hTg00>Pj3gTg00?Aj3fTg00?dj1uTg009Ej4_Tg007lj3Kk10RTg00@DR0j21Tg00@_j2rTg00A9k509Tg00:^R1j1nTg00AXR2j1WTg00B8k10QTg00BVl<cTg00C;j2bTg00C]j2MTg00D7j2aTg00D`j3`Tg00EIj2oTg00F5k10NTg00FSk20MTg00G4k30LTg00G]k20HTg00H;k10GTg00HYk40FTg00I7k10ETg00IUk10DTg00J@j2{Tg00Jcj4\Tg00KNj2kTg00L1k10BTg00LSk20ATg000\j2iTg00M5k20@Tg00Mak30?Tg00N@k40>Tg00O2R3j29Tg00ONj4[Tg00P9R4j2^Tg00PSj2ZTg00PjR5j2]Tg00QBk30=Tg00Q]R6j2xTg00R:j6qTg00Rcj3sTg00SFj4XTg00Saj4yTg00T;k20<Tg003:j26Tg003Zj2UTg004Wj2LTg00T\k20;Tg00U<k20:Tg00U\R7j2~Tg008Fk300Tg0069j3lTg00V8k208Tg00VUm<03Tg00W:k60ITg00W^k707Tg00XBk70JTg00Xfk70KTg00YJk806Tg00YnmB05Tg00<cR8f0R9'~p=O%59#5p=Sf2R:f1R;/99'1p=B%59#5#5#5#5#5#5#5p=D16:;/L9p=@f5R<f4R='3f3R>'6/U:/6;/L9p=?g009aR?@00;9p=GAl?=>16:;/L9':p=;%09#0#0#0p>0P%09#0#0#0#0#0#0#0p>0Og00:?R@P?P1P9C_p>02Al?;9p=}%09#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p>0C%09#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=Fg00;>RAAl?;9g00;^RB3Kp=AAKA9Bp=2AK?;9p=4A8@;9p=C20889p=Q1i?9p=EP?P@P?P?P2P=P1P>g00ZTP:P;P9N<03p=dP@P?P?P?P1P1P<P=P>P:P;P9N<03p>041989p=N1~98p=HAK?98p=Vg00[AR2@00;9p=JP;g00[mRCg00\LRDPDg00\lREP9J0Ip=|P;PCPDPDPEP9g00]LK07p==P:PCPDPDPEP;P9K0Jp=>P?P;g00]lP9C\p=jP:PCPDPDPEP;P9K0Kp=zP>PCPDPDPEP:P;P9L06p=IP@P?P4P1P7g00^Sg00=AR7P8P>P:P;P9M<cp=wP@P@P@P?P?P?g00_5P1P1P1P6g00_UP7P8P>P:P;P9NB05p=pP@P?P5P1P3g00`8P<P=P>P:P;P9M<cp=vP?P;g00`ZP9C\p=R16=>/U:/6;/L9p=P1U:;/69p=Y13:;/69p>01%O;R3g00<>R5#5R6#SR4#5RC#5RF#5#SRG#<RH7B;%<CRC9B3;g00aAP:P;%DG#D#D#D#D#D#D#<RGP9PHPAP?%<4R4,m9%<6R3;@8RIP;P:n0100000020000E?X0?%e5RJ#5#SRK#<%<F%e6#5#S#<%5K#<%eJ#5#S#<%t?'G'G'G'G'G,GC,G4RJ13;9RKPHP9D;17KG':X4?%07RK#0RF#0RL#0$0P$0ORM,T7RN$02RO'}XG?RP&0CM#F#F#F#F#F#F#FRQ,T7RR$02RS'ARTA8?9SPPP;O1#2[^1?RU,hTAgTU9W@Af?PSP9O2PUg00bGRUp4p710RPPUp4p7210RUP;\;RT%u:RVP0P=P>P:P;C_98>9P=P9O1=K<:f6RW?89>'1X1<,r<RX[P>P9O1=K=;A8<9:'1X1=,r=P<P=P>P:C_98=;[RYPWP<P=P>C_98<:\XP=P>P:P;P9I09P9n2001000000120000000XA:WKWJWCWBRXPY^A:^KV^JT^CU^BPRPP9P@P?P1PRPWP@%n9RUf7RT'41C9R'1X1@%WWRV%nVRY/4WRZ1CVRPZ%QWRZ/4WRRP?P?&0R?R[P9X1?R\P[14;9R]$0QXA?X1?R^PYPZP\P\%EUX1@RYPVPZP\%Q9X1?RVPWPW%EWR_DdJ04PWPWP_M<c1b8W%NW/1R%HW%VZ'1'M%QTRZP?p-0RR1a?FRF1a?K1a?7RK5`?5`?g00bdR_'oR`1a?L&0N5-0M?>0L?F=`?KRK5`?/o_RF1oK_RK%t2R_'J'J'J%u2R2P?20H?:P;&0G?H0FRL&0E?Ra&0D?Rb1|b=RcP?1{?5R5g00cPRd1{?6R6C\,=bRe5>b1k?8Rf,j6,=bP?P5PdPfC\,=bRd5>b5zb&0BDRDPb1jf6,=b1|b<Rg5>bPDPeCICI20AbEREP9P:1iAB20@9:#2dB0??8;H0>RBb=b>b?X7?X8?X5RW6Rh149;Ri,1:%H;%V9Rj'1'M%O:Rk/1=14:>[[^7?^8?^5R^6RRlP9f9Rm/9H%NmRnPmP;P:PTO6b:b<b3C[P01T;:,C91^:;1Z:>,];'1Ro[1^;91Z;:,]9'11T:>,C;[Rp1T>=,C:\oB0=:;9P9n2001000000120000000X9@XM@XL@RoPp^9@^M@^L@RpP9PQP7%WTRq1^7qRr1Z7QRs,]qRt'1%OZRu1x8HRv,9ZRw'1PrPtPuPw1i?8RwPqPZP\PVPTPT%ETDdRuCwPqPZPuPsPvPwPQPH%EHCpEvEq1b8T%NT14ZT'1%HT%VZ'1'Mf8RZ#QRQP?1J`_,JF,JKRKP2PLPaPb1Rf6,=b=>beA>bcd5zbRdPDPb1k?HRc,R6,=b9>bgPD1jf5,=bReAs?fc,R5,=b5>bCICIPEPBb=b>b?X7?X8?X5RX6R%N;/1i11:j'MRjAB=:HABk:v[[^7?^8?^5R^6RP9f:Rv#O%HvPvP;P:PZO6b:b<b3C[O4b3CXCyO6b3A8?<SP;PWP9O2PZP;PGP9PHPAP?PIP;PZn0100000020000E?X0?PJ13T9RWPHP9D;17WG':X4?/AOPmP;PGP9PHPAP?PIP;Pmn0100000020000E?X0?PJ13Z9RWPHP9D;17WG':X4?RW/AOA8?9ORSf;R<P;PGP9PHPAP?PIP;P<n0100000020000E?X0?PJ13v9RiPHP9D;17iG':X4?P;O1#2[^1?Ri'hPvP;PGP9PHPAP?PIP;Pvn0100000020000E?X0?PJ13m9RcPHP9D;17cG':X4?/AOf<RcP;PGP9PHPAP?PIP;Pcn0100000020000E?X0?PJ13<9RFPHP9D;17FG':X4?P;O1#2\S^1?;g9W@Af?WOP9O2PiPXPPP9P@P?P1PNPZP@14Um1C9N'1X1@%WZR@%n@RU/4ZR11C@NP114QZR1P?P?P[P\P[P^PUPQP\P\PYP@PQP\PVPZPZ%EZR@DdJ04PZPZP@M<c1b8Z%NZ/11%HZ%VQ'1'M%QmRQP?PhPlP919<C%N<P<P;P:PmO6b:b<b3C[PoPpP9PMP7%WmRp1^7pRo1Z7MR7,]pRl'1%OQRh1x8CR1,9QR@'1PoPlPhP@PwPpPQP\PVPmPm%EmDdRVCwPpPQPVP7P1PwPMPC%ECCpEvEq1b8m14Qm,1n%Hm%VQ'1'M%QvP?PKP2PLPaPbPdPDPb1k?CRd,R6,=b9>bgPDAs?fd,R5,=b9>beCICIPEPBb=b>b?X7?X8?X5RX6RAB=:CABk:1[\j^7?^8?^5R^6RP9%Oc%HcPcP;P:PvO6b:b<b3C[O4b3CXCyO6b3A8?TOP;PZP9O2PvPmPGP9PHPAP?PIPmPvn0100000020000E?X0?PJ13mZRmPHPZD;17mG':#2P01:;9#2%2:Rm%2;RZ'1[RO%29,1Z1::;#2RZ[%2>/1m\Z20<;9P;n2001000000120000000XIAXHARZPO^IA^HAROP913c<RmPGP9PHPAP?PIP<Pcn0100000020000DPX0?PJ13<vRRPHPvD;Rj17RGRRP;O3%2j%2R'1P0f=RR/3cRjPGP9PHPAP?PIPcPRn0100000020000DPX0?PJPmPHP<D;#217mG#2A8?9JRmf?R<f>R1'3Rk/6GRC?Y;HPAP?1m;4?@38R=P1P<n0100000020000'4[^0?16jH/4c?BjG'1P91UC9PAP?PIP1P<n01000000200007@HX0?PJ131RPHPRD;#217kG#2PZPOP9fBROfARZ'3RkPGP9PHPAP?PIPZPOn0100000020000DPX0?/}JRRf@R1,3Z?@H1R1P:O3%2R%21'1P0fCR1/3ORRPGP9PHPAP?PIPOP1n0100000020000DPX0?/AJA@kHZ#2fERkfDRZ'3R1/6GR<?Y;HPAP?P=PZPkn0100000020000'4\m^0?16RH/4O?BRG'1P91U<9PAP?PIPZPkn01000000200007@HX0?/AJA@1HZ#2fGR1fFRZPGP9PHPAP?PIPZP1n0100000020000E?X0?RZ/AJfIRkfHR<PGP9PHPAP?PIP<Pkn0100000020000E?X0?P;O1#2\m^1?RR'h13<1ROPGP9PHPAP?PIP1P<n0100000020000DPX0?/AJfJR</3kRCPGP9PHPAP?PIPkP<n0100000020000DPX0?P;O1#2\m^1?;g9W@Af?ZJP;O2PRP01L;9#214:;[RR1L:;#2RZ\]14>:\Z20;;9P;n2001000000120000000X;?X9?RZPR^;?^9?RRP916OHROP1P:O314O1P017;9#219:;[R019;917:;#2RO[19>:\O20:;9P;n2001000000120000000X;?X9?P0^;?^9?P9PCPGPvO319CGfMRCfLRv<01G?Y;HPAP?P=PvPCn0100000020000'4\m^0?fK/3<Rv/6H/4<R<19vGRv'1PZPRP9fNRR@01CG?Y:HPAP?1m:4?@38PCPRn0100000020000PTP:P;O2O3b2XPmX0?P<PvP:P9CXCXbFb2bEb2bDWEWDP;P9O2n2101000010121000000b2b3WFW2P;P9O2n2101000010121000000b2b3b2bRb2b2bQb2b2WOWNX4?XG?o"). Qed.

Lemma rep_le1 : forall b nb sh, 0 <= b < 256 -> 0 <= nb < 16 -> In sh [8; 16; 24; 32; 40; 48; 56] ->
  le1 (Z_to_bv 64 ((rep_val b nb mod 18446744073709551616) ≫ sh)) = [Z_to_bv 8 (if (sh / 8) mod 2 =? 0 then nb else b)].
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_x1t_cls ()) [] "p'0h02shh17__arithh24__x1h31bi001bh42H1h52Hbh62Hnh72Hsh82_Hh94__ffh:8__varmaph;5__with<1ah=2b0h>1lh?2nbh@1zp;2p;1p;3p;4p;7p;6p;8g00U\j2[Tg0027j11Tg002\j13Tg00O2j2=Tg00@DR0j27Tg0054j1CTg005Yj1BTg00=`j3GTg00d7j1ETg00dUj1JTg00?dj1FTg0016j2:Tg003:j20Tg003Zj29Tg00e8j2<j1UTg008Fj3Dj2Hj1VTg004:j28Tg007lj3?Tg000\j2>Tg00e^j4TTg00G]j2STg00I7j1RTg00IUj1QTg00J@j2LTg00Jcj4KTg00W^j7MTg00LSj2NTg00M5j2OTg00Maj3PTg00N@j4ITg00faj6@Tg00g?j8ATg00g\j1ZTg00h[j1YTg00iKj1XTg004Wj2WTf0R1#1#1p=;g009aR2f1R3;D1p=5%11#1#1#1#1#1#1#1p=4g00<cR4,W1p=6A?231p=2f2R5,[4R6g00<>R7#1R8#;R9#1R:#1R;#1R<#;R=#3R>,=5'7%3:R:,=5,76%39R6%C7R?#1#;R@#3%3;%C8#1#;#3%1@#3%C?#1#;#3%B2'5'5'5'5'5,5:'5R:9G25%E9R9#JR?#FR@f5R;f4RA':RB%4=#4#4#4#4#4#4#3R='0f3RC'9RD,<9RE%B?RF5D?g00;>RGP218A6%38R8'0#6P;f6RHn0100000020000,<9RI=D?F9?@1X>@P@P@1H?EPGP218C6/08#6PAP;n0100000020000RC,<9RJ,H?PFPFP?P@\@RK%V?RLPLPEPJPK\?/>LP?10D>RL,<9A??1IX3?P2P?%U9R9P9PLPCP?\2/>9P;PAP5P3CTAG21:R:f7R9/:H/0=R?/93/0>PGP21836/08#6RCPHP9n0100000020000'2[^0210B>/2A1=B='7'7P0f8R0/:9/0=/93/0>PGP2PCP9P0n0100000020000'2\:^021:H;RB/0>/2;1=B='719?;/0>PGP218;6/08#6PHP9n0100000020000'2P1f:R9f9RH':/0=R?/93/0>PGP2PCPHP9n0100000020000'2\:^021:H0R:/0>/201=:='7P2PGP21806/08#6R:PHP9n0100000020000PGP218H6/08#6P9f;R9n0100000020000,21X@2P:PGPGPGP2P1P9f<R:n0100000020000R8/28P1g00[AR8#B%F81S23%R2%Q2R8g00[mg00\LRHPHg00\lRHP21L27R7g00cPP7CKg00]LFM1N8HP1P5g00;^RH,>G1O15=?GHdAP243CIb9b:b;X22R41211^22RHP1P9O1b1P4PHP1P:O1b1n0110000020000b=19?0/0>P3P0P;O2E@W8W4P3P1O2n2101000000121000000b<GAPE%ZDE@GA1>@FGA%E</<D#Y%XDE@W7W6W5X02X?2X32o"). Qed.

Lemma rep_le1_0 : forall b nb, 0 <= b < 256 -> 0 <= nb < 16 -> le1 (Z_to_bv 64 (rep_val b nb)) = [Z_to_bv 8 nb].
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_x1t_cls ()) [] "h02shh11bh21Hh32H2h42Hbh52Hnh62_Hh73_H0h81ah91lh:2nbh;1zp;2p;1p;3p;4p;6p;8g00U\j2QTg0027j10Tg002\j11Tg00O2j25Tg00@DR0j28Tg00d7j1DTg00dUj1LTg00?dj1JTg0016j22Tg00e8j29j1OTg005Yj1BTg008Fj3=j2Ej1PTg007lj3<Tg000\j2;Tg003:j26Tg00e^j4MTg0054j1@Tg00=`j3KTg003Zj2?Tg004:j2ITg004Wj2HTg00faj6>Tg00g?j8ATg00g\j1GTg00h[j1FTg00iKj1NTf0R1#0#0p=:g009aR2f1R3;=1p=7%01#0#0#0#0#0#0#0p=4f2R4/63=<21p=3A<231p=Cg00<cR5/Q3R6g00<>R7#0R8#:R9#0R:#0R;#0R<#:R=#1R>,53'8%1:R:,53,86%D9R6#LR?#JR@f3RA/24RB,96RC%B?RD5=?196ARE==?D9<@1X9@P@P@1E?C1964RF,E?PDPDP?P@\@RG%P?RHPHPCPFPG\?/;HP?16B>RH,96A<?1EX1?P2P?%O6R6P6PHP4P?\2/;6PAP4P3P1CM%19R9%@7R7#0#:R6#1%1;%@8#0#:#1%06#1%@7#0#:#1%B2'7'7'7'7'7,7:'79K21R:f5R7f4R6'2R;%4=#4#4#4#4#4#4#1R='6/?3g00;>R?P21I39%18'6/H5R5P6P7n010000002000073>[^021CH415B='8'8P0f6RH/27/6=/?3P?P2P5P7PHn010000002000073>\:^02126AR7?3>A157='8A3;>6P1f8R;f7R6'2R7/6=/?3P?P2P5P6P;n010000002000073>\:^02126HR:?3>H15:='8P0A37>6157=f9R7/2;?3>;P1f:R;/27?3>7f;R7/2;/5=P2P7f<R=,C1X;21;2712=7/6>P3E>W7W3P3P1O2n2001000000120000000W2W6P3P1O2n2101000000121000000b8GAPC%GBE>GA1;@DGA%D</9B#F%NBE>W5W4X:2X12o"). Qed.

Lemma rep_le1_even : forall b nb sh, 0 <= b < 256 -> 0 <= nb < 16 -> In sh [16; 32; 48] ->
  le1 (Z_to_bv 64 ((rep_val b nb mod 18446744073709551616) ≫ sh)) = [Z_to_bv 8 nb].
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_x1t_cls ()) [] "h01Hh12H3h22shh32H4h42H0h52H1h62H2h72Hbh82Hnh92Hsh:1bh;1lh<2nbp;2p;1p;3p;6p;5g00U\j2HTg0027j12Tg002\j15Tg00O2j2;Tg00@Dj2PTg0054j1GTg005Yj1OTg00=`j3JTg00d7j1ITg00dUj1QTg00?dj1YTg004:j2>Tg003:j2:Tg007lj34Tg000\j2FTg00jIj6DTg0016j2WTg003Zj2VTg00e8j2LTg00h[j1UTg00C]R0j21Tg00jej3BTg00k?j36Tg00kYj2RTg00l8j6CTg00lTj5KTg00m1j6STg00faj6TTg008Fj3ATg004Wj2XTf0R1#2#2p=?g009aR2f1R3;A1p=Mf2R4AA2315A2p=@g00<cR5,X1p==f3R61L43;A1p=3A4231p=0g00n2R7,11,13p=9A4231/17p=EA4243/11p=71117p=N%21#2#2#2#2#2#2#2p=81131,14p=<1H54R8g00<>R9#2R:#?R;#2R<#2R=#2R>#?R?#5R@,;4'P%5<R<,;4,P8%5=R=%G9R9#2#?R8#2#5RA%O2RB'M5@<9J24%I;RC#QRD#YREPDPCg00;>RFP2%5;R;,>6%5:RG':#=f4RHf5RIn0100000020000%ODRJC3PDPCPIPJC3RK94E1X;EP010<6RL10=6RM10A6RN'9PDPCPFP21>H;/:G#=PIf6ROn0100000020000PJC3=4EKP110<HP2P<PDPCPFP21>1;/:G#=RKf7RPf8RQn0100000020000PJC3PDPCPPPJC3RR54EX22PDPCPOPJC3,FEPIP1EDW0P1O11EAH97=HP010=IRS10AIRT#NPDPCPFP21>O;/:G#=PPPQn0100000020000PJC3=4ERP110=OP2P=PDPCPFP2PKf9RRf:RUn0100000020000PJC3PDPCPRPJC3RV54EX22PDPCPQPJC3,FEPPP1EDW0P1O11EAOP010APR0P7PDPCPFP21>Q;/:G#=PRPUn0100000020000PJC3=4EVP110AQRVP2PAPDPCPFP2PKf;RKf<RWn0100000020000PJC3PDPCPKPJC3RX54EX22PDPCPUPJC3,FEPRP1EDW0P1O1P7PDPCPFP21>U;/:G#=PKPWn0100000020000PJC3=4EXP1n010000000X07P1O1n200100000021000010000W0P1O1n200100000021000011000W0P1O1n200100000021000011000%I>1WIH%8?#8#8#8#8#8#8#5':/V6'L#UPIPHP6P4P31H5IR31;I@%58R8/06%G:#2#?#5R:/06%G9#2#?#5R9/06,9N5<M5<L97;61;O@1H5OR51;O<10:I109I,9T5<S978I97<I97;I1;P<10<PRI10=PRS/90RT108P10:P109P,905<S5<I97;P10;QRP10<QRS10=QR010:Q109Q,9V3<978QRQ'1ROABSQ136X1IP0%NVRV11PO10;RRO10<RRP108RRI10=RRQ10ARRS109R'997:RRR'1R@'1RL'1RMABQR196I@96PL36X30PSP711OM10;URM10<URO108UR010=URL10:URP10AUR@1E9URU'1RI'1RR'1RQ'1RN'1R?AB@U196PI96LR960Q96ON36X1S11M?/R1X17P1ECX3VP1ECX1TPHECW6X55P6DKW4X03P4DK1M9B9@:A9@8=9@;<9J26eESETW9W8W7X22X<2X:2o"). Qed.

Lemma rep_le1_odd : forall b nb sh, 0 <= b < 256 -> 0 <= nb < 16 -> In sh [8; 24; 40; 56] ->
  le1 (Z_to_bv 64 ((rep_val b nb mod 18446744073709551616) ≫ sh)) = [Z_to_bv 8 b].
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_x1t_cls ()) [] "h01Hh12shh22H3h32H4h42H0h52H1h62H2h72Hbh82Hnh92Hsh:1bh;1lh<2nbp;2p;1p;3p;6p;5g00U\j2ITg0027j12Tg002\j15Tg00O2j2?Tg00@Dj2OTg0054j1HTg005Yj1MTg00=`j3LTg00d7j1KTg00dUj1UTg00?dj1QTg004:j2;Tg003:j2:Tg007lj3ATg000\j2ETg00jIj6DTg00C]R0j21Tg0016j2XTg003Zj2WTg00e8j2FTg00h[j1VTg00jej3CTg00kYj2TTg00l8j6BTg00lTj5JTg00m1j6RTg00faj6STg008Fj3GTg004Wj2YTg00k?j3PTf0R1#2#2p=@g009aR2f1R3;G1p=4g00<cR4,Y1p==f3R5f2R6/F3;G1p=6AA231p=0g00n2R7,11p=81131,16p=Nf5R8f4R91F56;G3;A1p=7AA263/11p=9%21#2#2#2#2#2#2#2p=<AA263/11,15p=3AP6319P95p=>1I46R:g00<>R;#2R<#@R=#2R>#2R?#2R@#@RA#5RB,?6'O%5>R>,?6,O:%5=R:%H;R;#2#@RC#5RD%H<#2#@#5RE%H;#2#@#5R;%M2'4RF'4'4'49L26%K=R=#URG#QRHPGP=g00;>RIP21;5:%5<R<':#=P9P8n0100000020000%MGRJC6PGP=f6RKPJC6RL9AH1X;HP010:5RM10D5RN10E5RO10;5#8RP3NPHPGP=PIP21;9:/:<#=P8PKn0100000020000PJPLE7P110:9P2P:PHPGP=PIP21;1:/:<#=RLf7RQf8RRn0100000020000PJPGP=PRPJC6RSE7X12PGP=PQPJC6,EHP8P1EDW0P1O110;9#899E999D9P010D8RT10E8RU10;8#8RV'1PHPGP=PIP21;K:/:<#=PQPRn0100000020000PJPSE7P110DKP2PDPHPGP=PIP2PLf9RSf:RWn0100000020000PJPGP=PWPJC6RXE7X12PGP=PSPJC6,EHPQP1EDW0P1O110;K#899EKP010EQRY10;Q#8RZPHPGP=PIP21;R:/:<#=PSPWn0100000020000PJPXE7P110ERRXP2PEPHPGP=PIP2PLf;R[f<R\n0100000020000PJPGP=P\PJC6R]E7X12PGP=P[PJC6,EHPSP1EDW0P1O110;R#8R^P010;SR0P7PHPGP=PIP21;W:/:<#=P[P\n0100000020000PJP]E7P110;WR]P2P;PHPGP=PIP2PLf=RLf>R_n0100000020000PJPGP=P_PJC6R`E7X12PGP=PLPJC6,EHP[P1EDW0P1O1P7PHPGP=PIP21;\:/:<#=PLP_n0100000020000PJP`E7P1n010000000X07P1O1n200100000021000010000W0P1O1n200100000021000011000W0P1O1n200100000021000011000W0P1O1n200100000021000011000%K@1X89%<A#<#<#<#<#<#<#5':/W5'F#VP8P9P5P6P31I48R31?8BPMP>P5PN%5?R?P5PO%2C#5RCP5PPC3C3C31?KB1I4KR41?K>PTP?P8PUPCP8PVC3C399>899:81?Q>10:QR810DQRV?NYZRUP8P>PQPVP?PQPYPCPQPZC3C3C310:RRZ10DRRQP?PRPXPCPRP^C3C399>RRR;C1X28PQ11X^R^11ZR10:SRR10>SRZ10DSRX10ESR8PCPS%80R0C399?SRS'1RY'1RVPZPYACXS1D>X3QP8P011RV10:WRV10>WRR10DWRQ10?WRS10EWRX%8]99CWRW'1RY'1RZ'1RT'1RKPRPTPQPZPSPYACXW1D>D>X28P]P711VK10:[RK10>[RV10D[R810?[RW10E[RX10C[RY10;[R[#8R;'1RS'1RZ'1RQ'1RT'1RRPVPTP8PQPWPZPXPSPYP;AC[71D>D>D>X3]11KR/T1X37P1EBX20P1EBX3^P1EBX2UP9EBW6X54P5DJW4X03P6DJ14CF,4E,4?,4D,4>,4:9L25eERESW9W8W7X12X<2X:2o"). Qed.
