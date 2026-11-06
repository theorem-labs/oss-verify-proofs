(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AxSymExec3 () := "C47Corelib5Lists7ListDef3mapC47Corelib4Init9Datatypes3fstC46Stdlib5Lists4List:fold_rightK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z9land_onesI47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib7Numbers7BinNums1Z01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z6moduloK47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z8leb_specI47Corelib4Init9Datatypes8BoolSpec00C56Stdlib6ZArith6BinInt1Z8ltb_specC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z=mod_neg_boundI47Corelib4Init5Logic3and00C56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z9mod_smallC47Corelib4Init5Logic8eq_ind_rK46Stdlib9micromega7EnvRing5PExpr06K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z7mod_addC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic6eq_symC56Stdlib6ZArith6BinInt1Z4landc69OSSVerify5KrLib2AS:AxSymExec33AX2=land_ones64z'C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS:AxSymExec33AX25snormC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS:AxSymExec33AX29snorm_refC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4bool02I47Corelib4Init5Logic4True00I47Corelib4Init5Logic5False00c69OSSVerify5KrLib2AS:AxSymExec33AX27ones64zC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS:AxSymExec33AX26zmod64C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z9div_smallC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2c69OSSVerify5KrLib2AS:AxSymExec33AX26zdiv64C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS:AxSymExec33AX29zmod64_eqC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS:AxSymExec33AX29zdiv64_eqC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS:AxSymExec33AX2:all_factsbC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS:AxSymExec33AX28is_factbC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indC47Corelib4Init9Datatypes8list_indC46Stdlib5Lists4List6filterK47Corelib4Init9Datatypes4list02i69OSSVerify5KrLib2AS:AxSymExec33AX26kentry00C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01c69OSSVerify5KrLib2AS:AxSymExec33AX2Aall_factsb_filterC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS:AxSymExec33AX28facts_ofC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS:AxSymExec33AX25sfactC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appc69OSSVerify5KrLib2AS:AxSymExec33AX26pt_getC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS:AxSymExec33AX26pt_setC1?~~~~~~~~~~~~~~~i69OSSVerify5KrLib2AS:AxSymExec33AX25ptree00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes6option01k69OSSVerify5KrLib2AS:AxSymExec33AX25ptree01C1?~~~~~~~~~~~~~~~k69OSSVerify5KrLib2AS:AxSymExec33AX25ptree02C1?~~~~~~~~~~~~~~~C47Corelib7Numbers7BinNums<positive_indI47Corelib7Numbers7BinNums8positive00C47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalk69OSSVerify5KrLib2AS:AxSymExec33AX24expr01C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS:AxSymExec33AX28expr_eqbC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS:AxSymExec33AX26wrap64C1?~~~~~~~~~~~~~~~k69OSSVerify5KrLib2AS:AxSymExec33AX24expr02C1?~~~~~~~~~~~~~~~k69OSSVerify5KrLib2AS:AxSymExec33AX24expr03C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS:AxSymExec33AX29evalS_defC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS:AxSymExec33AX25evalSC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS:AxSymExec33AX25zfastC1?~~~~~~~~~~~~~~~k69OSSVerify5KrLib2AS:AxSymExec33AX24expr04C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS:AxSymExec33AX26zfastwC1?~~~~~~~~~~~~~~~k69OSSVerify5KrLib2AS:AxSymExec33AX24expr05C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS:AxSymExec33AX26zfastmC1?~~~~~~~~~~~~~~~k69OSSVerify5KrLib2AS:AxSymExec33AX24expr06C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS:AxSymExec33AX24zmdwC1?~~~~~~~~~~~~~~~k69OSSVerify5KrLib2AS:AxSymExec33AX24expr07C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS:AxSymExec33AX29zext_fastC1?~~~~~~~~~~~~~~~k69OSSVerify5KrLib2AS:AxSymExec33AX24expr08C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS:AxSymExec33AX28expr_indC1?~~~~~~~~~~~~~~~i69OSSVerify5KrLib2AS:AxSymExec33AX24expr00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I4ELinuxProcessSemantics5Riscv5Instr5aluop00I4ELinuxProcessSemantics5Riscv5Instr5mulop00c69OSSVerify5KrLib2AS:AxSymExec33AX28conc_tryC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS:AxSymExec33AX2<conc_try_refC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS:AxSymExec33AX27closedbC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4negbI47Corelib4Init9Datatypes4prod00c69OSSVerify5KrLib2AS:AxSymExec33AX26erangeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS:AxSymExec33AX26probeSC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natc69OSSVerify5KrLib2AS:AxSymExec33AX2<all_eval_toSC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS:AxSymExec33AX2>evalS_def_NoneC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS:AxSymExec33AX2:conc_limitC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS:AxSymExec33AX2:itab_soundC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS:AxSymExec33AX2<mk_itab_fuelC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS:AxSymExec33AX2:itab_entryC1?~~~~~~~~~~~~~~~C56Stdlib6PArith6BinPos3Pos6eq_decI47Corelib4Init6Specif7sumbool00c69OSSVerify5KrLib2AS:AxSymExec33AX26pt_gssC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS:AxSymExec33AX26pt_gsoC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03c69OSSVerify5KrLib2AS:AxSymExec33AX2;itab_lookupC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02C47Corelib4Init9Datatypes7nat_indI4ELinuxProcessSemantics5Riscv5Instr5instr00c69OSSVerify5KrLib2AS:AxSymExec33AX24itabC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01c69OSSVerify5KrLib2AS:AxSymExec33AX2;pt_get_leafC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS:AxSymExec33AX2Bmk_itab_fuel_soundC1?~~~~~~~~~~~~~~~".
(* [comment removed for export] *)
Unset Lia Cache.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.

Module AX2.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive expr : Type :=
| ELit  (z : Z)                              (* [comment removed for export] *)
| EVar  (n : nat)                            (* [comment removed for export] *)
| EAlu  (op : aluop) (a b : expr)            (* [comment removed for export] *)
| EAluw (op : aluop) (a b : expr)            (* [comment removed for export] *)
| EMd   (op : mulop) (a b : expr)            (* [comment removed for export] *)
| EMdw  (op : mulop) (a b : expr)            (* [comment removed for export] *)
| EExt  (sx : bool) (lo n : nat) (e : expr)  (* [comment removed for export] *)
| EBlob (sx : bool) (k : nat) (i : Z) (n : nat).
                                             (* [comment removed for export] *)

(* [comment removed for export] *)
Record env : Type := Env { ev : nat -> word; eb : nat -> list byte }.

Definition ext_Z (sx : bool) (lo n : nat) (z : Z) : Z :=
  let u := ((z / 2 ^ (8 * Z.of_nat lo)) mod 2 ^ (8 * Z.of_nat n))%Z in
  if sx then bv_swrap (8 * N.of_nat n) u else u.

Definition ext_val (sx : bool) (lo n : nat) (v : word) : word :=
  Z_to_bv 64 (ext_Z sx lo n (bv_unsigned v)).

Definition blob_bytes (bs : list byte) (i : Z) (n : nat) : list byte :=
  firstn n (skipn (Z.to_nat i) bs).

Definition blob_val (sx : bool) (bs : list byte) (i : Z) (n : nat) : word :=
  Z_to_bv 64 (let u := bytes_le_to_Z (blob_bytes bs i n) in
              if sx then bv_swrap (8 * N.of_nat n) u else u).

Fixpoint edenot (E : env) (e : expr) : word :=
  match e with
  | ELit z => Z_to_bv 64 z
  | EVar n => ev E n
  | EAlu op a b => alu64 op (edenot E a) (edenot E b)
  | EAluw op a b => sext 64 (alu32 op (low32 (edenot E a)) (low32 (edenot E b)))
  | EMd op a b => mul_div op (edenot E a) (edenot E b)
  | EMdw op a b => sext 64 (mul_div op (low32 (edenot E a)) (low32 (edenot E b)))
  | EExt sx lo n a => ext_val sx lo n (edenot E a)
  | EBlob sx k i n => blob_val sx (eb E k) i n
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition aluop_eqb (a b : aluop) : bool :=
  match a, b with
  | ALU_ADD, ALU_ADD | ALU_SUB, ALU_SUB | ALU_SLL, ALU_SLL | ALU_SLT, ALU_SLT
  | ALU_SLTU, ALU_SLTU | ALU_XOR, ALU_XOR | ALU_SRL, ALU_SRL | ALU_SRA, ALU_SRA
  | ALU_OR, ALU_OR | ALU_AND, ALU_AND => true
  | _, _ => false
  end.

Definition mulop_eqb (a b : mulop) : bool :=
  match a, b with
  | M_MUL, M_MUL | M_MULH, M_MULH | M_MULHSU, M_MULHSU | M_MULHU, M_MULHU
  | M_DIV, M_DIV | M_DIVU, M_DIVU | M_REM, M_REM | M_REMU, M_REMU => true
  | _, _ => false
  end.

Fixpoint expr_eqb (x y : expr) : bool :=
  match x, y with
  | ELit a, ELit b => Z.eqb a b
  | EVar a, EVar b => Nat.eqb a b
  | EAlu o a b, EAlu o' a' b' => aluop_eqb o o' && expr_eqb a a' && expr_eqb b b'
  | EAluw o a b, EAluw o' a' b' => aluop_eqb o o' && expr_eqb a a' && expr_eqb b b'
  | EMd o a b, EMd o' a' b' => mulop_eqb o o' && expr_eqb a a' && expr_eqb b b'
  | EMdw o a b, EMdw o' a' b' => mulop_eqb o o' && expr_eqb a a' && expr_eqb b b'
  | EExt s l n a, EExt s' l' n' a' =>
      Bool.eqb s s' && Nat.eqb l l' && Nat.eqb n n' && expr_eqb a a'
  | EBlob s k i n, EBlob s' k' i' n' =>
      Bool.eqb s s' && Nat.eqb k k' && Z.eqb i i' && Nat.eqb n n'
  | _, _ => false
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition zalu (op : aluop) (x y : Z) : Z :=
  bv_unsigned (alu64 op (Z_to_bv 64 x) (Z_to_bv 64 y)).
Definition zaluw (op : aluop) (x y : Z) : Z :=
  bv_unsigned (sext 64 (alu32 op (low32 (Z_to_bv 64 x)) (low32 (Z_to_bv 64 y))) : word).
Definition zmd (op : mulop) (x y : Z) : Z :=
  bv_unsigned (mul_div op (Z_to_bv 64 x) (Z_to_bv 64 y)).
Definition zmdw (op : mulop) (x y : Z) : Z :=
  bv_unsigned (sext 64 (mul_div op (low32 (Z_to_bv 64 x)) (low32 (Z_to_bv 64 y))) : word).
Definition zext_lit (sx : bool) (lo n : nat) (x : Z) : Z :=
  bv_unsigned (ext_val sx lo n (Z_to_bv 64 x)).

Definition is_lit (e : expr) : option Z :=
  match e with ELit z => Some z | _ => None end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Definition two64z : Z := 2 ^ 64.
Definition two64 : Z := 2 ^ 64.         (* [comment removed for export] *)
Definition two64m1 : Z := two64 - 1.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition two63z : Z := 2 ^ 63.
Definition mtwo63z : Z := - 2 ^ 63.
Definition two32z : Z := 2 ^ 32.
Definition two31z : Z := 2 ^ 31.
Definition ones64z : Z := Z.ones 64.          (* [comment removed for export] *)
(* [comment removed for export] *)
Definition snorm_ref (k : Z) : Z :=
  let m := (k mod two64z)%Z in if Z.leb (2 ^ 63) m then (m - two64z)%Z else m.
(* [comment removed for export] *)
Definition snorm (k : Z) : Z :=
  if (if Z.leb mtwo63z k then Z.ltb k two63z else false) then k
  else let m := Z.land k ones64z in if Z.leb two63z m then (m - two64z)%Z else m.
Lemma land_ones64z' : forall a, Z.land a ones64z = (a mod 2 ^ 64)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_AxSymExec3 ()) [] "h07__arithh14__ffh28__varmaph35__with41ap;1p;2p;4p;7p;3p-1R0p10000R1p4p710p8P0P1p4p7210p8P0p1000LR1p4p710p8P0P1p4p7210p8P0p1000ip4p7210p8g001Hj10Tg001mj1ATg002Kj13Tg002kj12Tg003Kj1@Tg003ij1:Tg004Gj14Tg0052j21Tg005Uj45Tg006@j76Tg006dj27Tg007Fj28Tg007`j29Tg008Lj3?Tg008fj3>Tg009Ej4;Tg00:7j2<Tg00:Sj3=Tg00;6R0f0R1g00;T#0#0#0#0#0#0#AR2g00<9R3#3%23%@0%:0%40R3g00<eg00=DR4P4g00=dR4P0g00>DR5,10g00>b1102C5g00?IF61734P1f2R4g00?iR3g00@IR6'81914=?36df19>05C;b1b2b31<52P1b03=W4o"). Qed.
Lemma snorm_eq : forall k, snorm k = snorm_ref k.
Proof.
ltac2:(KReplay.run1 (kr_t_AxSymExec3 ()) [] "p'0h04__x1h11Hh27__arithh34__ffh48__varmaph55__with62H0h72H4h82H5h92H6h:2H7h;2H8h<6__sat4h=6__sat5h>6__sat6h?6__sat7h@6__sat8hA1qhB1rhC1bi001bhD2b0hE2H9hF2HahG1zhH2H1hI2H2hJ2H3hK1BhL6__sat0hM6__sat1hN1kp%0p;1p;2p;3p;4p;6p;7p;8g001Hj1<Tg001mj1BTg00@ij2TTg00AFj23Tg00Afj1@Tg00BKj1sTg00Bhj27Tg00CEj2HTg00Cbj28Tg00D?j2QTg00Dgj20Tg00ECj3\Tg002Kj1xTg002kj1wTg003Kj1rTg003ij1oTg004Gj1lTg0052j2UTg00Egj1RTg00FEj3YTg006dj2cTg007Fj2JTg007`j2bTg008Lj3ITg008fj3aTg009Ej4`Tg00Fhj3_j2OTg00GOj2ATg00:7j24Tg00H1R0j3>Tg00HUj2^Tg00I7j3Pj2WTg00Ihj2GTg00JIj1]Tg00Jbj2;Tg00K?j2FTg00K\j26Tg00L9j2NTg00L`R1j2DTg00M;j2MTg00Maj2KTg00NGj2vTg00Nej2qTg00OHj1pTg00Ojj3ZTg00PMj3[Tg00Q0j6VTg00QNj2jTg00R1j3iTg00RTj6hTg00S8j4kTg00SYj6STg00T5j4gTg00TQj2mTg00Toj1nTg00V3j1fTg00Voj1eTg005Uj4LTg006@j7dTg00Woj8tTg00XSj7uTg00;6R2f1R3f0R43Ip=1g00>DR5/44p=2P2P3g00Y7P4CLp==P3g00<eR6g00=DR7P7g00=dR8P4g00?IFdp=5f2R91034'Dp=:AI245p=EP2P3g00>bP4CLp=CP2P3g00Y^P4CLp=?f3R:P6P7P7P8P9P3P4Gtp=9P9P6P7P7P8P3P4Fup=XP2g00;TR;#<R<#BR=%<<#<#<#<#<R<#BR>'TR?,34R@g00?iRAP2PAPA%@;#@#@#@#@RB#BRC,T=RD#sRE/73RF1H3Dg00ZERGn0100000020000P3PAP217D4184?P4n0100000020000RHn0100000020000PAP2133?RI,7D18I?PIn0100000020000'1XG21Q=>RI105=RJ%2>105?RK[[RL%2=RMg00ZeRNA\=>3UWFR>%2?RO\N^FMRPg00<9RQ#xRR%wQRQ%r2S00%o2RS%l2RT1U25RU1U2=RV%R<5Y2R<'='51cT8RWP4P9g00@IRX,JA1b49=IAXdAa253C`RXb3b4b5PKP4b2bLbM9_4?%2@?:@?1AE314E3R@103E;>F17E9PAP014E:10:EPAP2PAPAP3f5RF/HDRYPGn0100000020000PFPAP213F?RG,7D18G?PGn0100000020000RGn0100000020000/1GP3f4RZ,4E1^FD10FD14DF;>Yf6/HDPAP0f7RY/0D14DYPAP2P3f9RYPAP213Y?RF,7D18F?PFn0100000020000RFn0100000020000/1FP3f8S01/0D1A5Y%2Y10Y5175Y3>f:,75PAP0f;RY#210Y5f=RYPAP213Y?R[,7D18[?P[n0100000020000'1P3f<S02#2P2PYf>R\/1HXG21ADY14DY10YD17DY3>17D\PAP0f?R],4D10]DfAR^PAP2P318^?P^n0100000020000'1P3f@R_,4DAP^?ZS03fBR`/3?#2\OS041Q=CRa%2C105D[\JRJA\=C3VNXFMRC%2D\N^FMRMPIPLP>PPfFRN/G?S05%E?R=#]RbfGRc1;c?Rd,F?13c?Re'6'1[S061Oc?S07fHRf/3?Rg#2?:g?\KRh1Nf?Ri10?5RjfIRk/3?Rl,0?14l5'D[Rm1Mk?RnfJRo/;?#E\=Rp1Ko?RqfKRr/3?/1r\=Rs1;r?RtP2fLRu/3?RvP2P1%24Rw104?RxfNRy18y?'1Pu%29Rz10:?R:PRPQ1v23R{PSPT%RB9Y2VRV1q2;RB'C,5T%p7R|PT1=BV,5TS08P|AZ2B<,?B,5TC9C9PWPXb3b4b5X0214D4103DR}189?,19[[^02P4fRR~P^PkO3b2WEW;P3P4O2n2001000000121000000bBbAb:b9b8b7b6b<b=b>b?b@W1P4O110_DQ03Q04PaPJPCPMPIPLP>PPQ05Q06Q07PhPiPmPnPpPqPsPtP2PvP2P1PwPx11yyPuPRPQP{PS1?BB,5TPWPXb3b4b5X021144^02P4P~O1b2XE:X;zP3P4O2n2001000000120000000bBbAb:b9b8b7b6b<b=b>b?b@W1P4O1n200210000000021100011000bDbCP[APY?413\?S07#2\OPaPJPCPMPIPLP>PP1G`?S06fCR~1;~?,F?13~?'6'1\bS051O~?R~fDRs/3?Rq#2S04?:q?\KRq1Ns?RsfERp/3?Rn,0?14n5'D\jRn1Mp?Rm1;N?#E\=Ri1KN?RN11ec\=RePdP2PgP2P1PwPx%2o?:o?PfPRPQP{PSPT1CUB,5TRhP|PTQ08P|1=B<,5T9XThC9C9PWPXb3b4b5X02A:z9?\}\w^02P4PyP^PpO3b2X;:X:zP3P4O2n2001000000121000000bBbAb9b8b7b6b1b<b=b>b?b@9[Y?EVWJP4O1Q02/05P2P[16Y?RpP2%B;S02/F?,6Y/3?16\?R\,14XG21WY?S08%2Y13]?#2\O[R;PaPJPCPMPIPLP>PPQ06Q05P~PqPsPnPmPiPNPePdP2PgP2P1PwPx16o?R}#2?:}?PfPRPQP{PSPT1=BU,5TP|PT1j2V/CB,5TS03P|Ai2B<R},CU,5T1=}<,5T5XTC9C9PWPXb3b4b5X021045169?Rh#2?:h?\@[^02P4PyP^PkO3b2X;:X:zP3P4O2n2001000000121000000bBbAb9b8b7b6b1b<b=b>b?b@9[p?P[PYQ02P?Q08P;PaPJPCPMPIPLP>PPQ06Q05P~PqPsPnPmPiPNPePdP2PgP2P1PwPxPbPfPRPQQ00PSPTP6P7P7P81?<U,5TEhPWPXb3b4b5g00[A\=P4b2X;:X:zP3P4O2n2001000000120000000bBbAb9b8b7b6b1b<b=b>b?b@CkESCg11p[P2P\11]HXG21AD\14D\10\D17D\3>16]?,7DPAP016_?R_,4D10_DPAP2P316`?RA/8?PAn0100000020000,1`P316^?RA,4D1W`?R_%2`Q04\O[ROPaPJPCPMPIPLP>PP1Gc?Rc1;f?,F?/6g,1f\bRb1Of?Rf%2l?:l?\KRK1Nk?Rk13o?Rl,0?14l5'D\jRj1Mo?Ro%Et\=Rt1Kr?Rr11vu\=R=1;u?RuP2fMRv/3?RlP2P1PwPxfOR5165?Rg/8?'1PvPRPQP{PSAZ2}<,?B,5TPWPXb3b4b5X02164?R</8?,14^02P4fSR?O1b2XE:X;zP3P4O2n2001000000120000000bBbAb:b9b8b7b6b<b=b>b?b@W1P4O110ADP_POPaPJPCPMPIPLP>PPPcPbPfPKPkPjPoPtPrP=PuP2PlP2P1PwPx115gPvPRPQP{PSPT1=}V,5TP|PTQ03P|1?B},5TC9C9PWPXb3b4b5X0210<D119h\@[^02P4P?P^PyO3b2XE:X;zP3P4O2n2001000000121000000bBbAb:b9b8b7b6b<b=b>b?b@W1P4O1n200210000000021100011000bDbCQ07P4ESb1WJP4O1n200210000000021100011000bDbCWIP4O1Q01,4D1J2FWIP4O1n200210000000021100010000bDbCWHP4O110ZE1J2GWHP4O1n200210000000021100010000bDbCbKg00[^,m4%n4EV%f4%e4'1eXN2o"). Qed.

(* [comment removed for export] *)
Definition zmod64 (z : Z) : Z :=
  if (if Z.leb 0 z then Z.ltb z two64z else false) then z else Z.land z ones64z.
Lemma zmod64_eq : forall z, zmod64 z = (z mod 2 ^ 64)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_AxSymExec3 ()) [] "p'0h01Hh12H0h22Hah34__x1h41bi001bh52b0h61zh77__arithh84__ffh96__sat1h:6__sat2h;8__varmaph<5__witp;1p;2p;3p;4p;7p;6p;8g001Hj12Tg001mj1=Tg00@ij2HTg00AFj24Tg00Bhj2>Tg00CEj27Tg008Lj33Tg00GOj2GTg00Dgj20Tg00H1R0j3<Tg00HUj2@Tg00:7j25Tg00D?j2ZTg00ECj3VTg002Kj1UTg002kj1RTg00NGj2QTg003ij1LTg004Gj1KTg00Nej2JTg0052j2;Tg00Egj1FTg00FEj3ETg005Uj49Tg00OHj1DTg00XSj7ITg006dj2CTg007Fj26Tg007`j2BTg008fj3ATg009Ej4MTg00L`j2NTg00PMj3OTg00T5j4PTg00TQj2?Tg00Toj1STg00Q0j6TTg00\\j1YTg006@j7XTg00Woj8WTg00>DR1f0R2'5p=1f1R3g00<eR4g00=DR5P5g00=dR6P2g00?IFXp=:f3R7P4P5P5P6f2R8P3P2GWp=8g00;6R9P9g00;TR:#2R;#=R<%2;#2#2#2#2R;#=R='HR>,42R?g00?iR@P9P@P@1>13RA173>g00ZERBn0100000020000P3P2n0100000020000143>539X691G12%1210211>123<PAP@P0%18RA1081P@P9P@P@P3f4RC/7>RDPBn0100000020000PC14C>RBn0100000020000=39BP3%171@C>10C>15>C;<Df5/7>P@P0f6R0/0>15>0P@P9P3f8R0140>RDn0100000020000=39DP3f7RC/0>P9PDP01Z<=101<%1=101>[[%1<REg00ZeRFAV<=3UW2%1>\F^2Eg00<9RE#U%RE1Q93%L9%K9REP91J9:R:g00Y71;9<%F;5E9C9,:ER;%D5R<PEP91;91g00>bP:C9,:ER:P<PEP4P5P5P6P:P;FIC8C81CE6P2P8g00@IRE,6@1B28=3@EdAA913CMb8b;b<X39102>%13108>,NA[[^39P2f;P7PCO3b7b9b:9O0>CPW1P2O115>C169DW1P2O1n200210000000021100010000b5b4W0P2O11071169BW0P2O1n200210000000021100010000b5b4g00[^,?2%S2ET%Y2=39?eW6o"). Qed.
Definition zdiv64 (z : Z) : Z :=
  if (if Z.leb 0 z then Z.ltb z two64z else false) then 0 else Z.shiftr z 64.
Lemma zdiv64_eq : forall z, zdiv64 z = (z / 2 ^ 64)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_AxSymExec3 ()) [] "p'0h01Hh12H0h22Hah37__arithh44__ffh56__sat1h66__sat2h78__varmaph85__with94__x1h:1bi001bh;2b0h<1zp;2p;3p;1p;4p;7p;8g00GOj2ZTg00Dgj20Tg00Bhj2=Tg00H1R0j3?Tg001Hj12Tg001mj1<Tg00@ij2HTg00CEj29Tg00]Yj2;Tg00Jbj25Tg008Lj33Tg00HUj2@Tg00:7j24Tg00D?j2VTg00ECj3UTg002Kj1TTg002kj1STg00NGj2NTg003ij1LTg004Gj1KTg00Nej2ITg0052j26Tg00Egj1GTg00FEj3FTg005Uj47Tg00OHj1ETg00XSj7DTg006dj2JTg007Fj2CTg007`j2BTg008fj3MTg009Ej4ATg00L`j2OTg00^9j3PTg00T5j4QTg003Kj1RTg00^\j3>Tg00_Ej1YTg006@j7XTg00Woj8WTg00>DR1f0R2'4p=1f1R3g00<eR4g00=DR5P5g00=dR6P2g00?IFXp=8f3R7P4P5P5P6f2R8P3P2GWp=:g00;6R91Z12%1210211=123?1=13g00?iR:P0%18R;1081P:P9P:P:P3f4R<g00;TR=#2R>#<R?%2>#2#2#2#2R>#<R@'HRA'9RBg00ZEn0100000020000P11;<@n010000002000015<A539P3%171@<A10<A14A<;?Bf5/9AP:P0f6R0/0A14A0P:P9P3P1f8R0/;@n0100000020000150ARB539P3f7RC/0AP9PBP11V?@RB101?%1@RD101A[[RE%1?RFg00ZeRGAU?@3UW2RH%1A\G^2FRFg00<9RG#TRI%SGRG1N93%L9RJ%K9RKP91I9=R=g00Y7169?%G>5F9C7,8KR>%E5R?PKP91691RLg00>bRMP=C7,8KR=P?PKP4P5P5P6P=P>FDC:C:1JK6R6P2P8g00@IR>,C:1B28=3:>dAM913CAR>b4b7b8X99102A%13108A,O;[[^99P2f;P7PCO3b3b5b69P0ACQW1P2O114ACPBPEPHPFPIPG%R9PJP9PLPM169@C7,8KP6P>b4b7b8PDP2b3RDb5b69>0@W1P2O1n200210000000021100010000b;b:W0P2O11071A><@DW0P2O1n200210000000021100010000b;b:%Y2152A539eW<o"). Qed.

(* [comment removed for export] *)
Definition wrap64 (z : Z) : Z :=
  if (Z.leb 0 z && Z.ltb z two64)%bool then z else (z mod two64)%Z.

Definition sx32 (r : Z) : Z :=
  if Z.ltb r 2147483648 then r else (r + 18446744069414584320)%Z.

(* [comment removed for export] *)
Definition ones32z : Z := Z.ones 32.
Definition land64 (z : Z) : Z :=
  if (Z.leb 0 z && Z.ltb z two64)%bool then z else Z.land z ones64z.
Definition land32 (z : Z) : Z :=
  if (Z.leb 0 z && Z.ltb z two32z)%bool then z else Z.land z ones32z.

Definition zfast (op : aluop) (x y : Z) : Z :=
  match op with
  | ALU_ADD => let t := (x + y)%Z in if Z.ltb t two64 then t else (t - two64)%Z
  | ALU_SUB => let t := (x - y)%Z in if Z.leb 0 t then t else (t + two64)%Z
  | ALU_AND => Z.land x y
  | ALU_OR => Z.lor x y
  | ALU_XOR => Z.lxor x y
  | ALU_SRL => Z.shiftr x (Z.land y 63)
  | ALU_SLL => land64 (Z.shiftl x (Z.land y 63))
  | ALU_SLTU => if Z.ltb x y then 1%Z else 0%Z
  | _ => zalu op x y
  end.

Definition zfastw (op : aluop) (x y : Z) : Z :=
  match op with
  | ALU_ADD => sx32 (land32 (x + y))
  | ALU_SUB => sx32 (land32 (x - y))
  | ALU_SRL => sx32 (Z.shiftr (land32 x) (Z.land y 31))
  | ALU_SLL => sx32 (land32 (Z.shiftl (land32 x) (Z.land y 31)))
  | _ => zaluw op x y
  end.

Definition zfastm (op : mulop) (x y : Z) : Z :=
  match op with
  | M_MUL => land64 (x * y)
  | _ => zmd op x y
  end.

(* [comment removed for export] *)
Definition zext_fast (sx : bool) (lo n : nat) (x : Z) : Z :=
  let k := (8 * Z.of_nat n)%Z in
  let u := Z.land (Z.shiftr x (8 * Z.of_nat lo)) (Z.ones k) in
  if sx then match n with
             | O => wrap64 u
             | _ => if Z.ltb u (Z.shiftl 1 (k - 1)) then wrap64 u else wrap64 (u - Z.shiftl 1 k + two64)
             end
  else wrap64 u.

(* [comment removed for export] *)
Definition zalu_l (op : aluop) (x y : Z) : Z := zfast op (wrap64 x) (wrap64 y).
Definition zaluw_l (op : aluop) (x y : Z) : Z := zfastw op (wrap64 x) (wrap64 y).
Definition zmd_l (op : mulop) (x y : Z) : Z := zfastm op (wrap64 x) (wrap64 y).

Definition lin : Type := (Z * list (Z * expr))%type.

Definition ctor_ix (e : expr) : nat :=
  match e with
  | ELit _ => 0 | EVar _ => 1 | EAlu _ _ _ => 2 | EAluw _ _ _ => 3
  | EMd _ _ _ => 4 | EMdw _ _ _ => 5 | EExt _ _ _ _ => 6 | EBlob _ _ _ _ => 7
  end.
Definition aluop_ix (op : aluop) : nat :=
  match op with
  | ALU_ADD => 0 | ALU_SUB => 1 | ALU_SLL => 2 | ALU_SLT => 3 | ALU_SLTU => 4
  | ALU_XOR => 5 | ALU_SRL => 6 | ALU_SRA => 7 | ALU_OR => 8 | ALU_AND => 9
  end.
Definition mulop_ix (op : mulop) : nat :=
  match op with
  | M_MUL => 0 | M_MULH => 1 | M_MULHSU => 2 | M_MULHU => 3
  | M_DIV => 4 | M_DIVU => 5 | M_REM => 6 | M_REMU => 7
  end.
Definition bool_ix (b : bool) : nat := if b then 1 else 0.
Definition lexc (c k : comparison) : comparison := match c with Eq => k | _ => c end.

Fixpoint expr_cmp (x y : expr) {struct x} : comparison :=
  match x, y with
  | ELit a, ELit b => Z.compare a b
  | EVar a, EVar b => Nat.compare a b
  | EAlu o a b, EAlu o' a' b' =>
      lexc (Nat.compare (aluop_ix o) (aluop_ix o')) (lexc (expr_cmp a a') (expr_cmp b b'))
  | EAluw o a b, EAluw o' a' b' =>
      lexc (Nat.compare (aluop_ix o) (aluop_ix o')) (lexc (expr_cmp a a') (expr_cmp b b'))
  | EMd o a b, EMd o' a' b' =>
      lexc (Nat.compare (mulop_ix o) (mulop_ix o')) (lexc (expr_cmp a a') (expr_cmp b b'))
  | EMdw o a b, EMdw o' a' b' =>
      lexc (Nat.compare (mulop_ix o) (mulop_ix o')) (lexc (expr_cmp a a') (expr_cmp b b'))
  | EExt s l n e, EExt s' l' n' e' =>
      lexc (Nat.compare (bool_ix s) (bool_ix s'))
           (lexc (Nat.compare l l') (lexc (Nat.compare n n') (expr_cmp e e')))
  | EBlob s k i n, EBlob s' k' i' n' =>
      lexc (Nat.compare (bool_ix s) (bool_ix s'))
           (lexc (Nat.compare k k') (lexc (Z.compare i i') (Nat.compare n n')))
  | _, _ => Nat.compare (ctor_ix x) (ctor_ix y)
  end.

(* [comment removed for export] *)
Fixpoint lins (k : Z) (a : expr) (ts : list (Z * expr)) : list (Z * expr) :=
  match ts with
  | [] => if Z.eqb (snorm k) 0 then [] else [(snorm k, a)]
  | (k', a') :: rest =>
      if expr_eqb a a' then
        (let s := snorm (k + k') in if Z.eqb s 0 then rest else (s, a') :: rest)
      else match expr_cmp a a' with
           | Lt => if Z.eqb (snorm k) 0 then ts else (snorm k, a) :: ts
           | _ => (k', a') :: lins k a rest
           end
  end.

Definition ladd (x y : lin) : lin :=
  (snorm (fst x + fst y), fold_right (fun t acc => lins (fst t) (snd t) acc) (snd y) (snd x)).

Fixpoint lscale_terms (m : Z) (ts : list (Z * expr)) : list (Z * expr) :=
  match ts with
  | [] => []
  | (k, a) :: rest =>
      let k' := snorm (m * k) in
      if Z.eqb k' 0 then lscale_terms m rest else (k', a) :: lscale_terms m rest
  end.

Definition lscale (m : Z) (x : lin) : lin := (snorm (m * fst x), lscale_terms m (snd x)).

(* [comment removed for export] *)
Fixpoint lin_of (e : expr) : lin :=
  match e with
  | ELit z => (snorm z, [])
  | EAlu ALU_ADD a b => ladd (lin_of a) (lin_of b)
  | EAlu ALU_SUB a b => ladd (lin_of a) (lscale (-1) (lin_of b))
  | EAlu ALU_SLL a (ELit s) => lscale (2 ^ (s mod 64)) (lin_of a)
  | EMd M_MUL (ELit k) a => lscale k (lin_of a)
  | EMd M_MUL a (ELit k) => lscale k (lin_of a)
  | _ => (0%Z, [(1%Z, e)])
  end.

Definition lterm (t : Z * expr) : expr :=
  if Z.eqb (fst t) 1 then snd t else EMd M_MUL (ELit (fst t)) (snd t).

Fixpoint lterms (ts : list (Z * expr)) : expr :=
  match ts with
  | [] => ELit 0
  | [t] => lterm t
  | t :: rest => EAlu ALU_ADD (lterm t) (lterms rest)
  end.

Definition unlin (x : lin) : expr :=
  match snd x with
  | [] => ELit (fst x)
  | _ => if Z.eqb (fst x) 0 then lterms (snd x) else EAlu ALU_ADD (lterms (snd x)) (ELit (fst x))
  end.

(* [comment removed for export] *)
Fixpoint coeffs_div (m : Z) (ts : list (Z * expr)) : bool :=
  match ts with
  | [] => true
  | (k, _) :: rest => (Z.eqb (k mod m) 0 && coeffs_div m rest)%bool
  end.

Definition lin_lowbits (e : expr) (k : Z) : option Z :=
  let l := lin_of e in
  if coeffs_div (2 ^ k) (snd l) then Some ((fst l) mod 2 ^ k)%Z else None.

(* [comment removed for export] *)
Definition shamt_of (e : expr) (bits : Z) : option Z :=
  match e with
  | ELit s => Some (s mod 2 ^ bits)%Z
  | _ => lin_lowbits e bits
  end.

Definition mkAlu (op : aluop) (a b : expr) : expr :=
  match is_lit a, is_lit b with
  | Some x, Some y => ELit (zalu_l op x y)
  | _, _ =>
    match op with
    | ALU_ADD => unlin (ladd (lin_of a) (lin_of b))
    | ALU_SUB => unlin (ladd (lin_of a) (lscale (-1) (lin_of b)))
    | ALU_SLL => match shamt_of b 6 with
                 | Some s => unlin (lscale (2 ^ s) (lin_of a))
                 | None => EAlu op a b
                 end
    | ALU_SRL | ALU_SRA => match is_lit b with
                           | Some _ => EAlu op a b
                           | None => match shamt_of b 6 with
                                     | Some s => EAlu op a (ELit s)
                                     | None => EAlu op a b
                                     end
                           end
    | _ => EAlu op a b
    end
  end.

Definition mkAluw (op : aluop) (a b : expr) : expr :=
  match is_lit a, is_lit b with
  | Some x, Some y => ELit (zaluw_l op x y)
  | _, _ =>
      match op with
      | ALU_SLL | ALU_SRL | ALU_SRA =>
          match is_lit b with
          | Some _ => EAluw op a b
          | None => match shamt_of b 5 with
                    | Some s => match is_lit a with
                                | Some x => ELit (zaluw_l op x s)
                                | None => EAluw op a (ELit s)
                                end
                    | None => EAluw op a b
                    end
          end
      | _ => EAluw op a b
      end
  end.

Definition mkMd (op : mulop) (a b : expr) : expr :=
  match is_lit a, is_lit b with
  | Some x, Some y => ELit (zmd_l op x y)
  | Some x, None => match op with M_MUL => unlin (lscale x (lin_of b)) | _ => EMd op a b end
  | None, Some y => match op with M_MUL => unlin (lscale y (lin_of a)) | _ => EMd op a b end
  | _, _ => EMd op a b
  end.

Definition mkMdw (op : mulop) (a b : expr) : expr :=
  match is_lit a, is_lit b with
  | Some x, Some y => ELit (zmdw op x y)
  | _, _ => EMdw op a b
  end.

(* [comment removed for export] *)
Definition mkExt (sx : bool) (lo n : nat) (e : expr) : expr :=
  match e with
  | ELit x => ELit (zext_fast sx lo n (wrap64 x))   (* [comment removed for export] *)
  | _ =>
    if (Nat.eqb lo 0 && Nat.eqb n 8)%bool then e
    else match e with
         | EExt false lo' n' e' =>
             if (Nat.leb (lo + n) n' && Nat.leb n' 8)%bool then EExt sx (lo' + lo) n e'
             else EExt sx lo n e
         | _ => EExt sx lo n e
         end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ridx (r : reg) : nat := Z.to_nat (bv_unsigned r).

Definition sr_get (sr : list expr) (r : reg) : expr :=
  if bv_eqb r 0 then ELit 0 else nth (ridx r) sr (ELit 0).

Fixpoint sr_upd (sr : list expr) (n : nat) (e : expr) : list expr :=
  match n with
  | O => match sr with [] => [e] | _ :: t => e :: t end
  | S n' => match sr with
            | [] => ELit 0 :: sr_upd [] n' e
            | h :: t => h :: sr_upd t n' e
            end
  end.

Definition sr_id : list expr :=
  [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7;
   EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15;
   EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23;
   EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record saddr : Type := SA { a_base : expr; a_off : Z }.

Definition split_lit (e : expr) : expr * Z :=
  match e with
  | ELit z => (ELit 0, z)
  | EAlu ALU_ADD b (ELit z) => (b, z)
  | _ => (e, 0%Z)
  end.

Definition to_saddr (e : expr) (imm : Z) : saddr :=
  let (b, k) := split_lit e in SA b (k + imm).

Definition adenot (E : env) (a : saddr) : word :=
  v_addi (edenot E (a_base a)) (a_off a).

Definition saddr_eqb (a b : saddr) : bool :=
  expr_eqb (a_base a) (a_base b) && Z.eqb (a_off a) (a_off b).

(* [comment removed for export] *)
Record sentry : Type := SE { e_addr : saddr; e_width : nat; e_val : expr }.

(* [comment removed for export] *)
Inductive kentry : Type :=
| KWord (a : saddr) (w : nat) (v : expr)      (* [comment removed for export] *)
| KZero (a : saddr) (n : expr)                (* [comment removed for export] *)
| KBlob (a : saddr) (n : expr) (k : nat)      (* [comment removed for export] *)
| KImg  (lo hi : Z)                           (* [comment removed for export] *)
| KAlign (e : expr) (m : Z)                   (* [comment removed for export] *)
| KRange (e : expr) (lo hi : Z)               (* [comment removed for export] *)
| KWr (a : saddr) (n : expr)                  (* [comment removed for export] *)
| KDisj (a1 : saddr) (n1 : expr) (a2 : saddr) (n2 : expr)
                                              (* [comment removed for export] *)
| KFill (a : saddr) (n : expr) (c : Z)        (* [comment removed for export] *)
| KUnk (a : saddr) (n : expr).                 (* [comment removed for export] *)

(* [comment removed for export] *)
Inductive sidecond : Type :=
| SCBr       (taken : bool) (c : branch_cond) (a b : expr)
| SCFlat     (a : saddr) (n : expr)                     (* [comment removed for export] *)
| SCDisj     (a1 : saddr) (n1 : expr) (a2 : saddr) (n2 : expr)  (* [comment removed for export] *)
| SCInside   (a1 : saddr) (n1 : expr) (a2 : saddr) (n2 : expr)  (* [comment removed for export] *)
| SCStoreOk  (a : saddr) (n : nat)                      (* [comment removed for export] *)
| SCReadBase (a : saddr) (n : nat) (sx : bool) (e : expr)  (* [comment removed for export] *)
| SCEq       (a b : expr).                              (* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint log_rm (a : saddr) (n : nat) (log : list sentry) : list sentry :=
  match log with
  | [] => []
  | SE a' n' v' :: rest =>
      (* [comment removed for export] *)
      if (Z.eqb (a_off a) (a_off a') && Nat.eqb n n' && expr_eqb (a_base a) (a_base a'))%bool then rest else SE a' n' v' :: log_rm a n rest
  end.
Definition log_push (a : saddr) (n : nat) (v : expr) (log : list sentry) : list sentry := SE a n v :: log_rm a n log.

Record sym_state : Type := SSR {
  s_pc   : Z;
  s_regs : list expr;
  s_log  : list sentry;       (* [comment removed for export] *)
  s_know : list kentry;
  s_next : nat;               (* [comment removed for export] *)
  s_resv : option saddr       (* [comment removed for export] *)
}.

(* [comment removed for export] *)
Abbreviation SS p r l k n := (SSR p r l k n None).

Definition sset (ss : sym_state) (rd : reg) (e : expr) (npc : Z) : sym_state :=
  SSR npc (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) e)
     (s_log ss) (s_know ss) (s_next ss) (s_resv ss).

Definition sjump (ss : sym_state) (npc : Z) : sym_state :=
  SSR npc (s_regs ss) (s_log ss) (s_know ss) (s_next ss) (s_resv ss).

(* [comment removed for export] *)
Definition clr (ss : sym_state) : sym_state :=
  SSR (s_pc ss) (s_regs ss) (s_log ss) (s_know ss) (s_next ss) None.
Definition s_clean (ss : sym_state) : bool :=
  match s_resv ss with None => true | Some _ => false end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive rangerel := RInside (delta : Z) | RDisjoint | RPartial | RUnknown.

(* [comment removed for export] *)
Definition rel_lit (rb : expr) (rk : Z) (rn : Z) (kb : expr) (kk : Z) (kn : Z) : rangerel :=
  if expr_eqb rb kb then
    if (Z.leb kk rk && Z.leb (rk + rn) (kk + kn))%bool then RInside (rk - kk)
    else if (Z.leb (rk + rn) kk || Z.leb (kk + kn) rk)%bool then RDisjoint
    else RPartial
  else RUnknown.

Definition elen (n : nat) : expr := ELit (Z.of_nat n).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition lit_strip (e : expr) : expr * Z :=
  match e with
  | EAlu ALU_ADD v (ELit c) => (v, c)
  | _ => (e, 0%Z)
  end.
Fixpoint find_range (kn : list kentry) (e : expr) : option (Z * Z) :=
  match kn with
  | [] => None
  | KRange e' lo hi :: rest =>
      if expr_eqb e e' then Some (lo, hi) else
      match e with
      | ELit _ => find_range rest e
      | _ =>
        let '(v, c) := lit_strip e in
        let '(v', c') := lit_strip e' in
        if expr_eqb v v' then
          let d := (c - c')%Z in
          if (Z.leb 0 lo && Z.leb lo hi && Z.ltb hi (2 ^ 64) && Z.leb 0 (lo + d) && Z.ltb (hi + d) (2 ^ 64))%bool
          then Some ((lo + d)%Z, (hi + d)%Z) else find_range rest e
        else find_range rest e
      end
  | _ :: rest => find_range rest e
  end.

(* [comment removed for export] *)
Fixpoint find_align (kn : list kentry) (e : expr) : option Z :=
  match kn with
  | [] => None
  | KAlign e' m :: rest => if expr_eqb e e' then Some m else find_align rest e
  | _ :: rest => find_align rest e
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma zmod64_eq2 : forall z, zmod64 z = (z mod two64)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_AxSymExec3 ()) [] "g00`Bo"). Qed.
Lemma zdiv64_eq2 : forall z, zdiv64 z = (z / two64)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_AxSymExec3 ()) [] "g00aBo"). Qed.

Definition clampi (r : Z * Z) : Z * Z :=
  let (lo, hi) := r in (Z.max lo 0, Z.min hi two64m1).

(* [comment removed for export] *)
Definition mask_cover (h : Z) : Z :=
  if Z.ltb h 0 then 0 else (2 ^ (Z.log2_up (h + 1)) - 1)%Z.

Definition lit_shamt (e : expr) : option Z :=
  match e with ELit s => Some (s mod 64)%Z | _ => None end.

(* [comment removed for export] *)
Definition zsigned64 (v : Z) : Z := if Z.leb two63z v then (v - two64)%Z else v.

(* [comment removed for export] *)
Fixpoint lin_range (rng : expr -> option (Z * Z)) (c : Z) (ts : list (Z * expr)) : option (Z * Z) :=
  match ts with
  | [] => Some (c, c)
  | (k, a) :: rest =>
      match rng a, lin_range rng c rest with
      | Some (al, ah), Some (lo, hi) =>
          if Z.leb 0 k then Some ((lo + k * al)%Z, (hi + k * ah)%Z)
          else Some ((lo + k * ah)%Z, (hi + k * al)%Z)
      | _, _ => None
      end
  end.

Definition lin_trivial (l : lin) : bool :=
  match l with
  | (c, [(k, _)]) => (Z.eqb c 0 && Z.eqb k 1)%bool
  | _ => false
  end.

Fixpoint erange_f (fuel : nat) (kn : list kentry) (e : expr) {struct fuel} : option (Z * Z) :=
  match fuel with
  | O => None
  | S fuel' =>
  let erange := erange_f fuel' in
  match find_range kn e with
  | Some r => Some (clampi r)
  | None =>
  match (let l := lin_of e in
         if lin_trivial l then None
         else match lin_range (erange kn) (fst l) (snd l) with
              | Some (lo, hi) =>
                  (* [comment removed for export] *)
                  let q := zdiv64 lo in   (* [comment removed for export] *)
                  if Z.eqb q (zdiv64 hi) then Some ((lo - q * two64)%Z, (hi - q * two64)%Z) else None
              | None => None
              end) with
  | Some r => Some r
  | None =>
  match e with
  | ELit z => let v := zmod64 z in Some (v, v)   (* [comment removed for export] *)
  | EVar _ => None
  | EAlu op a b =>
      match op with
      | ALU_ADD =>
          match erange kn a, erange kn b with
          | Some (al, ah), Some (bl, bh) =>
              if Z.ltb (ah + bh) two64 then Some ((al + bl)%Z, (ah + bh)%Z)
              else if Z.leb two64 (al + bl) then Some ((al + bl - two64)%Z, (ah + bh - two64)%Z)
              else None
          | _, _ => None
          end
      | ALU_SUB =>
          match erange kn a, erange kn b with
          | Some (al, ah), Some (bl, bh) =>
              if Z.leb bh al then Some ((al - bh)%Z, (ah - bl)%Z)
              else if Z.ltb ah bl then Some ((al - bh + two64)%Z, (ah - bl + two64)%Z)
              else None
          | _, _ => None
          end
      | ALU_AND =>
          (* [comment removed for export] *)
          match (match b, erange kn a with
                 | ELit m, Some (al, ah) =>
                     let m' := (m mod two64)%Z in
                     let j := Z.log2 (m' + 1) in
                     if (Z.eqb (m' + 1) (2 ^ j) && Z.leb (al / 2 ^ j) (ah / 2 ^ j) && Z.eqb (al / 2 ^ j) (ah / 2 ^ j))%bool
                     then Some ((al mod 2 ^ j)%Z, (ah mod 2 ^ j)%Z)
                     else let jh := Z.log2 (two64 - m') in
                          if (Z.eqb (two64 - m') (2 ^ jh) && Z.ltb jh 64)%bool
                          then Some ((al - al mod 2 ^ jh)%Z, (ah - ah mod 2 ^ jh)%Z)
                          else None
                 | _, _ => None
                 end) with
          | Some r => Some r
          | None =>
          match erange kn a, erange kn b with
          | Some (_, ah), Some (_, bh) => Some (0%Z, Z.min ah bh)
          | Some (_, ah), None => Some (0%Z, ah)
          | None, Some (_, bh) => Some (0%Z, bh)
          | None, None => None
          end
          end
      | ALU_OR =>
          match erange kn a, erange kn b with
          | Some (al, ah), Some (bl, bh) => Some (Z.max al bl, mask_cover (Z.max ah bh))
          | _, _ => None
          end
      | ALU_XOR =>
          match erange kn a, erange kn b with
          | Some (_, ah), Some (_, bh) => Some (0%Z, mask_cover (Z.max ah bh))
          | _, _ => None
          end
      | ALU_SRL =>
          match erange kn a, lit_shamt b with
          | Some (al, ah), Some s => Some ((al / 2 ^ s)%Z, (ah / 2 ^ s)%Z)
          | _, _ => None
          end
      | ALU_SRA =>
          match erange kn a, lit_shamt b with
          | Some (al, ah), Some s =>
              if Z.ltb ah (2 ^ 63) then Some ((al / 2 ^ s)%Z, (ah / 2 ^ s)%Z) else None
          | _, _ => None
          end
      | ALU_SLL =>
          match erange kn a, lit_shamt b with
          | Some (al, ah), Some s =>
              if Z.ltb (ah * 2 ^ s) two64 then Some ((al * 2 ^ s)%Z, (ah * 2 ^ s)%Z) else None
          | _, _ => None
          end
      | ALU_SLTU =>
          match erange kn a, erange kn b with
          | Some (al, ah), Some (bl, bh) =>
              if Z.ltb ah bl then Some (1%Z, 1%Z)
              else if Z.leb bh al then Some (0%Z, 0%Z) else Some (0%Z, 1%Z)
          | _, _ => Some (0%Z, 1%Z)
          end
      | ALU_SLT =>
          match erange kn a, erange kn b with
          | Some (al, ah), Some (bl, bh) =>
              if (Z.ltb ah (2 ^ 63) && Z.ltb bh (2 ^ 63))%bool then
                (if Z.ltb ah bl then Some (1%Z, 1%Z)
                 else if Z.leb bh al then Some (0%Z, 0%Z) else Some (0%Z, 1%Z))
              else Some (0%Z, 1%Z)
          | _, _ => Some (0%Z, 1%Z)
          end
      end
  | EAluw op a b =>
      match op with
      | ALU_ADD =>
          match erange kn a, erange kn b with
          | Some (al, ah), Some (bl, bh) =>
              let bl' := if Z.eqb bl bh then zsigned64 bl else bl in
              let bh' := if Z.eqb bl bh then zsigned64 bh else bh in
              if (Z.leb 0 (al + bl') && Z.ltb (ah + bh') (2 ^ 31))%bool
              then Some ((al + bl')%Z, (ah + bh')%Z) else None
          | _, _ => None
          end
      | ALU_SUB =>
          match erange kn a, erange kn b with
          | Some (al, ah), Some (bl, bh) =>
              if (Z.leb bh al && Z.ltb (ah - bl) (2 ^ 31))%bool
              then Some ((al - bh)%Z, (ah - bl)%Z) else None
          | _, _ => None
          end
      | ALU_SLL =>
          match erange kn a, lit_shamt b with
          | Some (al, ah), Some s =>
              let s' := (s mod 32)%Z in
              if Z.ltb (ah * 2 ^ s') (2 ^ 31) then Some ((al * 2 ^ s')%Z, (ah * 2 ^ s')%Z) else None
          | _, _ => None
          end
      | ALU_SRL =>
          match erange kn a, lit_shamt b with
          | Some (al, ah), Some s =>
              let s' := (s mod 32)%Z in
              if (Z.ltb ah (2 ^ 32) && (Z.ltb 0 s' || Z.ltb ah (2 ^ 31)))%bool
              then Some ((al / 2 ^ s')%Z, (ah / 2 ^ s')%Z) else None
          | _, _ => None
          end
      | ALU_SRA =>
          match erange kn a, lit_shamt b with
          | Some (al, ah), Some s =>
              let s' := (s mod 32)%Z in
              if Z.ltb ah (2 ^ 31) then Some ((al / 2 ^ s')%Z, (ah / 2 ^ s')%Z) else None
          | _, _ => None
          end
      | _ => None
      end
  | EMd op a b =>
      match op with
      | M_MUL =>
          match erange kn a, erange kn b with
          | Some (al, ah), Some (bl, bh) =>
              if (Z.leb 0 al && Z.leb 0 bl && Z.ltb (ah * bh) two64)%bool
              then Some ((al * bl)%Z, (ah * bh)%Z) else None
          | _, _ => None
          end
      | M_MULHU =>
          match erange kn a, erange kn b with
          | Some (al, ah), Some (bl, bh) =>
              if (Z.leb 0 al && Z.leb 0 bl)%bool
              then Some ((al * bl / two64)%Z, (ah * bh / two64)%Z) else None
          | _, _ => None
          end
      | M_DIVU =>
          match erange kn a, b with
          | Some (al, ah), ELit d =>
              let d' := (d mod two64)%Z in
              if Z.ltb 0 d' then Some ((al / d')%Z, (ah / d')%Z) else None
          | _, _ => None
          end
      | M_REMU =>
          match erange kn a, b with
          | Some (al, ah), ELit d =>
              let d' := (d mod two64)%Z in
              if Z.ltb 0 d' then Some (0%Z, Z.min ah (d' - 1)) else None
          | _, _ => None
          end
      | _ => None
      end
  | EMdw _ _ _ => None
  | EExt sx lo n a =>
      let w := (2 ^ (8 * Z.of_nat n))%Z in
      if sx then
        match lo, erange kn a with
        | O, Some (al, ah) =>
            if (Z.leb 0 al && Z.ltb ah (w / 2))%bool then Some (al, ah)
            else if (Nat.leb 1 n && Nat.leb n 8 && Z.leb (w / 2) al && Z.ltb ah w)%bool
                 then Some ((two64 - w + al)%Z, (two64 - w + ah)%Z) else None
        | _, _ => None
        end
      else
        match lo, erange kn a with
        | O, Some (al, ah) =>
            if (Z.leb 0 al && Z.ltb ah w)%bool then Some (al, ah) else Some (0%Z, Z.min (w - 1) (two64 - 1))
        | _, _ => Some (0%Z, Z.min (w - 1) (two64 - 1))
        end
  | EBlob sx k i n =>
      (* [comment removed for export] *)
      if sx then Some (0%Z, two64m1) else Some (0%Z, Z.min (2 ^ (8 * Z.of_nat n) - 1) (two64 - 1))%Z
  end
  end
  end
  end.

(* [comment removed for export] *)
Definition erange_fuel : nat := 64%nat.
Global Opaque erange_fuel.
(* [comment removed for export] *)
Definition is_factb (K : kentry) : bool :=
  match K with KRange _ _ _ | KAlign _ _ | KDisj _ _ _ _ | KWr _ _ => true | _ => false end.
(* [comment removed for export] *)
Fixpoint all_factsb (kn : list kentry) : bool :=
  match kn with [] => true | K :: rest => if is_factb K then all_factsb rest else false end.
Definition facts_of (kn : list kentry) : list kentry :=
  if all_factsb kn then kn else List.filter is_factb kn.
Lemma all_factsb_filter : forall kn, all_factsb kn = true -> List.filter is_factb kn = kn.
Proof.
ltac2:(KReplay.run1 (kr_t_AxSymExec3 ()) [] "p'0h01Hh12knh22H0h32IHh41Kh51bi001bh61eh71lh84restp;1p;3p;2p;6p;5g002kj1>Tg00bBj14Tg008Lj30Tg002Kj1;Tg007Fj25Tg00cCR0j18Tg00Q0j67Tg00SYj66Tg00dBj29Tg00daj5:Tg00eCj3=Tg00e^j3<Tg00?iR1f0R2g00@IR330p=2g00f>R4?=02p=3f1R0=<42p=1%>4R5P4%42#2%30=050[R6X15A0133%;4R7,55U%47#2%37=057[ef2R7#8P1P1P1P1P2f3R8#4g00ZER9n0100000020000#2P1P5P0f5R:f4R;#3R<'1P<n010000002000011:;R=505[P2%47#2P5P811:2=05=X7511;8,55%38P7P2O1E7W0A0193P1P9P1p-0P2g00[AR9g00Zen0110000020000X61g00g=P3P2E6P9A05<=/92b2W0n0110000020000b51170#4#21187R8#3=058[eX36X85X44P2D:W1o"). Qed.
Lemma facts_of_filter : forall kn, facts_of kn = List.filter is_factb kn.
Proof.
ltac2:(KReplay.run1 (kr_t_AxSymExec3 ()) [] "p'0h01Eh11bi001bh22knp;1p;2p;3p;4g002kj18Tg00bBj11Tg007Fj23Tg008Lj30Tg00gYj27Tg00T5j46Tg00haj14Tg00eCj35Tg00f>R0g00cCf0R135p=2%80R0%11g00?iR21321f1R3#1=021P2f3R4#1=021P2P0P3f4R5%25R5n0100000020000=005]0P3f2#1R3g00@I502P0%24R5P41741C6W0g00ZE90231305W0n0110000020000P1O1b0b1%41%21500eW2o"). Qed.
Definition erange0 (kn : list kentry) (e : expr) : option (Z * Z) := erange_f erange_fuel (facts_of kn) e.

(* [comment removed for export] *)
Fixpoint deand (e : expr) : expr * Z :=
  match e with
  | EAlu ALU_AND x (ELit m) =>
      let m' := (m mod two64)%Z in
      let j := Z.log2 (two64 - m') in
      if (Z.eqb (two64 - m') (2 ^ j) && Z.leb j 48)%bool
      then let '(x', s) := deand x in (x', (s + (2 ^ j - 1))%Z)
      else (e, 0%Z)
  | EAlu ALU_ADD a b => let '(a', s1) := deand a in let '(b', s2) := deand b in (EAlu ALU_ADD a' b', (s1 + s2)%Z)
  | _ => (e, 0%Z)
  end.

Definition erange (kn : list kentry) (e : expr) : option (Z * Z) :=
  let r := erange0 kn e in
  let '(e', s) := deand e in
  if Z.eqb s 0 then r else
  match erange0 kn (unlin (lin_of e')) with     (* [comment removed for export] *)
  | Some (lo', hi') =>
      if Z.leb s lo' then
        match r with
        | Some (lo, hi) => Some (Z.max lo (lo' - s), Z.min hi hi')
        | None => Some ((lo' - s)%Z, hi')
        end
      else r
  | None => r
  end.


(* [comment removed for export] *)
Definition base_range (kn : list kentry) (e : expr) : option (Z * Z) :=
  match e with ELit z => let v := (z mod two64)%Z in Some (v, v) | _ => erange kn e end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint ctz_fuel (fuel : nat) (z : Z) : Z :=
  match fuel with
  | O => 0
  | S f => if (Z.eqb (z mod 2) 0)%Z then (1 + ctz_fuel f (z / 2))%Z else 0%Z
  end.
Definition ctz64 (z : Z) : Z := ctz_fuel 64 z.

(* [comment removed for export] *)
Fixpoint ealign0 (kn : list kentry) (e : expr) {struct e} : Z :=
  match find_align kn e with
  | Some m => if Z.ltb 0 m then ctz64 m else 0%Z
  | None =>
  match e with
  | ELit z => ctz64 (z mod two64)
  | EAlu ALU_ADD a b => Z.min (ealign0 kn a) (ealign0 kn b)
  | EAlu ALU_SUB a b => Z.min (ealign0 kn a) (ealign0 kn b)
  | EAlu ALU_AND a b => Z.max (ealign0 kn a) (ealign0 kn b)
  | EAlu ALU_OR a b => Z.min (ealign0 kn a) (ealign0 kn b)
  | EAlu ALU_SLL a b =>
      match lit_shamt b with
      | Some s => Z.min (ealign0 kn a + s)%Z 64
      | None => 0%Z
      end
  | EMd M_MUL a b => Z.min (ealign0 kn a + ealign0 kn b)%Z 64
  | _ => 0%Z
  end
  end.


(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint lins_e (k : Z) (a : expr) (ts : list (Z * expr)) : list (Z * expr) :=
  match ts with
  | [] => if Z.eqb k 0 then [] else [(k, a)]
  | (k', a') :: rest =>
      if expr_eqb a a' then (let s := (k + k')%Z in if Z.eqb s 0 then rest else (s, a') :: rest)
      else (k', a') :: lins_e k a rest
  end.

Definition lsub_e (ts2 ts1 : list (Z * expr)) : list (Z * expr) :=
  fold_right (fun t acc => lins_e (- fst t)%Z (snd t) acc) ts2 ts1.

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint find_and_atom_k (sg : Z) (ts : list (Z * expr)) : option (expr * Z) :=
  match ts with
  | [] => None
  | (k, EAlu ALU_AND y (ELit mm)) :: r =>
      if (Z.eqb k sg && Z.ltb 0 mm && Z.eqb (Z.land (mm + 1) mm) 0)%bool then Some (y, mm) else find_and_atom_k sg r
  | _ :: r => find_and_atom_k sg r
  end.

Definition find_and_atom (ts : list (Z * expr)) : option (expr * Z) := find_and_atom_k 1 ts.

Definition pageup_low_k (sg : Z) (e : expr) (m : Z) : option Z :=
  let l := lin_of e in
  match find_and_atom_k sg (snd l) with
  | Some (y, mm) =>
      if (Z.ltb 0 m && Z.eqb ((mm + 1) mod m) 0 && Z.leb (mm + 1) two64)%bool then
        let ly := lin_of y in
        let rest := lins_e (- sg)%Z (EAlu ALU_AND y (ELit mm)) (snd l) in
        match fold_right (fun t acc => lins_e (sg * fst t)%Z (snd t) acc) (snd ly) rest with
        | [] => Some ((fst l + sg * fst ly) mod m)%Z
        | _ => None
        end
      else None
  | None => None
  end.

(* [comment removed for export] *)
Definition pageup_low (e : expr) (m : Z) : option Z :=
  match pageup_low_k 1 e m with
  | Some r => Some r
  | None => pageup_low_k (-1) e m
  end.

Definition pageup_align (e : expr) : Z :=
  let l := lin_of e in
  match (match find_and_atom_k 1 (snd l) with
         | Some p => Some p
         | None => find_and_atom_k (-1) (snd l)
         end) with
  | Some (y, mm) =>
      let m := (mm + 1)%Z in let k := ctz64 m in
      if (Z.eqb m (2 ^ k) && Z.leb k 64)%bool then
        match pageup_low e m with Some 0%Z => k | _ => 0%Z end
      else 0%Z
  | None => 0%Z
  end.

Definition ealign (kn : list kentry) (e : expr) : Z := Z.max (ealign0 (facts_of kn) e) (pageup_align e).

(* [comment removed for export] *)
Definition lin_nowrap (kn : list kentry) (e : expr) : bool :=
  let l := lin_of e in
  match lin_range (erange kn) (fst l) (snd l) with
  | Some (lo, hi) => (Z.leb 0 lo && Z.ltb hi two64)%bool
  | None => false
  end.

(* [comment removed for export] *)
Definition srl_rem (e : expr) (m : Z) : expr := EAlu ALU_AND e (ELit (m - 1)%Z).

(* [comment removed for export] *)
Definition highmask_s (mk : Z) : option Z :=
  let m' := (mk mod two64)%Z in
  let s := Z.log2 (two64 - m') in
  if (Z.eqb (two64 - m') (2 ^ s) && Z.ltb 0 s && Z.ltb s 64)%bool then Some s else None.

Fixpoint srl_expand (kn : list kentry) (ts : list (Z * expr)) : Z * list (Z * expr) :=
  match ts with
  | [] => (0%Z, [])
  | (k, a) :: rest =>
      let '(c, ts') := srl_expand kn rest in
      let keep := (c, lins_e k a ts') in
      match a with
      | EAlu ALU_SRL e (ELit s) =>
          let m := (2 ^ ((s mod two64) mod 64))%Z in
          if (Z.eqb (k mod m)%Z 0%Z && lin_nowrap kn e)%bool then
            let q := (k / m)%Z in
            let le := lin_of e in
            if Z.leb ((s mod two64) mod 64) (ealign kn e) then   (* [comment removed for export] *)
              ((c + q * fst le)%Z, fold_right (fun t acc => lins_e (q * fst t)%Z (snd t) acc) ts' (snd le))
            else
            ((c + q * fst le)%Z,
             lins_e (- q)%Z (srl_rem e m) (fold_right (fun t acc => lins_e (q * fst t)%Z (snd t) acc) ts' (snd le)))
          else keep
      | EAlu ALU_AND e (ELit mk) =>
          (* [comment removed for export] *)
          match highmask_s mk with
          | Some s =>
              if lin_nowrap kn e then
                let le := lin_of e in
                ((c + k * fst le)%Z,
                 lins_e (- k)%Z (srl_rem e (2 ^ s)) (fold_right (fun t acc => lins_e (k * fst t)%Z (snd t) acc) ts' (snd le)))
              else keep
          | None => keep
          end
      | _ => keep
      end
  end.

(* [comment removed for export] *)
Fixpoint has_srl (ts : list (Z * expr)) : bool :=
  match ts with
  | [] => false
  | (_, EAlu ALU_SRL _ (ELit _)) :: _ => true
  | _ :: rest => has_srl rest
  end.
(* [comment removed for export] *)
Definition sfact : Type := (list (Z * expr) * (Z * Z))%type.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sum_fact_x (allkn : list kentry) (ts : list (Z * expr)) (lo hi : Z) : list sfact :=
  let '(c2, ts2) := srl_expand allkn ts in
  match ts2 with
  | _ :: _ => if Z.eqb c2 0 then [] else [(ts2, ((lo - c2)%Z, (hi - c2)%Z))]
  | [] => []
  end.

(* [comment removed for export] *)
Definition fact_nowrap (allkn : list kentry) (e : expr) (hi : Z) : bool :=
  let l := lin_of e in
  match lin_range (erange allkn) (fst l) (snd l) with
  | Some (a, b) => (Z.ltb b two64 && Z.ltb hi (a + two64))%bool
  | None => false
  end.

Fixpoint sum_facts (allkn kn : list kentry) : list sfact :=
  match kn with
  | [] => []
  | KRange e lo hi :: rest =>
      match e with
      | EVar _ => sum_facts allkn rest
      | _ =>
        match lin_of e with
        | (c, (_ :: _ :: _) as ts) =>
            if fact_nowrap allkn e hi then (ts, ((lo - c)%Z, (hi - c)%Z)) :: sum_fact_x allkn ts (lo - c)%Z (hi - c)%Z ++ sum_facts allkn rest
            else sum_facts allkn rest
        | _ => sum_facts allkn rest
        end
      end
  | _ :: rest => sum_facts allkn rest
  end.

(* [comment removed for export] *)
Fixpoint coef_of (a : expr) (ts : list (Z * expr)) : Z :=
  match ts with
  | [] => 0
  | (k, a') :: r => if expr_eqb a a' then k else coef_of a r
  end.

(* [comment removed for export] *)
Fixpoint fact_quot (fts ts : list (Z * expr)) (acc : option Z) : option Z :=
  match fts with
  | [] => acc
  | (k, a) :: r =>
      if Z.eqb k 0 then None else
      let K := coef_of a ts in
      if Z.eqb K 0 then None else
      if negb (Z.eqb (K mod k) 0) then None else
      let q := (K / k)%Z in
      match acc with
      | None => fact_quot r ts (Some q)
      | Some q0 => if Z.eqb q0 q then fact_quot r ts acc else None
      end
  end.

Definition sub_fact (q : Z) (fts ts : list (Z * expr)) : list (Z * expr) :=
  fold_right (fun t acc => lins_e (- (q * fst t))%Z (snd t) acc) ts fts.

(* [comment removed for export] *)
Fixpoint sum_subst (fs : list sfact) (ts : list (Z * expr)) (lo hi : Z) (hit : bool)
  : list (Z * expr) * (Z * Z) * bool :=
  match fs with
  | [] => (ts, (lo, hi), hit)
  | (fts, (flo, fhi)) :: r =>
      match fact_quot fts ts None with
      | Some q =>
          let ts' := sub_fact q fts ts in
          if Z.leb 0 q then sum_subst r ts' (lo + q * flo)%Z (hi + q * fhi)%Z true
          else sum_subst r ts' (lo + q * fhi)%Z (hi + q * flo)%Z true
      | None => sum_subst r ts lo hi hit
      end
  end.

Definition lin_test_rel (kn : list kentry) (c : Z) (ts : list (Z * expr)) (test : Z -> Z -> bool) : bool :=
  match sum_facts kn kn with
  | [] => false
  | fs =>
      match sum_subst fs ts 0 0 false with
      | (ts', (lo0, hi0), true) =>
          match lin_range (erange kn) c ts' with
          | Some (lo, hi) => test (lo + lo0)%Z (hi + hi0)%Z
          | None => false
          end
      | _ => false
      end
  end.

Definition lin_test (kn : list kentry) (c : Z) (ts : list (Z * expr)) (test : Z -> Z -> bool) : bool :=
  match lin_range (erange kn) c ts with
  | Some (lo, hi) => if test lo hi then true else lin_test_rel kn c ts test
  | None => lin_test_rel kn c ts test
  end.

(* [comment removed for export] *)
Fixpoint srl_scale_need (ts : list (Z * expr)) : Z :=
  match ts with
  | [] => 0
  | (k, EAlu ALU_SRL _ (ELit s)) :: rest => Z.max (((s mod two64) mod 64) - ctz64 k)%Z (srl_scale_need rest)
  | _ :: rest => srl_scale_need rest
  end.
Definition zcdiv (a b : Z) : Z := (- ((- a) / b))%Z.
Definition lin_srange (kn : list kentry) (e : expr) : option (Z * Z) :=
  let l := lin_of e in
  let j := srl_scale_need (snd l) in
  if (if Z.leb 0 j then Z.leb j 24 else false) then   (* [comment removed for export] *)
    let sc := (2 ^ j)%Z in
    let ts := List.map (fun t => ((sc * fst t)%Z, snd t)) (snd l) in
    let '(c2, t2) := srl_expand kn ts in
    let '(c3, t3) := (if has_srl t2 then srl_expand kn t2 else (0%Z, t2)) in
    match lin_range (erange kn) (sc * fst l + c2 + c3)%Z t3 with
    | Some (lo', hi') =>
        let lo := zcdiv lo' sc in let hi := (hi' / sc)%Z in
        if (if Z.leb 0 lo then (if Z.leb lo hi then Z.ltb hi two64 else false) else false) then Some (lo, hi) else None
    | None => None
    end
  else None.

(* [comment removed for export] *)
Definition lin_nowrapR (kn : list kentry) (e : expr) : bool :=
  let l := lin_of e in
  let '(c2, t2) := srl_expand kn (snd l) in            (* [comment removed for export] *)
  if lin_test kn (fst l + c2)%Z t2 (fun lo hi => (Z.leb 0 lo && Z.ltb hi two64)%bool) then true
  else (* [comment removed for export] *)
    match lin_srange kn e with Some _ => true | None => false end.

(* [comment removed for export] *)
Fixpoint mentions_var (v : nat) (e : expr) : bool :=
  match e with
  | ELit _ => false
  | EVar w => Nat.eqb v w
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => if mentions_var v a then true else mentions_var v b
  | EExt _ _ _ a => mentions_var v a
  | EBlob _ _ _ _ => false
  end.
Fixpoint shares_var (e1 e2 : expr) : bool :=
  match e2 with
  | ELit _ => false
  | EVar w => mentions_var w e1
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => if shares_var e1 a then true else shares_var e1 b
  | EExt _ _ _ a => shares_var e1 a
  | EBlob _ _ _ _ => false
  end.
Fixpoint novars (e : expr) : bool :=
  match e with
  | ELit _ => true
  | EVar _ => false
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => if novars a then novars b else false
  | EExt _ _ _ a => novars a
  | EBlob _ _ _ _ => true
  end.
(* [comment removed for export] *)
Definition related (b1 b2 : expr) : bool :=
  if shares_var b1 b2 then true else novars b2.

(* [comment removed for export] *)
Definition lin_apart0 (kn : list kentry) (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) : bool :=
  (lin_nowrapR kn b1 && lin_nowrapR kn b2 &&
   let l1 := lin_of b1 in let l2 := lin_of b2 in
   lin_test kn (fst l2 + k2 - fst l1 - k1)%Z (lsub_e (snd l2) (snd l1))
            (fun lo hi => (Z.leb n1 lo || Z.leb hi (- n2))%bool))%bool.
Definition lin_apart (kn : list kentry) (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) : bool :=
  if shares_var b1 b2 then lin_apart0 kn b1 k1 n1 b2 k2 n2 else false.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition zlit64 (z : Z) : Z := if (Z.leb 0 z && Z.ltb z two64)%bool then z else (z mod two64)%Z.

(* [comment removed for export] *)
Definition lin_brange (kn : list kentry) (e : expr) : option (Z * Z) :=
  let l := lin_of e in
  match sum_facts kn kn with
  | [] => None
  | fs =>
      match sum_subst fs (snd l) 0 0 false with
      | (ts', (lo0, hi0), true) =>
          match lin_range (erange kn) (fst l) ts' with
          | Some (lo, hi) =>
              let lo' := (lo + lo0)%Z in let hi' := (hi + hi0)%Z in
              if (Z.leb 0 lo' && Z.ltb hi' two64)%bool then Some (lo', hi') else None
          | None => None
          end
      | _ => None
      end
  end.

Definition xlo (kn : list kentry) (e : expr) : option Z :=
  match e with
  | ELit z => Some (zlit64 z)
  | _ => match erange kn e with
         | Some (lo, _) => Some lo
         | None => match lin_brange kn e with
                   | Some (lo, _) => Some lo
                   | None => match lin_srange kn e with Some (lo, _) => Some lo | None => None end   (* [comment removed for export] *)
                   end
         end
  end.
Definition xhi (kn : list kentry) (e : expr) : option Z :=
  match e with
  | ELit z => Some (zlit64 z)
  | _ => match erange kn e with
         | Some (_, hi) => Some hi
         | None => match lin_brange kn e with
                   | Some (_, hi) => Some hi
                   | None => match lin_srange kn e with Some (_, hi) => Some hi | None => None end   (* [comment removed for export] *)
                   end
         end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition xterms := list (expr * Z).

Fixpoint xt_nowrap (kn : list kentry) (ts : xterms) : bool :=
  match ts with [] => true | (e, _) :: r => lin_nowrapR kn e && xt_nowrap kn r end.
Fixpoint xt_const (ts : xterms) : Z :=
  match ts with [] => 0 | (e, k) :: r => (fst (lin_of e) + k + xt_const r)%Z end.
Fixpoint xt_lin (ts : xterms) : list (Z * expr) :=
  match ts with [] => [] | (e, _) :: r => fold_right (fun t acc => lins_e (fst t) (snd t) acc) (xt_lin r) (snd (lin_of e)) end.

(* [comment removed for export] *)
Definition lin_ge0_scaled (kn : list kentry) (c : Z) (ts : list (Z * expr)) : bool :=
  let j := srl_scale_need ts in
  if (if Z.ltb 0 j then Z.leb j 24 else false) then
    let sc := (2 ^ j)%Z in
    let ts' := List.map (fun t => ((sc * fst t)%Z, snd t)) ts in
    let '(c2, t2) := srl_expand kn ts' in
    let '(c3, t3) := (if has_srl t2 then srl_expand kn t2 else (0%Z, t2)) in
    lin_test kn (sc * c + c2 + c3)%Z t3 (fun lo _ => Z.leb 0 lo)
  else false.

(* [comment removed for export] *)
Definition lin_ge0 (kn : list kentry) (pos neg : xterms) : bool :=
  (xt_nowrap kn pos && xt_nowrap kn neg &&
   (* [comment removed for export] *)
   (if lin_test kn (xt_const pos - xt_const neg)%Z (lsub_e (xt_lin pos) (xt_lin neg)) (fun lo _ => Z.leb 0 lo) then true
    else let '(c2, t2) := srl_expand kn (lsub_e (xt_lin pos) (xt_lin neg)) in
         if lin_test kn (xt_const pos - xt_const neg + c2)%Z t2 (fun lo _ => Z.leb 0 lo) then true
         else (* [comment removed for export] *)
         if (if has_srl t2 then
               let '(c3, t3) := srl_expand kn t2 in
               lin_test kn (xt_const pos - xt_const neg + c2 + c3)%Z t3 (fun lo _ => Z.leb 0 lo)
             else false) then true
         else (* [comment removed for export] *)
           lin_ge0_scaled kn (xt_const pos - xt_const neg)%Z (lsub_e (xt_lin pos) (xt_lin neg))))%bool.

(* [comment removed for export] *)
Definition xinside0 (kn : list kentry) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  if lin_ge0 kn [(b1, k1)] [(b2, k2)] then lin_ge0 kn [(b2, k2); (n2, 0%Z)] [(b1, k1); (n1, 0%Z)] else false.
(* [comment removed for export] *)
Definition xinside_num (kn : list kentry) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match xlo kn b2, xhi kn b2 with
  | Some lo2, Some hi2 =>
      if Z.eqb lo2 hi2 then
        match base_range kn b1, xhi kn n1, xlo kn n2 with
        | Some (lo1, hi1), Some h1, Some l2 => Z.leb (lo2 + k2) (lo1 + k1) && Z.leb (hi1 + k1 + h1) (lo2 + k2 + l2)
        | _, _, _ => false
        end
      else false
  | _, _ => false
  end.
(* [comment removed for export] *)
Definition lenlit (e : expr) : bool := match e with ELit _ => true | _ => false end.
Definition xinside (kn : list kentry) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  if shares_var b1 b2 then xinside0 kn b1 k1 n1 b2 k2 n2
  else if novars b2 then (if xinside_num kn b1 k1 n1 b2 k2 n2 then true
                          else if (lenlit n1 && lenlit n2)%bool then false else xinside0 kn b1 k1 n1 b2 k2 n2)
  else if (novars b1 && negb (lenlit n2))%bool then xinside0 kn b1 k1 n1 b2 k2 n2 else false.
  (* [comment removed for export] *)


(* [comment removed for export] *)
Definition sub_itv (allkn : list kentry) (b : expr) (k n : Z) (c : saddr) (m : expr) : bool :=
  if (if (expr_eqb b (a_base c) && Z.leb (a_off c) k)%bool then
        match xlo allkn m with Some ml => Z.leb (k + n) (a_off c + ml) | None => false end
      else false)
  then true
  else (* [comment removed for export] *)
    if (Z.leb 0 n && Z.ltb n two64)%bool then xinside allkn b k (ELit n) (a_base c) (a_off c) m else false.

(* [comment removed for export] *)
Fixpoint kdisj_apart (allkn kn : list kentry) (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) : bool :=
  match kn with
  | [] => false
  | KDisj c1 m1 c2 m2 :: rest =>
      if (if sub_itv allkn b1 k1 n1 c1 m1 then sub_itv allkn b2 k2 n2 c2 m2 else false) then true
      else if (if sub_itv allkn b1 k1 n1 c2 m2 then sub_itv allkn b2 k2 n2 c1 m1 else false) then true
      else kdisj_apart allkn rest b1 k1 n1 b2 k2 n2
  | _ :: rest => kdisj_apart allkn rest b1 k1 n1 b2 k2 n2
  end.

Definition ranges_apart (kn : list kentry) (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) : bool :=
  if (match base_range kn b1, base_range kn b2 with
      | Some (lo1, hi1), Some (lo2, hi2) =>
          (Z.leb (hi1 + k1 + n1) (lo2 + k2) || Z.leb (hi2 + k2 + n2) (lo1 + k1))%bool
      | _, _ => false
      end) then true
  else if kdisj_apart kn kn b1 k1 n1 b2 k2 n2 then true
  else lin_apart kn b1 k1 n1 b2 k2 n2.

Definition sub_itv_x (kn : list kentry) (b : expr) (k : Z) (n : expr) (c : saddr) (m : expr) : bool :=
  xinside kn b k n (a_base c) (a_off c) m.

Fixpoint kdisj_apart_x (allkn kn : list kentry) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match kn with
  | [] => false
  | KDisj c1 m1 c2 m2 :: rest =>
      if (if sub_itv_x allkn b1 k1 n1 c1 m1 then sub_itv_x allkn b2 k2 n2 c2 m2 else false) then true
      else if (if sub_itv_x allkn b1 k1 n1 c2 m2 then sub_itv_x allkn b2 k2 n2 c1 m1 else false) then true
      else kdisj_apart_x allkn rest b1 k1 n1 b2 k2 n2
  | _ :: rest => kdisj_apart_x allkn rest b1 k1 n1 b2 k2 n2
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition end_hi (kn : list kentry) (b : expr) (k : Z) (n : expr) (lo1 hi1 h1 : Z) : option Z :=
  match n with
  | ELit _ => None
  | _ => if (if Z.leb 0 (lo1 + k) then Z.ltb (hi1 + k + h1) two64 else false)
         then match find_range (facts_of kn) (mkAlu ALU_ADD (mkAlu ALU_ADD b (ELit k)) n) with
              | Some (_, ehi) => Some ehi
              | None => None
              end
         else None
  end.

Definition ranges_apart_x (kn : list kentry) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match n1, n2 with
  | ELit z1, ELit z2 => ranges_apart kn b1 k1 (zlit64 z1) b2 k2 (zlit64 z2)
  | _, _ =>
    if (match base_range kn b1, base_range kn b2, xhi kn n1, xhi kn n2 with
        | Some (lo1, hi1), Some (lo2, hi2), Some h1, Some h2 =>
            if (Z.leb (hi1 + k1 + h1) (lo2 + k2) || Z.leb (hi2 + k2 + h2) (lo1 + k1))%bool then true
            else (* [comment removed for export] *)
            if match end_hi kn b1 k1 n1 lo1 hi1 h1 with Some e1 => Z.leb e1 (lo2 + k2) | None => false end then true
            else match end_hi kn b2 k2 n2 lo2 hi2 h2 with Some e2 => Z.leb e2 (lo1 + k1) | None => false end
        | _, _, _, _ => false
        end) then true
    else if kdisj_apart_x kn kn b1 k1 n1 b2 k2 n2 then true
    else if negb (shares_var b1 b2) then false
    else if lin_ge0 kn [(b2, k2)] [(b1, k1); (n1, 0%Z)] then true
    else lin_ge0 kn [(b1, k1)] [(b2, k2); (n2, 0%Z)]
  end.

(* [comment removed for export] *)
Record sprep := SPrep {
  sp_rng : option (Z * Z);          (* [comment removed for export] *)
  sp_h1 : option Z;                 (* [comment removed for export] *)
  sp_D : list (saddr * expr);       (* [comment removed for export] *)
  sp_Dx : list (saddr * expr) }.    (* [comment removed for export] *)

Fixpoint disj_sides (allkn kn : list kentry) (b1 : expr) (k1 n1 : Z) : list (saddr * expr) :=
  match kn with
  | [] => []
  | KDisj c1 m1 c2 m2 :: rest =>
      let r := disj_sides allkn rest b1 k1 n1 in
      let r1 := if sub_itv allkn b1 k1 n1 c2 m2 then (c1, m1) :: r else r in
      if sub_itv allkn b1 k1 n1 c1 m1 then (c2, m2) :: r1 else r1
  | _ :: rest => disj_sides allkn rest b1 k1 n1
  end.

Fixpoint disj_sides_x (allkn kn : list kentry) (b1 : expr) (k1 : Z) (n1 : expr) : list (saddr * expr) :=
  match kn with
  | [] => []
  | KDisj c1 m1 c2 m2 :: rest =>
      let r := disj_sides_x allkn rest b1 k1 n1 in
      let r1 := if sub_itv_x allkn b1 k1 n1 c2 m2 then (c1, m1) :: r else r in
      if sub_itv_x allkn b1 k1 n1 c1 m1 then (c2, m2) :: r1 else r1
  | _ :: rest => disj_sides_x allkn rest b1 k1 n1
  end.

Fixpoint in_sides (allkn : list kentry) (D : list (saddr * expr)) (b2 : expr) (k2 n2 : Z) : bool :=
  match D with
  | [] => false
  | (c, m) :: r => if sub_itv allkn b2 k2 n2 c m then true else in_sides allkn r b2 k2 n2
  end.

Fixpoint in_sides_x (allkn : list kentry) (D : list (saddr * expr)) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match D with
  | [] => false
  | (c, m) :: r => if sub_itv_x allkn b2 k2 n2 c m then true else in_sides_x allkn r b2 k2 n2
  end.

Definition mk_sprep (kn : list kentry) (b1 : expr) (k1 : Z) (n1 : expr) : sprep :=
  SPrep (base_range kn b1) (xhi kn n1)
        (match n1 with ELit z1 => disj_sides kn kn b1 k1 (zlit64 z1) | _ => [] end)
        (disj_sides_x kn kn b1 k1 n1).

(* [comment removed for export] *)
Definition ranges_apart_p (kn : list kentry) (sp : sprep) (b1 : expr) (k1 : Z) (n1 : expr)
           (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match n1, n2 with
  | ELit z1, ELit z2 =>
      let m1 := zlit64 z1 in let m2 := zlit64 z2 in
      if (match sp_rng sp, base_range kn b2 with
          | Some (lo1, hi1), Some (lo2, hi2) =>
              (Z.leb (hi1 + k1 + m1) (lo2 + k2) || Z.leb (hi2 + k2 + m2) (lo1 + k1))%bool
          | _, _ => false
          end) then true
      else if in_sides kn (sp_D sp) b2 k2 m2 then true
      else lin_apart kn b1 k1 m1 b2 k2 m2
  | _, _ =>
    if (match sp_rng sp, base_range kn b2, sp_h1 sp, xhi kn n2 with
        | Some (lo1, hi1), Some (lo2, hi2), Some h1, Some h2 =>
            if (Z.leb (hi1 + k1 + h1) (lo2 + k2) || Z.leb (hi2 + k2 + h2) (lo1 + k1))%bool then true
            else (* [comment removed for export] *)
            if match end_hi kn b1 k1 n1 lo1 hi1 h1 with Some e1 => Z.leb e1 (lo2 + k2) | None => false end then true
            else match end_hi kn b2 k2 n2 lo2 hi2 h2 with Some e2 => Z.leb e2 (lo1 + k1) | None => false end
        | _, _, _, _ => false
        end) then true
    else if in_sides_x kn (sp_Dx sp) b2 k2 n2 then true
    else if negb (shares_var b1 b2) then false
    else if lin_ge0 kn [(b2, k2)] [(b1, k1); (n1, 0%Z)] then true
    else lin_ge0 kn [(b1, k1)] [(b2, k2); (n2, 0%Z)]
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Inductive ptree (A : Type) : Type := PTLeaf | PTNode (l : ptree A) (o : option A) (r : ptree A).
Arguments PTLeaf {A}. Arguments PTNode {A} _ _ _.
Fixpoint pt_get {A} (t : ptree A) (k : positive) {struct k} : option A :=
  match t with
  | PTLeaf => None
  | PTNode l o r => match k with xH => o | xO k' => pt_get l k' | xI k' => pt_get r k' end
  end.
Fixpoint pt_set {A} (k : positive) (v : A) (t : ptree A) {struct k} : ptree A :=
  match t with
  | PTLeaf => match k with
              | xH => PTNode PTLeaf (Some v) PTLeaf
              | xO k' => PTNode (pt_set k' v PTLeaf) None PTLeaf
              | xI k' => PTNode PTLeaf None (pt_set k' v PTLeaf)
              end
  | PTNode l o r => match k with
                    | xH => PTNode l (Some v) r
                    | xO k' => PTNode (pt_set k' v l) o r
                    | xI k' => PTNode l o (pt_set k' v r)
                    end
  end.
Lemma pt_gss : forall A (k : positive) (v : A) t, pt_get (pt_set k v t) k = Some v.
Proof.
ltac2:(KReplay.run1 (kr_t_AxSymExec3 ()) [] "p'0h01kh11th21vh31oi001oh42t1h52t2h63IHkh71Ai011li021pi031rp;1p;2p;4p;5p;3p100i`p4p70p100j\p4p710p8p200R0p100Q0p4p710p8P0g00k9R1p4p710p8P0g00l6R2p4p710p8g00m3R3j13Tg00n1j11Tg00nSj22Tg00Afj15Tg00o5j18Tg0103j47Tg001Hj14Tg007Fj26Tg0111j5<TP2j4;TP1j3:Tg008Lj39Tf7R1f6R2f5R4f4R5f3R6f2R7C;f1R83:f0R939p=0g011XR:%36%15R;P5P5P7P8P9P71258G0]1^27R<X0:%35R=P3P4%12R>P2P2%55R?P7P9P?1227R?G0P9P7P8%84R@O2RA%14RBP4P4%56RCP8P@PC1248RCG0ef8RD#3REf9RF#1RGf:#3RHPDP1P9O2f;RI#1RJPIPI%5FRKP1PIP7P8P9C7RLPK12I1RKG0eW5W3W4P7P8P9O3n10110200020030101100103W1X26X6<X0:P3P4P>P2P2%45R>P7P9P>P?G0P9PAPBP4P4%46R4P8P@P4PCG0ePDP1P7O2PJPIPI%4FRIP1PLPIPKG0eX5HX3GX4EP7P8P9O3n10110200020030101100103X1=X26X6<X0:%37P3P6P;P5P5g00;TR;P7P9P;1257G0P9%16R51268R3'6P5P6P6P;P8%86P;P3G0e%32%1112F1R2,6GPGPFPFP;P1PFP7P8P9C7P;P2G0eX5EW3W4P7P8P9O3n10110200020030101100103W1X28P9D<W0X70o"). Qed.
Lemma pt_gso : forall A (k k' : positive) (v : A) t, k <> k' -> pt_get (pt_set k' v t) k = pt_get t k.
Proof.
ltac2:(KReplay.run1 (kr_t_AxSymExec3 ()) [] "p'0h03IHkh11Hh21th31vh42k'h51kh61oi001oh72t1h82t2h93Heqh:2H0h;1fh<1Ai011li021pi031rp%0p;1p;4p;3p;2p;6p;5p200R0g00Q0R1p4p710p8P0g00k9R2p4p710p8P0g00l6R3p4p710p8g00m3R4j1;Tg00n1j15TP3j42Tg00AfR3j16TP2j31Tg00o5j1CTg00OHj1?Tg008Lj38Tg007Fj24Tg001HR2j17Tg00JIj1<Tg012=j6GTg00dBj2ITP1j6FTg0103j4HTg00nSj2JTg0111j5PTg012[j6ETg011XR1f1R5f0R638#<p=0f6R7f5R8f4R9f3R:31f2R;?15638p=:A1:;5=896p=3g00;TR<=816p=@A156<p==A1;5<=8:6p=DA8156p=BP;P1P5P3P3P6EEp=OP1P1P3P;P5P6EEp=NA1;56989:p=MP9P:P;P5C2=18<=876p=>A816<#<p=9P;P<P5P6C2p=AP;P1P5P2P2P6EEp=LP1P1P2P;P5P6EEp=K%;9S0010:;R=%57R>P7P7P:P;P5C2S01P9P7P5P9F:[]2^3:^41R?X51P1%;7S02%68R@/0;f8RA#5RBPAPAP:P;P5C2S03%67RCA1A5CS04D3[]2^38P6f7RD#;REP4PA%6DRF%6:RG'0f:RH#5RIPHPH%69RJP:P5C2S05%6ARKA1H5KRLD3[P6%6;RM,0CRNf9RO#5RP%CORQ=1ODS06%?HS0798I6X6PS08P1f;RRf<RS#;f>RT#5PTPTP:P;P5C2P9PTP5P9F:\=]2]3^41RU%65RV/0@%5SRWPS%CSP;%?SD3RX]1]0PDf=RY#;RZ10G;R[f?R\#5R]P\P\P:P;P5C2R^PJP\P5PJF:[]2^3S^41R_%6VR`/0C%5YRa%?Y'4RbW1W0X51P6O1%7:Rc/0;RdP]P\P^%79R^P\P5P^F:[^2Z^3S^41Re%75Rf#6Rg/0CPbW1W0X51P6O1%;RRh%@;#<RiPaPYPYP:P;P5C2Rj1=Y5CD[]2^3H^41Rk%6<Rl/0J%5RS09%?R'4RmW1W0n011020003101021010200P7P6O2POP:P;PQC2=1ODS0:P7P:P;PQ1BD:RnP1PKPKPJP1\1RoP6POO1X;oS0;14o3R33OANA96EG1BKJg00[AP;P6O1'IRpb9W:%<nS0<eO4EFUPPPOPOPGP;PQC2S0=PFA1OQFS0>D3\Ne%6SRN/0KRqP]A1\5YRrf@Rs#5S0?P6PsP;PTDMX6]P1fARtfBRu#;fDRv#5PvPvP:P;P5C2P9PvP5P9F:\=]2]3^41S0@%6RRv,0V%5uS0AA1u9;Rw;8w]1]0PYfCRw#;RxfERy#5RzPyPyP:P;P5C2R{PJPyP5PJF:\[]2^3u^41S0B10`N%5wR|A1w8M'4W1W0X51P6O1PzPyP{P^PyP5P^F:\d^2x^3u^41S0C10gN%7;Rx91w8,4|W1W0X51P6O1%;tP|PwPwP:P;P51=w5F>\i]2^3s^41S0D%6HRy,0l%5tS0E1=t:'4W1W0n011020003101021010200PSP6O2P\POPAP5C2=1\YPSPOPAP51BYOR{P1%6TRzPzPyP6P\O1X;oR}=Oo3ANTH6EG1BzyPpb9W:%<{S0FeO4EFUP]P\P\%6OS0GPAP\P:P;P5CHRzC2S0H%6YR3A1\z3S0ID3\qeX8ZX6WX7hP;P5P6O3n10110200020131101100103W2X37X41P6O1P4PA10FcPIPHPHP^P:P5C2S0JPKPLD3[P610CxRLP1%78Rq,0VPX]1^0UPD%77R~,0`PbW1X0_X51P6O110g~PbW1X0eX51P6O110l^PmW1X0kn011020003101021010200P7P6O2UPPPOPOPcP;PQC2S0KPFQ0>D3\Le%7ARL,0NRN14]rUP]P\P\%7OS0>PAPzC2S0LP3Q0ID3\NeX8ZX6WX7hP;P5P6O3n10110200020130101100103X2EX37X41P6O1%;8RNP4P7%9@PBPAAAA:5S0IPCQ04D3[P6%9JR3P1%;HPWPSPSP:P;P5C2P9PSP5P9F:\=]2^3O^41R=%9VPIPH%CHP;Q07D3S07]1]0P8PaPYPjPJPYP5PJF:\[^2h^3H^41R[%9`PmW1W0X51P6O1PaPYPjP^PYP5P^F:\d^2h^3H^41Rd%9gPmW1W0X51P6O1%;ORgQ09PRPRP:P;P51=R5F>\i]2^3A^41Rj%9l%?O,4PS04W1W0n011020003101021010200P9P6O2U%5DRlPD%CDR`9AD;S0MP@PDP`P@F:\3e%9yRyA1Y5R,4aUPaPYPYP:P;P5CHR39AYAS0NPvPYP3PvF:\yeX8hX6IX7gP;P5P6O3n10110200020130101100103W2X39n011020003111021110201X41X0?X51P1Q0210q;PBPAQ03P~A1A5~S03D3[]2^38P6P4PA%7DRy/0GPIPHQ05PLA1H5LS05D3[P610~MRvP110f@PX]1^0UPD%7VRV/0CPbW1X0_X51P6O1%7fR@/0CPbW1X0eX51P6O1%7<RC/0JPmW1X0kn011020003101021010200P7P6O2UPPPOQ0=PyA1OQyS0=D3\ve%7SRv/0KRrA1\:YS02,4]UP]P\Q0H%7YRFA1\zFRzD3\reX8ZX6WX7hP;P5P6O3n10110200020130101100103X2EX37X41P6O1P4PA10ycPIPHQ0JPLQ05D3[P610~xRrPPQ06Q08P110fqPX]1^0UPD10V~PbW1X0_X51P6O110@~PbW1X0eX51P6O110C^PmW1X0kn011020003101021010200P7P6O2Q0:P7P:P;PQP1PLPLP^Q0;14o2R25LoAKA96EG1BL^Ppb9X:nQ0<eO4EFUPPPOQ0KPyQ0=D3\re10vLRrP]Q02Q0?P6PsP9PTDMX6]P1Q0@%7RRs,0fQ0AA1u7;Ru;8u]1]0PYQ0B10VvA1wDM,4|W1W0X51P6O1Q0C10@vA1wDx,4|W1W0X51P6O1Q0D%7HR|,0CQ0E1=t8'4W1W0n011020003101021010200PSP6O2P\POPAP:C2=1\YPSPOPAP:P1%7TRtPtP|ALo}2AKTH6EG1Bt|Ppb9X:{Q0FeO4EFUP]P\Q0LPFPzD3\reX8ZX6WX7hP;P5P6O3n10110200020131101100103X2EX37X41P6O1P4P7%9qPBPAQ0IP~Q03D3[P6%9^R~P1%9fQ07]1^0=P8%9VPmW1X0[X51P6O1%9@PmW1X0dX51P6O1%9CQ04W1X0jn011020003101021010200P9P6O2UPlPDQ0MPqPDP`PqF:\~e%9|R|A1Y:R,4aUPaPYQ0NPsPYP3PsF:\|eX8hX6IX7gP;P5P6O3n10110200020130101100103X2NX39n011020003111021110201X41X0?X51P1Q00P>P7Q011=75R?CD\i]2^3:P6P4P7%@G#<PBPAPAPJP:P51=A5RJF>[P6%@M#<RM%?D,4lRiUPlPDPDPGP;P`1=D`RGF>\Me%@K#<RK14a;RMUPaPYPYQ0GPAP31=Y3R|F>\KeX8hX6IX7gP;P5P6O3n10110200020030101100103X2NX39X41P6O1P4P7%@c#<PBPAPAP^P:P5PJF>[P6%@x#<RxPiUPlPDPDPcP;P`PGF>\xe%@L#<RLPMUPaPYPYQ0>PAP3P|F>\LeX8hX6IX7gP;P5P6O3n10110200020030101100103X2NX39X41P6O1%;:P4P9A81<<R9#<R4P>P7AA7:5P?CD[P6141<R<P91J7:%?758>P5P6O1R>'Ib9V4%58P8%C8R79A8;1=87CD\4eP<P91JSO=8W:/I>b9V4Q09PRPRP:P;P5CHR:9ARA1=R:CD\4eX8gX6BX7EP;P5P6O3n10110200020030101100103W2X3;n011020003101021010200X41P6DPX51X<0o"). Qed.
Lemma pt_get_leaf : forall A (k : positive), pt_get (@PTLeaf A) k = None.
Proof.
ltac2:(KReplay.run1 (kr_t_AxSymExec3 ()) [] "p'0h01kh11Ai001pp;1p;3p;2p200R0p100Q0p4p710p8P0g00k9R1p4p710p8g00n1j10Tg00o5j15TP1j33Tg00OHj11Tg008Lj34Tg007Fj22Tg011XR1P1f2R2#0%52f0R3532%1234P3f3R2#0%12'2X01P3O1R3P3f1R3#0%13'2n011000003101001010000W0X10o"). Qed.



(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive lres :=
| LHit (v : expr) (scs : list sidecond) (hints : list bool)
| LMiss (scs : list sidecond) (hints : list bool)     (* [comment removed for export] *)
| LStuck.

Fixpoint zbytes_le_to_Z (bs : list Z) : Z :=
  match bs with
  | [] => 0
  | b :: rest => Z.lor b (Z.shiftl (zbytes_le_to_Z rest) 8)
  end.

Definition lit_of_bytes (sx : bool) (n : nat) (bs : list Z) : expr :=
  ELit (let u := zbytes_le_to_Z bs in if sx then bv_swrap (8 * N.of_nat n) u else u).

(* [comment removed for export] *)
Fixpoint log_byte_lit (log : list sentry) (rb : expr) (rk : Z) : option Z :=
  match log with
  | [] => None
  | SE (SA kb kk) w v :: rest =>
      match rel_lit rb rk 1 kb kk (Z.of_nat w) with
      | RInside d => match v with
                     | ELit z => Some (((z mod two64) / 2 ^ (8 * d)) mod 256)%Z
                     | _ => None
                     end
      | RDisjoint => log_byte_lit rest rb rk
      | _ => None
      end
  end.

(* [comment removed for export] *)
Fixpoint log_bytes_lit (log : list sentry) (rb : expr) (rk : Z) (n : nat) : option (list Z) :=
  match n with
  | O => Some []
  | S n' => match log_byte_lit log rb rk, log_bytes_lit log rb (rk + 1) n' with
            | Some b, Some r => Some (b :: r)
            | _, _ => None
            end
  end.

(* [comment removed for export] *)
Fixpoint log_lookup (kn : list kentry) (log : list sentry) (rb : expr) (rk : Z) (n : nat) (sx : bool)
         (hints : list bool) (acc : list sidecond) : lres :=
  match log with
  | [] => LMiss acc hints
  | SE (SA kb kk) w v :: rest =>
      match rel_lit rb rk (Z.of_nat n) kb kk (Z.of_nat w) with
      | RInside d => LHit (mkExt sx (Z.to_nat d) n v) acc hints
      | RDisjoint => log_lookup kn rest rb rk n sx hints acc
      | RPartial => match log_bytes_lit log rb rk n with
                    | Some bs => LHit (lit_of_bytes sx n bs) acc hints
                    | None => LStuck
                    end
      | RUnknown =>
          if ranges_apart kn rb rk (Z.of_nat n) kb kk (Z.of_nat w)
          then log_lookup kn rest rb rk n sx hints acc
          else
          match hints with
          | false :: _ => LStuck
          | _ => log_lookup kn rest rb rk n sx (tl hints)
                   (SCDisj (SA rb rk) (elen n) (SA kb kk) (elen w) :: acc)
          end
      end
  end.

(* [comment removed for export] *)
Fixpoint img_bytes (segs : list Segment) (a : Z) (n : nat) : option (list Z) :=
  match n with
  | O => Some []
  | S n' =>
      match seg_rom segs (Z_to_bv 64 a) with
      | Some b => match img_bytes segs (a + 1) n' with
                  | Some r => Some (bv_unsigned b :: r)
                  | None => None
                  end
      | None => None
      end
  end.

(* [comment removed for export] *)
Definition fill_lit (sx : bool) (n : nat) (c : Z) : expr :=
  lit_of_bytes sx n (repeat (c mod 256)%Z n).

(* [comment removed for export] *)
Fixpoint know_byte_lit (segs : list Segment) (kn : list kentry) (rb : expr) (rk : Z) : option Z :=
  match kn with
  | [] => None
  | K :: rest =>
      match K with
      | KWord (SA kb kk) w (ELit z) =>
          match rel_lit rb rk 1 kb kk (Z.of_nat w) with
          | RInside d => Some (((z mod two64) / 2 ^ (8 * d)) mod 256)%Z
          | _ => know_byte_lit segs rest rb rk
          end
      | KZero (SA kb kk) (ELit l0) =>
          match rel_lit rb rk 1 kb kk (l0 mod 2 ^ 64)%Z with
          | RInside _ => Some 0%Z
          | _ => know_byte_lit segs rest rb rk
          end
      | KFill (SA kb kk) (ELit l0) c =>
          match rel_lit rb rk 1 kb kk (l0 mod 2 ^ 64)%Z with
          | RInside _ => Some (c mod 256)%Z
          | _ => know_byte_lit segs rest rb rk
          end
      | KImg lo hi =>
          match rb with
          | ELit 0 =>
              if (Z.leb lo rk && Z.ltb rk hi)%bool then
                match seg_rom segs (Z_to_bv 64 rk) with
                | Some b => Some (bv_unsigned b)
                | None => None            (* [comment removed for export] *)
                end
              else know_byte_lit segs rest rb rk
          | _ => know_byte_lit segs rest rb rk
          end
      | _ => know_byte_lit segs rest rb rk
      end
  end.

(* [comment removed for export] *)
Fixpoint know_bytes_lit (segs : list Segment) (kn : list kentry) (rb : expr) (rk : Z) (n : nat)
  : option (list Z) :=
  match n with
  | O => Some []
  | S n' => match know_byte_lit segs kn rb rk, know_bytes_lit segs kn rb (rk + 1) n' with
            | Some b, Some r => Some (b :: r)
            | _, _ => None
            end
  end.

(* [comment removed for export] *)
Fixpoint know_lookupA0 (allkn : list kentry) (segs : list Segment) (kn : list kentry) (rb : expr) (rk : Z)
         (n : nat) (sx : bool) (hints : list bool) (acc : list sidecond) : lres :=
  let know_lookup := know_lookupA0 allkn in
  match kn with
  | [] => LMiss acc hints
  | K :: rest =>
      match K with
      | KWord (SA kb kk) w v =>
          match rel_lit rb rk (Z.of_nat n) kb kk (Z.of_nat w) with
          | RInside d => LHit (mkExt sx (Z.to_nat d) n v) acc hints
          | _ => know_lookup segs rest rb rk n sx hints acc
          end
      | KZero (SA kb kk) len =>
          match len with
          | ELit l0 =>
              match rel_lit rb rk (Z.of_nat n) kb kk (l0 mod 2^64)%Z with
              | RInside _ => LHit (ELit 0) acc hints
              | RDisjoint | RPartial => know_lookup segs rest rb rk n sx hints acc
              | RUnknown =>
                  (* [comment removed for export] *)
                  if xinside allkn rb rk (elen n) kb kk len then LHit (ELit 0) acc hints else
                  match hints with
                  | true :: hs => LHit (ELit 0) (SCInside (SA rb rk) (elen n) (SA kb kk) len :: acc) hs
                  | false :: hs => know_lookup segs rest rb rk n sx hs acc
                  | [] => know_lookup segs rest rb rk n sx [] acc
                  end
              end
          | _ =>
              if xinside allkn rb rk (elen n) kb kk len then LHit (ELit 0) acc hints else
              match hints with
              | true :: hs => LHit (ELit 0) (SCInside (SA rb rk) (elen n) (SA kb kk) len :: acc) hs
              | false :: hs => know_lookup segs rest rb rk n sx hs acc
              | [] => know_lookup segs rest rb rk n sx [] acc
              end
          end
      | KFill (SA kb kk) len c =>
          (* [comment removed for export] *)
          let hit := fill_lit sx n c in
          match len with
          | ELit l0 =>
              match rel_lit rb rk (Z.of_nat n) kb kk (l0 mod 2^64)%Z with
              | RInside _ => LHit hit acc hints
              | RDisjoint | RPartial => know_lookup segs rest rb rk n sx hints acc
              | RUnknown =>
                  if xinside allkn rb rk (elen n) kb kk len then LHit hit acc hints else
                  match hints with
                  | true :: hs => LHit hit (SCInside (SA rb rk) (elen n) (SA kb kk) len :: acc) hs
                  | false :: hs => know_lookup segs rest rb rk n sx hs acc
                  | [] => know_lookup segs rest rb rk n sx [] acc
                  end
              end
          | _ =>
              if xinside allkn rb rk (elen n) kb kk len then LHit hit acc hints else
              match hints with
              | true :: hs => LHit hit (SCInside (SA rb rk) (elen n) (SA kb kk) len :: acc) hs
              | false :: hs => know_lookup segs rest rb rk n sx hs acc
              | [] => know_lookup segs rest rb rk n sx [] acc
              end
          end
      | KUnk _ _ => know_lookup segs rest rb rk n sx hints acc   (* [comment removed for export] *)
      | KBlob (SA kb kk) len k =>
          if expr_eqb rb kb then
            (* [comment removed for export] *)
            if Z.leb kk rk then
              match len with
              | ELit l0 =>
                  if Z.leb (rk + Z.of_nat n) (kk + (l0 mod 2^64)%Z)
                  then LHit (EBlob sx k (rk - kk) n) acc hints
                  else if Z.leb (kk + (l0 mod 2^64)%Z) rk then know_lookup segs rest rb rk n sx hints acc
                  else LStuck
              | _ =>
                  (* [comment removed for export] *)
                  if match erange allkn len with   (* [comment removed for export] *)
                     | Some (lo, _) => Z.leb (rk + Z.of_nat n) (kk + lo)
                     | None => false
                     end
                  then LHit (EBlob sx k (rk - kk) n) acc hints
                  else
                  match hints with
                  | true :: hs => LHit (EBlob sx k (rk - kk) n)
                                    (SCInside (SA rb rk) (elen n) (SA kb kk) len :: acc) hs
                  | false :: hs => know_lookup segs rest rb rk n sx hs acc
                  | [] => know_lookup segs rest rb rk n sx [] acc
                  end
              end
            else know_lookup segs rest rb rk n sx hints acc
          else know_lookup segs rest rb rk n sx hints acc
      | KImg lo hi =>
          match rb with
          | ELit 0 =>
              if (Z.leb lo rk && Z.leb (rk + Z.of_nat n) hi)%bool then
                match img_bytes segs rk n with
                | Some bs => LHit (lit_of_bytes sx n bs) acc hints
                | None => LStuck
                end
              else know_lookup segs rest rb rk n sx hints acc
          | _ => know_lookup segs rest rb rk n sx hints acc
          end
      | KAlign _ _ => know_lookup segs rest rb rk n sx hints acc
      | KRange _ _ _ => know_lookup segs rest rb rk n sx hints acc
      | KWr _ _ => know_lookup segs rest rb rk n sx hints acc
      | KDisj _ _ _ _ => know_lookup segs rest rb rk n sx hints acc
      end
  end.

(* [comment removed for export] *)
Definition know_lookupA (allkn : list kentry) (segs : list Segment) (kn : list kentry) (rb : expr) (rk : Z)
         (n : nat) (sx : bool) (hints : list bool) (acc : list sidecond) : lres :=
  match know_lookupA0 allkn segs kn rb rk n sx hints acc with
  | LMiss acc' hints' =>
      match know_bytes_lit segs kn rb rk n with
      | Some bs => LHit (lit_of_bytes sx n bs) acc' hints'
      | None => LMiss acc' hints'
      end
  | r => r
  end.

Definition know_lookup (segs : list Segment) (kn : list kentry) (rb : expr) (rk : Z)
         (n : nat) (sx : bool) (hints : list bool) (acc : list sidecond) : lres :=
  know_lookupA kn segs kn rb rk n sx hints acc.

(* [comment removed for export] *)
Fixpoint coeffs_divk (kn : list kentry) (m : Z) (ts : list (Z * expr)) : bool :=
  match ts with
  | [] => true
  | (k, a) :: rest => ((Z.eqb (k mod m) 0 || Z.eqb ((k * 2 ^ ealign kn a) mod m) 0) && coeffs_divk kn m rest)%bool
  end.

Definition lin_lowbits_kn (kn : list kentry) (e : expr) (k : Z) : option Z :=
  let l := lin_of e in
  if coeffs_divk kn (2 ^ k) (snd l) then Some ((fst l) mod 2 ^ k)%Z
  else pageup_low e (2 ^ k).   (* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint ldiv_terms (m : Z) (ts : list (Z * expr)) : list (Z * expr) :=
  match ts with
  | [] => []
  | (k, a) :: rest => ((k / m)%Z, a) :: ldiv_terms m rest
  end.

(* [comment removed for export] *)
Fixpoint lsplit_divc (m : Z) (ts : list (Z * expr)) : list (Z * expr) * list (Z * expr) :=
  match ts with
  | [] => ([], [])
  | (k, a) :: rest =>
      let (d, r) := lsplit_divc m rest in
      if Z.eqb (k mod m) 0 then ((k, a) :: d, r) else (d, (k, a) :: r)
  end.

(* [comment removed for export] *)
Definition lin_nowrap_l (kn : list kentry) (c : Z) (ts : list (Z * expr)) : bool :=
  match lin_range (erange kn) c ts with
  | Some (lo, hi) => (Z.leb 0 lo && Z.ltb hi two64)%bool
  | None => false
  end.

Definition mkSrl (kn : list kentry) (a : expr) (s : Z) : expr :=
  let l := lin_of a in
  let m := (2 ^ s)%Z in
  if (negb (lin_trivial l) && coeffs_div m (snd l) && lin_nowrap kn a)%bool
  then unlin ((fst l / m)%Z, ldiv_terms m (snd l))     (* [comment removed for export] *)
  else
    (* [comment removed for export] *)
    match (if (negb (lin_trivial l) && lin_nowrap kn a)%bool then lsplit_divc m (snd l) else ([], [])) with
    | ((_ :: _) as dts, (_ :: _) as rts) =>
        match (if lin_nowrap_l kn (fst l) rts then erange kn (unlin (fst l, rts)) else None) with
        | Some (lo, hi) =>
            if Z.eqb (lo / m) (hi / m) then unlin ((lo / m)%Z, ldiv_terms m dts)
            else mkAlu ALU_SRL a (ELit s)
        | None => mkAlu ALU_SRL a (ELit s)
        end
    | _ => mkAlu ALU_SRL a (ELit s)
    end.

(* [comment removed for export] *)
Fixpoint lowbits (kn : list kentry) (e : expr) (j : Z) {struct e} : option Z :=
  let m := (2 ^ j)%Z in
  let dflt := if Z.leb j (ealign kn e) then Some 0%Z else lin_lowbits_kn kn e j in
  match e with
  | ELit z => Some ((z mod two64) mod m)%Z
  | EAlu ALU_AND a (ELit c) =>
      if Z.eqb ((c mod two64) mod m) 0 then Some 0%Z else
      match lowbits kn a j with Some v => Some (Z.land v ((c mod two64) mod m)) | None => dflt end
  | EAlu ALU_OR a (ELit c) =>
      match lowbits kn a j with Some v => Some (Z.lor v ((c mod two64) mod m)) | None => dflt end
  | EAlu ALU_XOR a (ELit c) =>
      match lowbits kn a j with Some v => Some (Z.lxor v ((c mod two64) mod m)) | None => dflt end
  | EAlu ALU_ADD a b =>
      match lowbits kn a j, lowbits kn b j with Some x, Some y => Some ((x + y) mod m)%Z | _, _ => dflt end
  | EAlu ALU_SUB a b =>
      match lowbits kn a j, lowbits kn b j with Some x, Some y => Some ((x - y) mod m)%Z | _, _ => dflt end
  | EMd M_MUL (ELit c) a =>
      if Z.eqb ((c mod two64) mod m) 0 then Some 0%Z else
      match lowbits kn a j with Some v => Some ((c * v) mod m)%Z | None => dflt end
  | _ => dflt
  end.

(* [comment removed for export] *)
Fixpoint lsplit_div (kn : list kentry) (m : Z) (ts : list (Z * expr)) : list (Z * expr) * list (Z * expr) :=
  match ts with
  | [] => ([], [])
  | (k, a) :: rest =>
      let (d, r) := lsplit_div kn m rest in
      if (Z.eqb (k mod m) 0 || Z.eqb ((k * 2 ^ ealign kn a) mod m) 0)%bool then ((k, a) :: d, r) else (d, (k, a) :: r)
  end.

(* [comment removed for export] *)
Definition and_high_split (kn : list kentry) (bk : expr) (j c : Z) (dts rts : list (Z * expr)) : expr :=
  let m := (2 ^ j)%Z in
  let cA := (c - c mod m)%Z in
  let r := unlin ((c mod m)%Z, rts) in
  match erange kn r with
  | Some (lo, hi) =>
      if Z.eqb (lo / m) (hi / m) then unlin ((cA + (lo / m) * m)%Z, dts)
      else mkAlu ALU_ADD (unlin (cA, dts)) (mkAlu ALU_AND r bk)
  | None => mkAlu ALU_ADD (unlin (cA, dts)) (mkAlu ALU_AND r bk)
  end.

Definition and_low_split (kn : list kentry) (bk : expr) (j c : Z) (rts : list (Z * expr)) : expr :=
  let m := (2 ^ j)%Z in
  let r := unlin ((c mod m)%Z, rts) in
  match erange kn r with
  | Some (lo, hi) =>
      if Z.eqb (lo / m) (hi / m) then unlin ((c mod m - (lo / m) * m)%Z, rts)
      else mkAlu ALU_AND r bk
  | None => mkAlu ALU_AND r bk
  end.

(* [comment removed for export] *)
Definition mkAnd0 (kn : list kentry) (a b : expr) : expr :=
  match b with
  | ELit k =>
      let k' := (k mod two64)%Z in
      let j := Z.log2 (two64 - k') in
      if (Z.eqb (two64 - k') (2 ^ j) && Z.ltb j 64)%bool then
        (* [comment removed for export] *)
        (if Z.leb j (ealign kn a) then a
         else let l := lin_of a in
              if (negb (lin_trivial l) && coeffs_divk kn (2 ^ j) (snd l))%bool
              then unlin ((fst l - (fst l) mod 2 ^ j)%Z, snd l)
              else (* [comment removed for export] *)
                match (if lin_trivial l then ([], snd l) else lsplit_div kn (2 ^ j) (snd l)) with
                | ((_ :: _) as dts, (_ :: _) as rts) => and_high_split kn b j (fst l) dts rts
                | _ => (* [comment removed for export] *)
                       mkMd M_MUL (ELit (2 ^ j)%Z) (mkSrl kn a j)
                end)
      else
        let j2 := Z.log2 (k' + 1) in
        if (Z.eqb (k' + 1) (2 ^ j2) && Z.ltb j2 64)%bool then
          (* [comment removed for export] *)
          (if Z.leb j2 (ealign kn a) then ELit 0
           else match lowbits kn a j2 with        (* [comment removed for export] *)
           | Some v => ELit v
           | None =>
           if lin_trivial (lin_of a) then mkAlu ALU_AND a b
           else match lin_lowbits_kn kn a j2 with
                | Some v => ELit v
                | None => (* [comment removed for export] *)
                    match lsplit_div kn (2 ^ j2) (snd (lin_of a)) with
                    | (_ :: _, (_ :: _) as rts) => and_low_split kn b j2 (fst (lin_of a)) rts
                    | _ => mkAlu ALU_AND a b
                    end
                end
           end)
        else (* [comment removed for export] *)
          let j3 := (Z.log2 k' + 1)%Z in
          if (Z.ltb 0 k' && Z.leb j3 64 && negb (lin_trivial (lin_of a)))%bool then
            match lin_lowbits_kn kn a j3 with
            | Some v => ELit (Z.land v k')
            | None => mkAlu ALU_AND a b
            end
          else mkAlu ALU_AND a b
  | _ => mkAlu ALU_AND a b
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition narrow_mask (kn : list kentry) (a : expr) (k' : Z) : option Z :=
  let i := ctz64 k' in
  let m := (k' + 2 ^ i)%Z in
  let j := Z.log2 m in
  if (Z.ltb 0 k' && Z.eqb m (2 ^ j) && Z.ltb j 64)%bool then
    match xhi kn a with
    | Some h => if Z.ltb h (2 ^ j) then Some (two64 - 2 ^ i)%Z else None
    | None => None
    end
  else None.

Definition mkAnd (kn : list kentry) (a b : expr) : expr :=
  match b with
  | ELit k =>
      match narrow_mask kn a (k mod two64)%Z with
      | Some m => mkAnd0 kn a (ELit m)
      | None => mkAnd0 kn a b
      end
  | _ => mkAnd0 kn a b
  end.

Definition mkAndK (kn : list kentry) (a b : expr) : expr :=
  match a, b with
  | EAlu ALU_AND x (ELit m1), ELit k => mkAnd kn x (ELit (Z.land (m1 mod two64) (k mod two64))%Z)
  | EMd M_MUL (ELit m) (EAlu ALU_SRL x (ELit i)), ELit k =>
      (* [comment removed for export] *)
      let i' := ((i mod two64) mod 64)%Z in
      if Z.eqb (m mod two64) (2 ^ i') then mkAnd kn x (ELit (Z.land (two64 - 2 ^ i') (k mod two64))%Z)
      else mkAnd kn a b
  | _, _ => mkAnd kn a b
  end.

(* [comment removed for export] *)
Definition or_disjoint (kn : list kentry) (a b : expr) : bool :=
  match erange kn b with
  | Some (lo, hi) => (Z.leb 0 lo && Z.ltb hi (2 ^ (ealign kn a)))%bool
  | None => false
  end.

Definition mkOr (kn : list kentry) (a b : expr) : expr :=
  match is_lit a, is_lit b with
  | Some x, Some y => ELit (zalu ALU_OR x y)
  | _, _ =>
      if or_disjoint kn a b then mkAlu ALU_ADD a b
      else if or_disjoint kn b a then mkAlu ALU_ADD a b
      else (* [comment removed for export] *)
           match b with
           | ELit c => mkAlu ALU_ADD (mkAndK kn a (ELit (Z.lnot (c mod two64)))) (ELit c)
           | _ => match a with
                  | ELit c => mkAlu ALU_ADD (mkAndK kn b (ELit (Z.lnot (c mod two64)))) (ELit c)
                  | _ => EAlu ALU_OR a b
                  end
           end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Fixpoint closedb (e : expr) : bool :=
  match e with
  | ELit _ => true
  | EVar _ => false
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => closedb a && closedb b
  | EExt _ _ _ a => closedb a
  | EBlob _ _ _ _ => false
  end.

Fixpoint esubst (s r e : expr) : expr :=
  if expr_eqb e s then r else
  match e with
  | EAlu op a b => EAlu op (esubst s r a) (esubst s r b)
  | EAluw op a b => EAluw op (esubst s r a) (esubst s r b)
  | EMd op a b => EMd op (esubst s r a) (esubst s r b)
  | EMdw op a b => EMdw op (esubst s r a) (esubst s r b)
  | EExt sx lo n a => EExt sx lo n (esubst s r a)
  | _ => e
  end.

(* [comment removed for export] *)
Fixpoint eval_closed (e : expr) : option Z :=
  match e with
  | ELit z => Some (z mod two64)%Z
  | EVar _ => None
  | EAlu op a b => match eval_closed a, eval_closed b with
                   | Some x, Some y => Some (zalu op x y) | _, _ => None end
  | EAluw op a b => match eval_closed a, eval_closed b with
                    | Some x, Some y => Some (zaluw op x y) | _, _ => None end
  | EMd op a b => match eval_closed a, eval_closed b with
                  | Some x, Some y => Some (zmd op x y) | _, _ => None end
  | EMdw op a b => match eval_closed a, eval_closed b with
                   | Some x, Some y => Some (zmdw op x y) | _, _ => None end
  | EExt sx lo n a => match eval_closed a with
                      | Some x => Some (zext_lit sx lo n x) | None => None end
  | EBlob _ _ _ _ => None
  end.

(* [comment removed for export] *)
Fixpoint subexprs (e : expr) : list expr :=
  match e with
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => subexprs a ++ subexprs b ++ [e]
  | EExt _ _ _ a => subexprs a ++ [e]
  | _ => [e]
  end.

(* [comment removed for export] *)
Fixpoint all_eval_to (s e : expr) (v lo : Z) (cnt : nat) : bool :=
  match cnt with
  | O => true
  | S c => match eval_closed (esubst s (ELit lo) e) with
           | Some w => if Z.eqb w v then all_eval_to s e v (lo + 1) c else false   (* [comment removed for export] *)
           | None => false
           end
  end.

Fixpoint evalS (s : expr) (z : Z) (e : expr) : option Z :=
  if expr_eqb e s then Some z else
  match e with
  | ELit w => Some (wrap64 w)
  | EVar _ => None
  | EAlu op a b => match evalS s z a with
                   | Some x => match evalS s z b with Some y => Some (zfast op x y) | None => None end
                   | None => None
                   end
  | EAluw op a b => match evalS s z a with
                    | Some x => match evalS s z b with Some y => Some (zfastw op x y) | None => None end
                    | None => None
                    end
  | EMd op a b => match evalS s z a with
                  | Some x => match evalS s z b with Some y => Some (zfastm op x y) | None => None end
                  | None => None
                  end
  | EMdw op a b => match evalS s z a with
                   | Some x => match evalS s z b with Some y => Some (zmdw op x y) | None => None end
                   | None => None
                   end
  | EExt sx lo n a => match evalS s z a with
                      | Some x => Some (zext_fast sx lo n x) | None => None end   (* [comment removed for export] *)
  | EBlob _ _ _ _ => None
  end.

(* [comment removed for export] *)
Fixpoint all_eval_toS (s e : expr) (v lo : Z) (cnt : nat) : bool :=
  match cnt with
  | O => true
  | S c => match evalS s (wrap64 lo) e with
           | Some w => if Z.eqb w v then all_eval_toS s e v (lo + 1) c else false
           | None => false
           end
  end.

(* [comment removed for export] *)
Definition probeS (s e : expr) (v z : Z) : bool :=
  match evalS s (wrap64 z) e with Some w => Z.eqb w v | None => false end.

Fixpoint memE (e : expr) (l : list expr) : bool :=
  match l with [] => false | x :: r => if expr_eqb e x then true else memE e r end.

Fixpoint nubE_acc (l acc : list expr) : list expr :=
  match l with
  | [] => []
  | x :: r => if memE x acc then nubE_acc r acc else x :: nubE_acc r (x :: acc)
  end.
Definition nubE (l : list expr) : list expr := nubE_acc l [].

Definition conc_limit : Z := 4096.

(* [comment removed for export] *)
Fixpoint evalS_def (s e : expr) : bool :=
  if expr_eqb e s then true else
  match e with
  | ELit _ => true
  | EVar _ => false
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => if evalS_def s a then evalS_def s b else false
  | EExt _ _ _ a => evalS_def s a
  | EBlob _ _ _ _ => false
  end.

Fixpoint conc_try (kn : list kentry) (e : expr) (cands : list expr) : option Z :=
  match cands with
  | [] => None
  | s :: rest =>
      if closedb s then conc_try kn e rest else
      if negb (evalS_def s e) then conc_try kn e rest else
      match erange kn s with
      | Some (lo, hi) =>
          if Z.leb (hi - lo) conc_limit then
            match evalS s (wrap64 lo) e with
            | Some v =>
                if (if Z.ltb hi lo then true
                     else if probeS s e v hi then probeS s e v (lo + (hi - lo) / 2)%Z else false) then
                  if all_eval_toS s e v lo (Z.to_nat (hi - lo + 1)) then Some v
                  else conc_try kn e rest
                else conc_try kn e rest
            | None => conc_try kn e rest
            end
          else conc_try kn e rest
      | None => conc_try kn e rest
      end
  end.

(* [comment removed for export] *)
Fixpoint conc_try_ref (kn : list kentry) (e : expr) (cands : list expr) : option Z :=
  match cands with
  | [] => None
  | s :: rest =>
      if closedb s then conc_try_ref kn e rest else
      match erange kn s with
      | Some (lo, hi) =>
          if Z.leb (hi - lo) conc_limit then
            match evalS s (wrap64 lo) e with
            | Some v =>
                if (if Z.ltb hi lo then true
                     else if probeS s e v hi then probeS s e v (lo + (hi - lo) / 2)%Z else false) then
                  if all_eval_toS s e v lo (Z.to_nat (hi - lo + 1)) then Some v
                  else conc_try_ref kn e rest
                else conc_try_ref kn e rest
            | None => conc_try_ref kn e rest
            end
          else conc_try_ref kn e rest
      | None => conc_try_ref kn e rest
      end
  end.

Lemma evalS_def_None : forall s e z, evalS_def s e = false -> evalS s z e = None.
Proof.
ltac2:(KReplay.run1 (kr_t_AxSymExec3 ()) [] "p'0h01Hh14IHe1h22E1h31bi001bh41oi011oh52H0h64IHe2h71eh82e1h92e2h:2oph;1nh<2sxh=2z0h>3IHeh?2e0h@1ihA1khB2lohC1shD1zi021zi031xi041yp;1p;2p;3p;6p;4p;:g00n1R0j1NTg00OHj1MTg0138j1GTg0145j28Tg0154j1LTg008Lj30Tg00dBj29Tg0161j1;Tg007Fj2:Tg016nj3FTg017kj27Tg018kj34Tg019gj3CTg00Q0j66Tg01:cj3@Tg01;`j3ATg01<]j3BTg01=Zj3?Tg01>Wj3>Tg01?Tj3ETg01@Oj4=Tg01ALj4KTg01BLj4DTg01CIl:HTg00nSj2ITg00SYj6JTg00?iR1f1R2f0R3'7g00ZER430p=3f4R5f3R6f2R7;42;03p=2A0134p=5g00;6R8/I3p=1P1g00@IR9P2g00g=P4P3EJp=<g01DHR:1363%N8R;P5P7P2%M8R<D2[X7:%G3R=/86P1P1P1P1P3P9P9n0100000020000#5P1P;P2%15R>%L6#1R?n0100000020000=0;<[P3A0194R@P1p-0P3g00Zeg00[ARAn0110000020000RBX71/<3RCPAA0;></93b5W0RDPCPAA0;?</93b5X0@n0110000020000b3136=P;P5P7%G2P<D2[eX=8g01EER=%;3R?/86P1P1P1P1P3P9P4n0100000020000#5REP1P;P2P>P<n0100000020000=0;<[P3PDA0144RD1:;<R>W0RFn0110000020000b3136?P;P5P7%;2P<D2[eW;g01EdR?1353P;f5RGP6P2P<D2[RHf6RI/33P;f7RJPGP2P<D2[RKAF562RL/8JP1P1P1P1P3P9P1P1f9RM/7GRN17M6ROP4n0100000020000n0100000020000#5RPP1P;P2f8RQ#1RRP0P8P;f:RS?4QIRTP0P8P;f;RU?4MGRVACM23#1P<n10110300021010400P<n10110300021010300n0100000020000=0;<[P3PCPAA0;R</93RWb5X0@RXP1P117Q517Q7RYP4n0100000020000#5RZPNP11:13R[17SI=013R\P1f<R]/7Q=013R^%52f>R_?4]SR`=0;<[RaP1P1P717_QP4n0100000020000#5RbP0P8P;f?f=Rc;4URdP0P8P;f@?4_SReAC_23#1RfP<n10110300021010400RgP<n10110300021010300=0;<]0]1]2P217UJRh=019RiP;PcPUPMP<D2RU\@Rj13cJRcP;P<P0P8P;PdP0P8P;P2PfP<n10110300021010400P<n10110300021010300=0;<X4;P`P;P0P8A0;2<\@P0P8P;P2P<P<n10110300021010300=0;<]1P3%12=0;<\@P>W1X=8P3O1A0;<<\@P>W1n10110100021010200P7O1b4RfA4_]QR]PJP3O1RkE6W0W1W2%5hRhPU\DRUP;P<P0P8P;P3PgP<n10110300021010300=0;<X4;P>P`P21:14O1R4E6X0DW1W2n0110000020000P3PIP7O3b2b3W0n0110000020001b313JLP;PQPIAFG57P<D2[eW6X9:W1X8:W:A@562RL/8JP1P1P1P;P2PRP0P8P;PTP0P8P;PVAAM23#1P<n10110300021010400P<n10110300021010300n0100000020000=0;<\PP3PXPNP1P[P\P1P0P8P;PdP0P8P;PeAA_23#1RgP<n10110300021010400RlP<n10110300021010300=0;<^0b^1a^2^P2P;P<P0P8P;PdP0P8P;P2PgP<n10110300021010400P<n10110300021010300=0;<X4;PfP]PkE6X0cX1jX2iP;P<P0P8P;P3PlP<n10110300021010300=0;<X4;P>P`P4E6X0DX1UX2hn0110000020000P3PIP7O3b2b3X0Zn0110000020001b313JLP;PQPIA@G57P<D2[eX6KX9:X1HX8:X:?g01FPR?AB562RL/8JP1P1P1P;P2PRP0P8P;PTP0P8P;PVA?M23#1P<n10110300021010400P<n10110300021010300n0100000020000=0;<\PP3PXPNP1P[P\P1P0P8P;PdP0P8P;PeA?_23#1RlP<n10110300021010400RgP<n10110300021010300=0;<^0b^1a^2^P2P;P<P0P8P;PdP0P8P;P2PlP<n10110300021010400P<n10110300021010300=0;<X4;PfP]PkE6X0cX1jX2iP;P<P0P8P;P3PgP<n10110300021010300=0;<X4;P>P`P4E6X0DX1UX2hn0110000020000P3PIP7O3b2b3X0Zn0110000020001b313JLP;PQPIABG57P<D2[eX6KX9:X1HX8:W:A>562RL/8JP1P1P1P;P2PRP0P8P;PTP0P8P;PVAEM23#1P<n10110300021010400P<n10110300021010300n0100000020000=0;<\PP3PXPNP1P[P\P1P0P8P;PdP0P8P;PeAE_23#1R_P<n10110300021010400ReP<n10110300021010300=0;<^0b^1a^2^P2P;P<P0P8P;PdP0P8P;P2P_P<n10110300021010400P<n10110300021010300=0;<X4;PfP]PkE6X0cX1jX2iP;P<P0P8P;P3PeP<n10110300021010300=0;<X4;P>P`P4E6X0DX1UX2hn0110000020000P3PIP7O3b2b3X0Zn0110000020001b313JLP;PQPIA>G57P<D2[eX6KX9:X1HX8:X:?P5P6P7P2C=R?/8JP1P1P1P1P3P9POn0100000020000#5P1P;P2PRP0P8P;A4SQ5PQPJPIP3CK#1RSP<n10110300021010300n0100000020000=0;<[P3PBX?1/<3PAPWb5X0@%5YP;P<P0P8P;P3PSP<n10110300021010300=0;<X4;P>A4MJ6P7P3O1E6W0n0110000020000b313J?P;PQPIPGP5P6P7C=P<D2[eX>KX7:X;=XB=X<1P6P7P2P3CDRK/8IP1P1P1P;P2%1JRQP<n0100000020000=0;<\EP3PCPAA0;Q</93b5X0@PFn0110000020000b313IKP;PJPGP5P6P7P2CDP<D2[eX;=X@8XA=X<1P2M:HXD8X7:WCo"). Qed.
Lemma conc_try_eq : forall kn e cands, conc_try kn e cands = conc_try_ref kn e cands.
Proof.
ltac2:(KReplay.run1 (kr_t_AxSymExec3 ()) [] "p'0h02Hdh11bi001bh21oi011oh35candsh42IHh51eh62hii022hih72knh82loi032loh91pi041ph:4resth;1si051vi061xi071zp;1p;3p;2p;4p;5p;6g002kj1?Tg00n1R0j1DTg01G<j39Tg01H;j30Tg008Lj31Tg002Kj1LTg007Fj25Tg01I>j1<Tg017kj28Tg01J<j16Tg01JZR1j2ETg01K:j27Tg00Cbj2;Tg00Bhj2CTg0154j1MTg018kj33Tg00CEj2@Tg01L7j42Tg001Hj1KTg001mj1>Tg00Jbj2ATg00K\j2:Tg01M4j1=Tg01MTj54Tg00nSj2ITg00OHj1HTg01NWj4GTg00Q0j6BTg00e^j3FTg00daj5JTg00f>#?g01DHR2%?2R3P2g00;6R4#DR5f3R6f2R7f0R839A067831X33f1R9%L2507,55f4R:?968A0:68515P5f5R;?0:9g00?iR<P5%<6R=P8P<P5186;R>#6P8P01E44R?P5f6R@/76RAP1P4P4P5P8P<P51;89g01O\RB'CRCP0P4P5%M9RDf8RE53@RFP<P5P<P<1@97RGg00@IRHP<P<f7RIf9RJP8P9C2PIPJP81;97RKg00;TRL#K#>RM'A,:7RNC2g00ZEROn0100000020000n0100000020000RPP<P5PIPJP8P7%>LRL,:K#=RQD4RR1I48RSP:n0100000020000P:n0100000020000P6n10110600021010500P6n0100000020000n2001104000120103102P8n10110600021010400n0100000020000n0100000020000P<P5P=A0@;7R=P0P?P5PAP1P4P4P5P8P<P5PCP0P4P5PFP<P5PPP<P5PRPSf:RR?0J@RPn0100000020000PPn0100000020000A0JE;RFn10110600021010500PFn0100000020000n2001104000120103102P=n10110600021010400n0100000020000515X25%<7P<P<P<P5P8A0I@6RAP<P518:@RT#6PAP0P?P517I:P1P4P4P5P8P<P5PCP0P4P5A3IDJP<P5P<P<PGPHP<P<PEPRP8P9C2PEPRP8PNC2POn0100000020000n0100000020000P<P5PEPRP8P7PQD4PSf;RU?0RIRVn0100000020000PVn0100000020000PPn10110600021010500PPn0100000020000n2001104000120103102PAn10110600021010400RWn0100000020000n0100000020000P<P5P8PAPWn0100000020000515P8155=P>P<15<8A1<T8P<18@E=1<8P<P5%69PPP0P?P517RIP1P4P4P5P8P<P5PCP0P4P5f<RT93RDP<P5P<P<PGPHP<P<PUf=R>P8P9C2PUP>P8PNC2POn0100000020000n0100000020000P<P5PUP>P8P7PQD4PSf>R=?0>RRWn0100000020000PWn0100000020000A0>TJRAn10110600021010500PAn0100000020000n2001104000120103102PPn10110600021010400RXn0100000020000=15X]0P918;IRX=1<HP0P?P517J@R@P1P4P4P5P8P<P5PCP0P4P5A3JDUP<P5P<P<PGPHP<P<PRPTP8P9C2PRPTP8PNC2POn0100000020000n0100000020000P<P5PRPTP8P7PQD4PSPAn0100000020000PAn0100000020000A0TUEREn10110600021010500PEn0100000020000n2001104000120103102PFn10110600021010400RE,55P<P5%6HPFPEn0100000020000=15EeW0A1<XOP@%D?P0P?P0P?P5P8P1P4P4P5P8P<P5PCP0P4P5A3UD>P<P5P<P<PGPHP<P<PTP=P8P9C2PTP=P8PNC2POn0100000020000n0100000020000P<P5PTP=P8P7PQD4PSf?R@?0=URUn0100000020000PUn0100000020000PWn10110600021010500PWn0100000020000n2001104000120103102PVn10110600021010400915VP8P1P4P4P1P4P4P5P8P<P5PCP0P4P5A3TD=P<P5P<P<PGPHP<P<P>P@P8P9C2P>P@P8PNC2POn0100000020000n0100000020000P<P5P>P@P8P7PQD4PSf@RQ?0@TRTn0100000020000PTn0100000020000PUn10110600021010500PUn0100000020000n2001104000120103102915AP8P5%H4fARA?0Q>RQP<P51CKBP0P4P5P8P<P5P<P<1@76PHP<P<P@PAP8P7C2P@PAP81;76RH/AM,:6C2POn0100000020000n0100000020000P<P5P@PAP8P61:HL#=D4PSfB?0A=RAn0100000020000PAn0100000020000PQn10110600021010500PQn0100000020000515X25PCP<P<P<P5P8PAPAn0100000020000915AP8155QRQPQn0110000020000b1A3>D@P>P@PDPICGEBX64X84P9P8O2n2001104000120107107X9?P8O1155Pn10110100021110400b2P<P5%6OPFPEn0100000020000=15EeW0n0110000020101P8O1b0b1n0110001020001b1A9;:9P8EBAF279R999;:A0;:9515eW4X:3X;2P8DJW3W5W7o"). Qed.

Definition concretize (kn : list kentry) (e : expr) : option Z :=
  if closedb e then eval_closed e else conc_try kn e (nubE (subexprs e)).

(* [comment removed for export] *)
Definition foldK (kn : list kentry) (e : expr) : expr :=
  match e with
  | ELit _ => e
  | _ => match erange kn e with
         | Some (lo, hi) => if Z.eqb lo hi then ELit lo
                            else match concretize kn e with Some v => ELit v | None => e end
         | None => match concretize kn e with Some v => ELit v | None => e end   (* [comment removed for export] *)
         end
  end.

Definition lit_branch (c : branch_cond) (x y : Z) : bool :=
  branch_taken c (Z_to_bv 64 x) (Z_to_bv 64 y).

(* [comment removed for export] *)
Definition cond_on_eq (c : branch_cond) : bool :=
  match c with
  | BC_EQ => true | BC_NE => false | BC_LT => false | BC_GE => true
  | BC_LTU => false | BC_GEU => true
  end.

(* [comment removed for export] *)
Definition itv_ltu (al ah bl bh : Z) : option bool :=
  if Z.ltb ah bl then Some true else if Z.leb bh al then Some false else None.

(* [comment removed for export] *)
Definition itv_lts (al ah bl bh : Z) : option bool :=
  let h := (2 ^ 63)%Z in
  if ((Z.ltb ah h && Z.ltb bh h) || (Z.leb h al && Z.leb h bl))%bool then itv_ltu al ah bl bh
  else if (Z.leb h al && Z.ltb bh h)%bool then Some true
  else if (Z.ltb ah h && Z.leb h bl)%bool then Some false
  else None.

Definition range_branch (c : branch_cond) (al ah bl bh : Z) : option bool :=
  match c with
  | BC_EQ =>
      if (Z.ltb ah bl || Z.ltb bh al)%bool then Some false
      else if (Z.eqb al ah && Z.eqb bl bh && Z.eqb al bl)%bool then Some true else None
  | BC_NE =>
      if (Z.ltb ah bl || Z.ltb bh al)%bool then Some true
      else if (Z.eqb al ah && Z.eqb bl bh && Z.eqb al bl)%bool then Some false else None
  | BC_LTU => itv_ltu al ah bl bh
  | BC_GEU => option_map negb (itv_ltu al ah bl bh)
  | BC_LT => itv_lts al ah bl bh
  | BC_GE => option_map negb (itv_lts al ah bl bh)
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition diff_branch (c : branch_cond) (a b : expr) : option bool :=
  match c with
  | BC_EQ | BC_NE =>
      match is_lit (mkAlu ALU_SUB a b) with
      | Some z => let e := Z.eqb (z mod two64) 0 in Some (match c with BC_EQ => e | _ => negb e end)
      | None => None
      end
  | _ => None
  end.

(* [comment removed for export] *)
Definition lin_branch (kn : list kentry) (c : branch_cond) (a b : expr) : option bool :=
  let ltu := if lin_ge0 kn [(b, (-1)%Z)] [(a, 0%Z)] then Some true
             else if lin_ge0 kn [(a, 0%Z)] [(b, 0%Z)] then Some false else None in
  match c with
  | BC_LTU => ltu
  | BC_GEU => option_map negb ltu
  | BC_LT | BC_GE =>
      match erange kn a, erange kn b with
      | Some (_, ah), Some (_, bh) =>
          if (Z.ltb ah (2 ^ 63) && Z.ltb bh (2 ^ 63))%bool
          then match c with BC_LT => ltu | _ => option_map negb ltu end
          else None
      | _, _ => None
      end
  | BC_EQ | BC_NE =>
      (* [comment removed for export] *)
      if (lin_ge0 kn [(b, (-1)%Z)] [(a, 0%Z)] || lin_ge0 kn [(a, (-1)%Z)] [(b, 0%Z)])%bool
      then Some (match c with BC_EQ => false | _ => true end)
      else
      (* [comment removed for export] *)
      if (if lin_ge0 kn [(a, 0%Z)] [(b, 0%Z)] then lin_ge0 kn [(b, 0%Z)] [(a, 0%Z)] else false)
      then Some (match c with BC_EQ => true | _ => false end)
      else None
  end.

Definition decide_branch (kn : list kentry) (c : branch_cond) (a b : expr) : option bool :=
  match a, b with
  | ELit x, ELit y => Some (lit_branch c x y)
  | _, _ =>
      if expr_eqb a b then Some (cond_on_eq c)
      else match diff_branch c a b with
           | Some t => Some t
           | None =>
             match (match erange kn a, erange kn b with
                    | Some (al, ah), Some (bl, bh) => range_branch c al ah bl bh
                    | _, _ => None
                    end) with
             | Some t => Some t
             | None => lin_branch kn c a b      (* [comment removed for export] *)
             end
           end
  end.


(* [comment removed for export] *)
Definition mkSlt (kn : list kentry) (c : branch_cond) (op : aluop) (a b : expr) : expr :=
  match a, b with
  | ELit _, ELit _ => mkAlu op a b
  | _, _ => match decide_branch kn c a b with
            | Some true => ELit 1
            | Some false => ELit 0
            | None => mkAlu op a b
            end
  end.

Definition mkAluK0 (kn : list kentry) (op : aluop) (a b : expr) : expr :=
  match op with
  | ALU_SLTU => mkSlt kn BC_LTU ALU_SLTU a b
  | ALU_SLT => mkSlt kn BC_LT ALU_SLT a b
  | ALU_AND => match a, b with
               | ELit _, ELit _ => mkAnd kn a b
               | ELit _, _ => mkAndK kn b a      (* [comment removed for export] *)
               | _, _ => mkAndK kn a b
               end
  | ALU_OR => if expr_eqb a b then a else mkOr kn a b
  | ALU_XOR => if expr_eqb a b then ELit 0 else match is_lit a, b with
               | None, ELit k => if Z.eqb (k mod two64) (two64 - 1) then mkAlu ALU_SUB (ELit (two64 - 1)) a
                                else mkAlu op a b
               | _, _ => mkAlu op a b
               end
  | ALU_SRL => match is_lit a, shamt_of b 6 with
               | None, Some s => mkSrl kn a s
               | _, _ => mkAlu op a b
               end
  | _ => mkAlu op a b
  end.

(* [comment removed for export] *)
Definition zsx32 (v : Z) : Z := ((bv_swrap 32 v) mod two64)%Z.

Definition mkAluK (kn : list kentry) (op : aluop) (a b : expr) : expr :=
  foldK kn (mkAluK0 kn op a b).

(* [comment removed for export] *)
Definition pow2_log (m : Z) : option Z :=
  let m' := (m mod two64)%Z in
  let k := Z.log2 m' in
  if (Z.ltb 0 m' && Z.eqb m' (2 ^ k) && Z.ltb k 64)%bool then Some k else None.

Definition mkMdK (kn : list kentry) (op : mulop) (a b : expr) : expr :=
  match is_lit a, op, b with
  | None, M_REMU, ELit m =>
      match pow2_log m with
      | Some k => mkAluK kn ALU_AND a (ELit (2 ^ k - 1))
      | None => mkMd op a b
      end
  | None, M_DIVU, ELit m =>
      match pow2_log m with
      | Some k => mkAluK kn ALU_SRL a (ELit k)
      | None => mkMd op a b
      end
  | _, _, _ => mkMd op a b
  end.

(* [comment removed for export] *)
Definition sx32_stable (lo hi : Z) : bool :=
  (Z.ltb hi (2 ^ 31) || Z.leb (two64 - 2 ^ 31) lo)%bool.

(* [comment removed for export] *)
Definition zband32 (kn : list kentry) (d : expr) : bool :=
  let l := lin_of d in
  match lin_range (erange kn) (fst l) (snd l) with
  | Some (lo, hi) => (Z.ltb (- 2 ^ 31) lo && Z.ltb hi (2 ^ 31))%bool
  | None => false
  end.

Definition mkAluwK0 (kn : list kentry) (op : aluop) (a b : expr) : expr :=
  match op with
  | ALU_ADD | ALU_SUB =>
      let d := mkAlu op a b in
      match is_lit d with
      | Some v => ELit (zsx32 v)
      | None => match erange kn d with
                | Some (lo, hi) => if sx32_stable lo hi then d else if zband32 kn d then d else mkAluw op a b
                | None => if zband32 kn d then d else mkAluw op a b
                end
      end
  | _ => mkAluw op a b
  end.

Definition mkAluwK (kn : list kentry) (op : aluop) (a b : expr) : expr :=
  foldK kn (mkAluwK0 kn op a b).

(* [comment removed for export] *)
Definition extK0 (kn : list kentry) (v : expr) : expr :=
  match v with
  | EExt sx O n e =>
      if Nat.leb n 7 then
        match erange kn e with
        | Some (lo, hi) => if Z.ltb hi (if sx then 2 ^ (8 * Z.of_nat n) / 2 else 2 ^ (8 * Z.of_nat n)) then e else v
        | None => v
        end
      else v
  | _ => v
  end.

Definition extK (kn : list kentry) (v : expr) : expr := foldK kn (extK0 kn v).

Definition msize_bytes (sz : msize) : nat :=
  match sz with SZ1 => 1 | SZ2 => 2 | SZ4 => 4 | SZ8 => 8 end.

(* [comment removed for export] *)
Definition flat_sc (kn : list kentry) (a : saddr) (n : nat) : list sidecond :=
  match base_range kn (a_base a) with
  | Some (lo, hi) =>
      if (Z.leb 0 (lo + a_off a) && Z.leb (hi + a_off a + Z.of_nat n) (2 ^ 64))%bool
      then [] else [SCFlat a (elen n)]
  | None => [SCFlat a (elen n)]
  end.

(* [comment removed for export] *)
Fixpoint wr_covered (allkn kn : list kentry) (a : saddr) (n : nat) : bool :=
  match kn with
  | [] => false
  | KWr (SA kb kk) len :: rest =>
      if (if (expr_eqb (a_base a) kb && Z.leb kk (a_off a))%bool
          then match xlo allkn len with Some l => Z.leb (a_off a + Z.of_nat n) (kk + l) | None => false end
          else false)
      then true
      else if xinside allkn (a_base a) (a_off a) (ELit (Z.of_nat n)) kb kk len then true
      else wr_covered allkn rest a n
  | _ :: rest => wr_covered allkn rest a n
  end.

Definition storeok_sc (kn : list kentry) (a : saddr) (n : nat) : list sidecond :=
  if wr_covered kn kn a n then [] else [SCStoreOk a n].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record scripts : Type := SCR {
  sc_dirs  : list bool;     (* [comment removed for export] *)
  sc_reads : list expr;     (* [comment removed for export] *)
  sc_hints : list bool      (* [comment removed for export] *)
}.

Inductive stepres :=
| SOk (ss : sym_state) (scs : list sidecond) (scr : scripts)
| SStop.

(* [comment removed for export] *)
Definition conc_expr (kn : list kentry) (e : expr) : expr :=
  match e with
  | ELit _ => e
  | _ => match concretize kn e with Some v => ELit v | None => e end
  end.

(* [comment removed for export] *)
Definition cond_probe (c : branch_cond) (a b : expr) : expr * bool :=
  match c with
  | BC_EQ => (EAlu ALU_SLTU (EAlu ALU_SUB a b) (ELit 1%Z), true)    (* [comment removed for export] *)
  | BC_NE => (EAlu ALU_SLTU (EAlu ALU_SUB a b) (ELit 1%Z), false)
  | BC_LT => (EAlu ALU_SLT a b, true)
  | BC_GE => (EAlu ALU_SLT a b, false)
  | BC_LTU => (EAlu ALU_SLTU a b, true)
  | BC_GEU => (EAlu ALU_SLTU a b, false)
  end.

Definition enum_branch (kn : list kentry) (c : branch_cond) (a b : expr) : option bool :=
  let '(e, pos) := cond_probe c a b in
  match concretize kn e with
  | Some v => let z := Z.eqb (v mod two64) 0 in Some (if pos then negb z else z)
  | None => None
  end.

(* [comment removed for export] *)
Definition to_saddrK (kn : list kentry) (e : expr) (imm : Z) : saddr :=
  match split_lit e with
  | (ELit _, _) => to_saddr e imm
  | _ => match concretize kn (mkAlu ALU_ADD e (ELit imm)) with
         | Some v => SA (ELit 0) v
         | None => to_saddr e imm
         end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition amo_sz (wd : awidth) : msize := match wd with AW => SZ4 | AD => SZ8 end.
(* [comment removed for export] *)
Definition amo_sx (wd : awidth) : bool := match wd with AW => true | AD => false end.

(* [comment removed for export] *)
Definition amo_alignedb (kn : list kentry) (e : expr) (wd : awidth) : bool :=
  match lin_lowbits_kn kn e (match wd with AW => 2 | AD => 3 end) with
  | Some r => Z.eqb r 0
  | None => false
  end.

(* [comment removed for export] *)
Definition resv_inval (r : option saddr) (a : saddr) : option (option saddr) :=
  match r with
  | None => Some None
  | Some ra =>
      if saddr_eqb ra a then Some None
      else if (expr_eqb (a_base ra) (a_base a) && negb (Z.eqb ((a_off ra - a_off a) mod two64) 0))%bool
           then Some r
           else None
  end.

(* [comment removed for export] *)
Definition amo_aluop (op : amoop) : option (option aluop) :=
  match op with
  | AMO_SWAP => Some None
  | AMO_ADD => Some (Some ALU_ADD)
  | AMO_XOR => Some (Some ALU_XOR)
  | AMO_AND => Some (Some ALU_AND)
  | AMO_OR => Some (Some ALU_OR)
  | _ => None
  end.

(* [comment removed for export] *)
Definition amo_newval (kn : list kentry) (wd : awidth) (aop : option aluop) (old src : expr) : expr :=
  match aop with
  | None => src
  | Some o => match wd with AW => mkAluwK kn o old src | AD => mkAluK kn o old src end
  end.

(* [comment removed for export] *)
Definition sym_read (segs : list Segment) (ss : sym_state) (fk : list kentry) (scr : scripts)
           (a : saddr) (n : nat) (sx' : bool)
  : option (expr * list sidecond * scripts * nat) :=
  match log_lookup fk (s_log ss) (a_base a) (a_off a) n sx' (sc_hints scr) [] with
  | LStuck => None
  | LHit v scs hints =>
      Some (extK fk v, flat_sc fk a n ++ scs, SCR (sc_dirs scr) (sc_reads scr) hints, s_next ss)
  | LMiss scs hints =>
      match know_lookupA fk segs (s_know ss) (a_base a) (a_off a) n sx' hints scs with
      | LStuck => None
      | LHit v scs' hints' =>
          Some (extK fk v, flat_sc fk a n ++ scs', SCR (sc_dirs scr) (sc_reads scr) hints', s_next ss)
      | LMiss scs' hints' =>
          (* [comment removed for export] *)
          let i := s_next ss in
          let rv := match sc_reads scr with [] => EVar i | e :: _ => e end in
          let reads' := match sc_reads scr with [] => [] | _ :: t => t end in
          Some (rv, flat_sc fk a n ++ SCReadBase a n sx' rv :: scs', SCR (sc_dirs scr) reads' hints', S i)
      end
  end.

Definition sym_step (segs : list Segment) (i : instr) (ss : sym_state) (scr : scripts) : stepres :=
  let g r := sr_get (s_regs ss) r in
  let p := s_pc ss in
  let fk := facts_of (s_know ss) in   (* [comment removed for export] *)
  match i with
  | OpImm op rd rs imm => SOk (sset ss rd (mkAluK fk op (g rs) (ELit (bv_signed imm))) (p + 4)) [] scr
  | ShiftImm op rd rs sh => SOk (sset ss rd (mkAluK fk op (g rs) (ELit (bv_unsigned sh))) (p + 4)) [] scr
  | Op op rd rs1 rs2 => SOk (sset ss rd (mkAluK fk op (g rs1) (g rs2)) (p + 4)) [] scr
  | OpImm32 rd rs imm => SOk (sset ss rd (mkAluwK fk ALU_ADD (g rs) (ELit (bv_signed imm))) (p + 4)) [] scr
  | ShiftImm32 op rd rs sh => SOk (sset ss rd (mkAluw op (g rs) (ELit (bv_unsigned sh))) (p + 4)) [] scr
  | Op32 op rd rs1 rs2 => SOk (sset ss rd (mkAluwK fk op (g rs1) (g rs2)) (p + 4)) [] scr
  | Mul op rd rs1 rs2 => SOk (sset ss rd (mkMdK fk op (g rs1) (g rs2)) (p + 4)) [] scr
  | Mul32 op rd rs1 rs2 => SOk (sset ss rd (mkMdw op (g rs1) (g rs2)) (p + 4)) [] scr
  | Lui rd imm => SOk (sset ss rd (ELit (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_signed imm) 12)))) (p + 4)) [] scr
  | Auipc rd imm => SOk (sset ss rd (ELit (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_signed imm) 12 + p)))) (p + 4)) [] scr
  | Jal rd imm => SOk (sset ss rd (ELit (p + 4)) (bv_unsigned (Z_to_bv 64 (p + bv_signed imm)))) [] scr
  | Jalr rd rs1 imm =>
      match conc_expr fk (g rs1) with
      | ELit z => SOk (sset ss rd (ELit (p + 4)) (Z.land (bv_wrap 64 z + bv_signed imm) (-2) mod 2^64)) [] scr
      | _ => SStop
      end
  | Branch c rs1 rs2 imm =>
      let tk := bv_unsigned (Z_to_bv 64 (p + bv_signed imm)) in
      let a := g rs1 in let b := g rs2 in
      match match decide_branch fk c a b with
            | Some t => Some t
            | None => match decide_branch fk c (conc_expr fk a) (conc_expr fk b) with
                      | Some t => Some t
                      | None => enum_branch fk c a b
                      end
            end with
      | Some t => SOk (sjump ss (if t then tk else p + 4)) [] scr
      | None =>
          match sc_dirs scr with
          | [] => SStop
          | t :: dirs' =>
              SOk (sjump ss (if t then tk else p + 4)) [SCBr t c a b]
                  (SCR dirs' (sc_reads scr) (sc_hints scr))
          end
      end
  | Fence _ _ _ _ _ => SOk (sjump ss (p + 4)) [] scr
  | FenceI _ _ _ => SOk (sjump ss (p + 4)) [] scr
  | Load sz sx rd rs imm =>
      let n := msize_bytes sz in
      (* [comment removed for export] *)
      let sx' := match sz with SZ8 => false | _ => sx end in
      let a := to_saddrK fk (g rs) (bv_signed imm) in
      match sym_read segs ss fk scr a n sx' with
      | None => SStop
      | Some (v, scs, scr', nx') =>
          SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) v)
                   (s_log ss) (s_know ss) nx' (s_resv ss)) scs scr'
      end
  | Store sz rs1 rs2 imm =>
      let n := msize_bytes sz in
      let a := to_saddrK fk (g rs1) (bv_signed imm) in
      match resv_inval (s_resv ss) a with
      | None => SStop
      | Some r' =>
          SOk (SSR (p + 4) (s_regs ss) (log_push a n (g rs2) (s_log ss)) (s_know ss) (s_next ss) r')
              (flat_sc fk a n ++ storeok_sc fk a n) scr
      end
  (* [comment removed for export] *)
  | Lr wd _ _ rd rs =>
      let n := msize_bytes (amo_sz wd) in
      let e := g rs in
      if amo_alignedb fk e wd then
        let a := to_saddrK fk e 0 in
        match sym_read segs ss fk scr a n (amo_sx wd) with
        | None => SStop
        | Some (v, scs, scr', nx') =>
            SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) v)
                     (s_log ss) (s_know ss) nx' (Some a)) scs scr'
        end
      else SStop
  | Sc wd _ _ rd rs1 rs2 =>
      let n := msize_bytes (amo_sz wd) in
      let e := g rs1 in
      if amo_alignedb fk e wd then
        let a := to_saddrK fk e 0 in
        match s_resv ss with
        | Some r =>
            if saddr_eqb r a then
              SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) (ELit 0))
                       (log_push a n (g rs2) (s_log ss)) (s_know ss) (s_next ss) None)
                  (flat_sc fk a n ++ storeok_sc fk a n) scr
            else SStop   (* [comment removed for export] *)
        | None => SStop
        end
      else SStop
  | Amo op wd _ _ rd rs1 rs2 =>
      match amo_aluop op with
      | None => SStop
      | Some aop =>
          let n := msize_bytes (amo_sz wd) in
          let e := g rs1 in
          if amo_alignedb fk e wd then
            let a := to_saddrK fk e 0 in
            match resv_inval (s_resv ss) a with
            | None => SStop
            | Some r' =>
                match sym_read segs ss fk scr a n (amo_sx wd) with
                | None => SStop
                | Some (vold, scs, scr', nx') =>
                    SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) vold)
                             (log_push a n (amo_newval fk wd aop vold (g rs2)) (s_log ss)) (s_know ss) nx' r')
                        (scs ++ storeok_sc fk a n) scr'
                end
            end
          else SStop
      end
  | _ => SStop
  end.



(* [comment removed for export] *)
Definition sidecond_eqb (x y : sidecond) : bool :=
  match x, y with
  | SCFlat a n, SCFlat a' n' => saddr_eqb a a' && expr_eqb n n'
  | SCStoreOk a n, SCStoreOk a' n' => saddr_eqb a a' && Nat.eqb n n'
  | SCDisj a n b m, SCDisj a' n' b' m' =>
      saddr_eqb a a' && expr_eqb n n' && saddr_eqb b b' && expr_eqb m m'
  | SCInside a n b m, SCInside a' n' b' m' =>
      saddr_eqb a a' && expr_eqb n n' && saddr_eqb b b' && expr_eqb m m'
  | _, _ => false
  end.

Fixpoint sc_mem (x : sidecond) (l : list sidecond) : bool :=
  match l with [] => false | y :: t => sidecond_eqb x y || sc_mem x t end.

Fixpoint sc_add (news acc : list sidecond) : list sidecond :=
  match news with
  | [] => acc
  | x :: t => sc_add t (if sc_mem x acc then acc else x :: acc)
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition itab : Type := ptree instr.
Definition itab_lookup (t : itab) (pc : Z) : option instr :=
  match pc with Zpos p => pt_get t p | _ => None end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
Definition itab_entry (pc : Z) : option instr :=
  match fetch_word segs (Z_to_bv 64 pc) with
  | None => None
  | Some w => if is_ecall w then None else
              match decode_any w with
              | Some (i, sz) => if Z.eqb sz 4 then Some i else None
              | None => None
              end
  end.
Fixpoint mk_itab_fuel (n : nat) (pc : Z) (t : itab) : itab :=
  match n with
  | O => t
  | S n' => mk_itab_fuel n' (pc + 4)%Z
            (match pc, itab_entry pc with
             | Zpos p, Some i => pt_set p i t
             | _, _ => t
             end)
  end.
(* [comment removed for export] *)
Definition mk_itab (lo : Z) (n : nat) : itab := mk_itab_fuel n lo PTLeaf.
Definition itab_sound (t : itab) : Prop :=
  forall pc i, itab_lookup t pc = Some i -> itab_entry pc = Some i.
Lemma mk_itab_fuel_sound : forall n pc t, itab_sound t -> itab_sound (mk_itab_fuel n pc t).
Proof.
ltac2:(KReplay.run1 (kr_t_AxSymExec3 ()) ["WithSegs"] "p'0h01Eh11Hh22H0h31ei001eh41ni011nh51oi021oh62p'h72pci032pch81th92Hth:2i'h;1pi041ph<3Hneh=2IHh>1ii051ih?3pc'h@1si061si071xi081zp;1p;3p;2p;6p;4g01P]j15Tg01Q^j38Tg001Hj1<Tg001mj14Tg00K\j2MTg01Raj17Tg00n1R0j1BTg007Fj2@Tg008Lj30Tg00OHj1>Tg00SYj6;Tg00dBj2=Tg01Sbj2LTg00JIj1:Tg01TDR1j2KTg012[j6ITg01Tdj4HTg00Q0j69Tg01Uaj6ATg01V^j1CTg01W<j2DTg01X>j1ETg01X]j4FTg00l6j4GTg00nSj2?Tg00k9j3JTg01Y>R2f2R3f1R4f0R5CGp=31?25p=1%74=035p=2AJ245p=6g01EER6g00;6R7g01YjR8%55R9f3R:?834#5[]8]7R;X46P5g01Ze?834#5eX99X88X77P:g00;T#<#<#4,M3P7P8P3P4P0P2P8%45#7R<A345:P3n10110700021010500P3n011030003001010410104P7P7P8P5P3P0P2P8P<f4R=9345P:n10110700021010500P:n011030003001010410104#5P3P5g011XR>P<%B2R<1@<5%44#7R?=0<5P0P2%4:R@#7RA=0<5P0P2P8P4f5RBf8RC735f7RDn10110700021010500#5]0P4%4=%15RE52<P7P7P<P5%>2RFf9RGf<RH73B/65PFn011030003001010410104%14RI50<%13RJ92<4[P4A0<FEP<PFP0P2p-0P5g00[ARKg00Zen10110200021000000X3<RLg00g=RMPIP5E;PKg00>D=2<J/=5b2W11L5GA0>5GRN%:N'KP1f:R190>4RN%:Nf;RNf>RO73D/63%1=RP50<%1BRQ90<A[P5A0>3NRAP>PHf=f@RR73G/65f6RS#1RT50<%1DRU90<?[X6>P<%1CR?A0<5TRV%4O=2<U[X5<A0<?QP<P2P0P2P2P5P5P1n10110200021010500X3<%1GPTP5EIA02GSA021DP2PN%4R=2<EX:2P1PCP5E;W1P5O1b2W1f?RR93HCRN/6HP2PHPCPRCHE9P:P5E9W3P5O1%:AP<16R:%4B=2<U\VX5<POP@PBO216N:P2P:PHPCPRP5EAE9W<P5O1n200110600021010010101b@X6>P5O1A0<FJP<PFPLPM%1:P5E;PK%C3=2<P/=5b2W1X6>P5O1n011080003001110410104A3D:1/D4=0<EA2<3I[eX:2X?7A3B4C#5eW0X>2P5O1%43=2<FPBW0n10110200021110500P5O1b0b5W;P5O1P3X;>P5O1n011080003001110410104O3%E=?834#5eX99X88X77X=;X46P5CFW4o"). Qed.
Lemma mk_itab_sound : forall lo n, itab_sound (mk_itab lo n).
Proof.
ltac2:(KReplay.run1 (kr_t_AxSymExec3 ()) ["WithSegs"] "p'0h01Hh12H0h21pi001ph31eh41ih52loh61nh71oi011oh82pci022pci031zp;1p;3p;2p;6p;4g00o5j1?Tg00n1R0j1>Tg00OHj16Tg00k9j35Tg00nSj22Tg008Lj30Tg01Raj11Tg00SYj64Tg00dBj23Tg001mj17Tg01[Dj28Tg00Q0j69Tg01V^j1:Tg01W<j2=Tg01P]j1<Tg01\Fj4;Tg00;6R1g01EEf0R2f1R3g01Y>R4#?R5P1%>4R6P1P6P2%64R7A5452R8P7n0110200030010100101001243R930%13f2R:,24R;506[P31242R<9067P6P7P0P4p-0P2g00[AR0g00Zen10110100021000000X36R=g00g=R>P9P2E4P0g00>D#1=06;/32b1W0g011XR?P6P7f3,24R@9062%7:#1f4,24RA506RB[X76A067;R;P6P7P=P>P@P2E4R@P013B2b1W0P81842E9W2P2O1P@P0%::#1=06A/32b1X0;X2?P2O1n0110300030010100101001=53=06<%1:=069[eX44X81%<5eC;W6W5o"). Qed.

(* [comment removed for export] *)
Fixpoint sym_exec_go (fuel : nat) (first : bool) (stops : list Z) (scr : scripts)
                  (ss : sym_state) (acc : list sidecond)
                  (ck : sym_state * list sidecond * scripts)
  : sym_state * list sidecond * scripts :=
  match fuel with
  | O => if s_clean ss then (ss, acc, scr) else ck
  | S f =>
      if (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool then (if s_clean ss then (ss, acc, scr) else ck) else
      match fetch_word segs (Z_to_bv 64 (s_pc ss)) with
      | None => if s_clean ss then (ss, acc, scr) else ck
      | Some w =>
          if is_ecall w then (if s_clean ss then (ss, acc, scr) else ck) else
          match decode_any w with
          | None => if s_clean ss then (ss, acc, scr) else ck
          | Some (i, sz) =>
              if negb (Z.eqb sz 4) then (if s_clean ss then (ss, acc, scr) else ck) else
              match sym_step segs i ss scr with
              | SOk ss' scs scr' =>
                  let acc' := sc_add scs acc in
                  sym_exec_go f false stops scr' ss' acc'
                    (if s_clean ss' then (ss', acc', scr') else ck)
              | SStop => if s_clean ss then (ss, acc, scr) else ck
              end
          end
      end
  end.

Definition sym_exec (fuel : nat) (first : bool) (stops : list Z) (scr : scripts)
           (ss : sym_state) (acc : list sidecond) : sym_state * list sidecond * scripts :=
  sym_exec_go fuel first stops scr (clr ss) acc (clr ss, acc, scr).

(* [comment removed for export] *)
Definition scr_nil : scripts := SCR [] [] [].

Fixpoint sym_execS_go (fuel : nat) (first : bool) (stops : list Z) (ss : sym_state) (ck : sym_state)
  : sym_state :=
  match fuel with
  | O => if s_clean ss then ss else ck
  | S f =>
      if (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool then (if s_clean ss then ss else ck) else
      match fetch_word segs (Z_to_bv 64 (s_pc ss)) with
      | None => if s_clean ss then ss else ck
      | Some w =>
          if is_ecall w then (if s_clean ss then ss else ck) else
          match decode_any w with
          | None => if s_clean ss then ss else ck
          | Some (i, sz) =>
              if negb (Z.eqb sz 4) then (if s_clean ss then ss else ck) else
              match sym_step segs i ss scr_nil with
              | SOk ss' [] _ => sym_execS_go f false stops ss' (if s_clean ss' then ss' else ck)
              | _ => if s_clean ss then ss else ck
              end
          end
      end
  end.

Definition sym_execS (fuel : nat) (first : bool) (stops : list Z) (ss : sym_state) : sym_state :=
  sym_execS_go fuel first stops (clr ss) (clr ss).

(* [comment removed for export] *)
Fixpoint sym_execT_go (t : itab) (fuel : nat) (first : bool) (stops : list Z) (ss : sym_state) (ck : sym_state)
  : sym_state :=
  match fuel with
  | O => if s_clean ss then ss else ck
  | S f =>
      if (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool then (if s_clean ss then ss else ck) else
      match itab_lookup t (s_pc ss) with
      | None => if s_clean ss then ss else ck
      | Some i =>
          match sym_step segs i ss scr_nil with
          | SOk ss' [] _ => sym_execT_go t f false stops ss' (if s_clean ss' then ss' else ck)
          | _ => if s_clean ss then ss else ck
          end
      end
  end.

Definition sym_execT (t : itab) (fuel : nat) (first : bool) (stops : list Z) (ss : sym_state) : sym_state :=
  sym_execT_go t fuel first stops (clr ss) (clr ss).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition zf_covers (allkn : list kentry) (rb : expr) (rk : Z) (n : nat) (kb : expr) (kk : Z) (len : expr) : bool :=
  (match len with
   | ELit l0 => match rel_lit rb rk (Z.of_nat n) kb kk (l0 mod 2 ^ 64)%Z with RInside _ => true | _ => false end
   | _ => false
   end) || xinside allkn rb rk (elen n) kb kk len.

(* [comment removed for export] *)
Definition kentry_overlay (allkn : list kentry) (rb : expr) (rk : Z) (n : nat) (K : kentry) : bool :=
  match K with
  | KUnk (SA kb kk) len | KZero (SA kb kk) len | KFill (SA kb kk) len _ | KBlob (SA kb kk) len _ =>
      zf_covers allkn rb rk n kb kk len
  | _ => false
  end.

(* [comment removed for export] *)
Definition kentry_readable (allkn : list kentry) (rb : expr) (rk : Z) (n : nat) (K : kentry) : bool :=
  match K with
  | KWord (SA kb kk) w _ =>
      match rel_lit rb rk (Z.of_nat n) kb kk (Z.of_nat w) with RInside _ => true | _ => false end
  | _ => kentry_overlay allkn rb rk n K
  end.

(* [comment removed for export] *)
Fixpoint know_byte_cov (img : bool) (kn : list kentry) (rb : expr) (rk : Z) : bool :=
  match kn with
  | [] => false
  | K :: rest =>
      let lit kb kk (l : Z) := match rel_lit rb rk 1 kb kk l with RInside _ => true | _ => false end in
      (match K with
       | KWord (SA kb kk) w _ => img && lit kb kk (Z.of_nat w)
       | KZero (SA kb kk) (ELit l0) | KFill (SA kb kk) (ELit l0) _ | KBlob (SA kb kk) (ELit l0) _
       | KUnk (SA kb kk) (ELit l0) => lit kb kk (l0 mod 2 ^ 64)%Z
       | KImg lo hi =>
           img && match rb with
                  | ELit 0 => Z.leb lo rk && Z.ltb rk hi &&
                              match seg_rom segs (Z_to_bv 64 rk) with Some _ => true | None => false end
                  | _ => false
                  end
       | _ => false
       end) || know_byte_cov img rest rb rk
  end%bool.

Fixpoint know_bytes_cov (img : bool) (kn : list kentry) (rb : expr) (rk : Z) (n : nat) : bool :=
  match n with
  | O => true
  | S n' => know_byte_cov img kn rb rk && know_bytes_cov img kn rb (rk + 1) n'
  end.

Definition kn_readable (allkn kn : list kentry) (rb : expr) (rk : Z) (n : nat) : bool :=
  existsb (kentry_readable allkn rb rk n) kn || know_bytes_cov true kn rb rk n.
Definition kn_overlay (allkn kn : list kentry) (rb : expr) (rk : Z) (n : nat) : bool :=
  existsb (kentry_overlay allkn rb rk n) kn || know_bytes_cov false kn rb rk n.

(* [comment removed for export] *)
Fixpoint evars_lt (b : nat) (e : expr) : bool :=
  match e with
  | ELit _ | EBlob _ _ _ _ => true
  | EVar v => Nat.ltb v b
  | EAlu _ x y | EAluw _ x y | EMd _ x y | EMdw _ x y => evars_lt b x && evars_lt b y
  | EExt _ _ _ x => evars_lt b x
  end.

(* [comment removed for export] *)
Fixpoint find_readbase (i : nat) (scs : list sidecond) : option (saddr * nat * bool) :=
  match scs with
  | [] => None
  | SCReadBase a n sx (EVar j) :: rest => if Nat.eqb j i then Some (a, n, sx) else find_readbase i rest
  | _ :: rest => find_readbase i rest
  end.

(* [comment removed for export] *)
Definition x_dischargeable (ss ss' : sym_state) (rb : option (saddr * nat * bool)) (sc : sidecond) : bool :=
  let kn := s_know ss in
  let fk := facts_of kn in
  match sc with
  | SCReadBase a n sx (EVar j) =>
      (match rb with
       | Some (a', n', sx') => saddr_eqb a' a && Nat.eqb n' n && Bool.eqb sx' sx
       | None => false
       end)
      && Nat.eqb j (s_next ss) && Nat.ltb j (s_next ss') && evars_lt (s_next ss) (a_base a)
      && Nat.leb 1 n && Nat.leb n 8 && kn_readable fk kn (a_base a) (a_off a) n
  | SCFlat a (ELit z) =>
      Z.leb 1 z && Z.leb z 8 && kn_readable fk kn (a_base a) (a_off a) (Z.to_nat z)
  | SCStoreOk a n => Nat.leb 1 n && Nat.leb n 8 && kn_overlay fk kn (a_base a) (a_off a) n
  | _ => false
  end%bool.

Definition x_filter (ss ss' : sym_state) (scs : list sidecond) : list sidecond :=
  match scs with
  | [] => []          (* [comment removed for export] *)
  | _ => let rb := find_readbase (s_next ss) scs in
         List.filter (fun sc => negb (x_dischargeable ss ss' rb sc)) scs
  end.

(* [comment removed for export] *)
Fixpoint esize_budget (e : expr) (b : nat) {struct e} : option nat :=
  match b with
  | O => None
  | S b' =>
      match e with
      | ELit _ | EVar _ | EBlob _ _ _ _ => Some b'
      | EAlu _ x y | EAluw _ x y | EMd _ x y | EMdw _ x y =>
          match esize_budget x b' with Some b'' => esize_budget y b'' | None => None end
      | EExt _ _ _ x => esize_budget x b'
      end
  end.
Definition esize_le (e : expr) (k : nat) : bool :=
  match esize_budget e k with Some _ => true | None => false end.

(* [comment removed for export] *)
Definition rd_of (i : instr) : option reg :=
  match i with
  | Lui rd _ | Auipc rd _ | Jal rd _ | Jalr rd _ _ | Load _ _ rd _ _
  | OpImm _ rd _ _ | ShiftImm _ rd _ _ | Op _ rd _ _ | OpImm32 rd _ _ | ShiftImm32 _ rd _ _ | Op32 _ rd _ _
  | Mul _ rd _ _ | Mul32 _ rd _ _ | Lr _ _ _ rd _ | Sc _ _ _ rd _ _ | Amo _ _ _ _ rd _ _ => Some rd
  | _ => None
  end.

(* [comment removed for export] *)
Definition cap_rd (K : nat) (i : instr) (ss : sym_state) : sym_state :=
  match K with
  | O => ss
  | _ =>
      match rd_of i with
      | None => ss
      | Some rd =>
          if bv_eqb rd 0 then ss
          else if esize_le (sr_get (s_regs ss) rd) K then ss
          else SSR (s_pc ss) (sr_upd (s_regs ss) (ridx rd) (EVar (s_next ss)))
                   (s_log ss) (s_know ss) (S (s_next ss)) (s_resv ss)
      end
  end.

Definition sym_stepX (K : nat) (i : instr) (ss : sym_state) (scr : scripts) : stepres :=
  match sym_step segs i ss scr with
  | SOk ss' scs scr' =>
      if Nat.leb (s_next ss) (s_next ss')            (* [comment removed for export] *)
      then SOk (cap_rd K i ss') (x_filter ss ss' scs) scr'
      else SStop
  | SStop => SStop
  end.

(* [comment removed for export] *)
Fixpoint sym_execSX_go (K : nat) (fuel : nat) (first : bool) (stops : list Z) (ss : sym_state) (ck : sym_state)
  : sym_state :=
  match fuel with
  | O => if s_clean ss then ss else ck
  | S f =>
      if (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool then (if s_clean ss then ss else ck) else
      match fetch_word segs (Z_to_bv 64 (s_pc ss)) with
      | None => if s_clean ss then ss else ck
      | Some w =>
          if is_ecall w then (if s_clean ss then ss else ck) else
          match decode_any w with
          | None => if s_clean ss then ss else ck
          | Some (i, sz) =>
              if negb (Z.eqb sz 4) then (if s_clean ss then ss else ck) else
              match sym_stepX K i ss scr_nil with
              | SOk ss' [] _ => sym_execSX_go K f false stops ss' (if s_clean ss' then ss' else ck)
              | _ => if s_clean ss then ss else ck
              end
          end
      end
  end.

Definition sym_execSX (K : nat) (fuel : nat) (first : bool) (stops : list Z) (ss : sym_state) : sym_state :=
  sym_execSX_go K fuel first stops (clr ss) (clr ss).

Fixpoint sym_execTX_go (t : itab) (K : nat) (fuel : nat) (first : bool) (stops : list Z) (ss : sym_state) (ck : sym_state)
  : sym_state :=
  match fuel with
  | O => if s_clean ss then ss else ck
  | S f =>
      if (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool then (if s_clean ss then ss else ck) else
      match itab_lookup t (s_pc ss) with
      | None => if s_clean ss then ss else ck
      | Some i =>
          match sym_stepX K i ss scr_nil with
          | SOk ss' [] _ => sym_execTX_go t K f false stops ss' (if s_clean ss' then ss' else ck)
          | _ => if s_clean ss then ss else ck
          end
      end
  end.

Definition sym_execTX (t : itab) (K : nat) (fuel : nat) (first : bool) (stops : list Z) (ss : sym_state) : sym_state :=
  sym_execTX_go t K fuel first stops (clr ss) (clr ss).



End WithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition kcut (mk : saddr -> expr -> kentry) (kn : list kentry) (wb : expr) (wk : Z) (wn : expr)
           (kb : expr) (kk : Z) (len : expr) : list kentry :=
  let ws := mkAlu ALU_ADD wb (ELit wk) in
  let ks := mkAlu ALU_ADD kb (ELit kk) in
  (* [comment removed for export] *)
  let low :=
    if (if lin_ge0 kn [(kb, kk)] [(wb, wk)] then false   (* [comment removed for export] *)
        else if lin_ge0 kn [(wb, wk)] [(kb, kk)] then lin_ge0 kn [(kb, kk); (len, 0%Z)] [(wb, wk)] else false)
    then [mk (SA kb kk) (mkAlu ALU_SUB ws ks)] else [] in
  let high :=
    if (if lin_ge0 kn [(kb, kk); (len, 0%Z)] [(wb, wk); (wn, 0%Z)]            (* [comment removed for export] *)
        then if lin_ge0 kn [(wb, wk); (wn, 0%Z)] [(kb, kk)]                    (* [comment removed for export] *)
             then lin_ge0 kn [(ELit 0, (two64 - 1)%Z)] [(kb, kk); (len, 0%Z)]  (* [comment removed for export] *)
             else false
        else false)
    then let we := mkAlu ALU_ADD ws wn in
         let '(hb, ho) := split_lit we in
         let ha := if (lin_ge0 kn [(hb, ho)] [(wb, wk); (wn, 0%Z)] && lin_ge0 kn [(wb, wk); (wn, 0%Z)] [(hb, ho)])%bool
                   then SA hb ho else SA we 0%Z in
         [mk ha (mkAlu ALU_SUB (mkAlu ALU_ADD ks len) we)]
    else [] in
  low ++ high.

Definition kzero_cut (kn : list kentry) (wb : expr) (wk : Z) (wn : expr)
           (kb : expr) (kk : Z) (len : expr) : list kentry := kcut KZero kn wb wk wn kb kk len.
Definition kfill_cut (c : Z) (kn : list kentry) (wb : expr) (wk : Z) (wn : expr)
           (kb : expr) (kk : Z) (len : expr) : list kentry := kcut (fun a n => KFill a n c) kn wb wk wn kb kk len.
Definition kunk_cut (kn : list kentry) (wb : expr) (wk : Z) (wn : expr)
           (kb : expr) (kk : Z) (len : expr) : list kentry := kcut KUnk kn wb wk wn kb kk len.

(* [comment removed for export] *)
Definition ktrim (mk : saddr -> expr -> kentry) (kb : expr) (kk : Z) (l0 : Z) (k : Z) (w : nat) : list kentry :=
  let l := (l0 mod 2 ^ 64)%Z in
  let hi1 := Z.min k (kk + l) in
  let r1 := if Z.ltb kk hi1 then [mk (SA kb kk) (ELit (hi1 - kk))] else [] in
  let lo2 := Z.max kk (k + Z.of_nat w) in
  let r2 := if Z.ltb lo2 (kk + l) then [mk (SA kb lo2) (ELit (kk + l - lo2))] else [] in
  r1 ++ r2.

(* [comment removed for export] *)
Definition kword_cut (kb : expr) (kk : Z) (w' : nat) (v : expr) (k : Z) (w : nat) : list kentry :=
  match v with
  | ELit _ =>
      let n1 := (k - kk)%Z in                                (* [comment removed for export] *)
      let r1 := if Z.ltb 0 n1 then [KWord (SA kb kk) (Z.to_nat n1) (mkExt false 0 (Z.to_nat n1) v)] else [] in
      let d := (k + Z.of_nat w - kk)%Z in                    (* [comment removed for export] *)
      let r2 := if Z.ltb d (Z.of_nat w')
                then [KWord (SA kb (kk + d)) (w' - Z.to_nat d) (mkExt false (Z.to_nat d) (w' - Z.to_nat d) v)]
                else [] in
      r1 ++ r2
  | _ => []
  end.

(* [comment removed for export] *)
Definition prune_zf (mk : saddr -> expr -> kentry) (allkn : list kentry) (wb : expr) (k : Z) (w : nat)
           (K : kentry) (kb : expr) (kk : Z) (len : expr) (apart : unit -> bool) (hints : list bool)
           (diffbase : unit -> list kentry * list sidecond * list bool)
  : list kentry * list sidecond * list bool :=
  (* [comment removed for export] *)
  if expr_eqb kb wb then
    match len with
    | ELit l0 => (ktrim mk kb kk l0 k w, [], hints)
    | _ => if Z.leb (k + Z.of_nat w) kk then ([K], [], hints)
           else (kcut mk allkn wb k (elen w) kb kk len, [], hints)
    end
  else if apart tt then ([K], [], hints)
  else match kcut mk allkn wb k (elen w) kb kk len with
       | [] => diffbase tt
       | cut => (cut, [], hints)
       end.

Definition prune1 (allkn : list kentry) (wa : saddr) (w : nat) (wv : expr) (K : kentry) (hints : list bool)
  : list kentry * list sidecond * list bool :=
  let k := a_off wa in
  let diffbase (ka : saddr) (kl : expr) :=
    let apart := ranges_apart_x allkn (a_base wa) k (elen w) (a_base ka) (a_off ka) kl in
    if apart then ([K], [], hints) else
    match hints with
    | true :: hs => ([K], [SCDisj wa (elen w) ka kl], hs)   (* [comment removed for export] *)
    | false :: hs => ([], [], hs)                          (* [comment removed for export] *)
    | [] => ([], [], [])                                   (* [comment removed for export] *)
    end in
  match K with
  | KAlign _ _ => ([K], [], hints)
  | KRange _ _ _ => ([K], [], hints)
  | KWr _ _ => ([K], [], hints)
  | KDisj _ _ _ _ => ([K], [], hints)
  | KImg lo hi =>
      match a_base wa with
      | ELit 0 =>
          let r1 := if Z.ltb lo (Z.min k hi) then [KImg lo (Z.min k hi)] else [] in
          let lo2 := Z.max lo (k + Z.of_nat w) in
          let r2 := if Z.ltb lo2 hi then [KImg lo2 hi] else [] in
          (r1 ++ r2, [], hints)
      | _ => if Z.ltb (hi - lo) (2 ^ 64) then diffbase (SA (ELit 0) lo) (ELit (hi - lo))
             else ([], [], hints)
      end
  | KZero (SA kb kk) len =>
      prune_zf KZero allkn (a_base wa) k w K kb kk len
               (fun _ => ranges_apart_x allkn (a_base wa) k (elen w) kb kk len) hints (fun _ => diffbase (SA kb kk) len)
  | KFill (SA kb kk) len c =>
      prune_zf (fun a n => KFill a n c) allkn (a_base wa) k w K kb kk len
               (fun _ => ranges_apart_x allkn (a_base wa) k (elen w) kb kk len) hints (fun _ => diffbase (SA kb kk) len)
  | KUnk (SA kb kk) len =>
      prune_zf KUnk allkn (a_base wa) k w K kb kk len
               (fun _ => ranges_apart_x allkn (a_base wa) k (elen w) kb kk len) hints (fun _ => diffbase (SA kb kk) len)
  | KWord (SA kb kk) w' v =>
      if expr_eqb kb (a_base wa) then
        (if (Z.leb (kk + Z.of_nat w') k || Z.leb (k + Z.of_nat w) kk)%bool
         then ([K], [], hints) else (kword_cut kb kk w' v k w, [], hints))   (* [comment removed for export] *)
      else if ranges_apart_x allkn (a_base wa) k (elen w) kb kk (elen w') then ([K], [], hints)
      else if (Nat.eqb w 1 && Nat.eqb w' 1 && expr_eqb wv v)%bool
      then ([K], [], hints)   (* [comment removed for export] *)
      else diffbase (SA kb kk) (elen w')
  | KBlob (SA kb kk) len bk =>
      if expr_eqb kb (a_base wa) then
        match len with
        | ELit l0 =>
            let l := (l0 mod 2 ^ 64)%Z in
            (if (Z.leb (kk + l) k || Z.leb (k + Z.of_nat w) kk)%bool
             then ([K], [], hints) else ([], [], hints))
        | _ => if Z.leb (k + Z.of_nat w) kk then ([K], [], hints) else ([], [], hints)
        end
      else diffbase (SA kb kk) len
  end.

Fixpoint prune (allkn : list kentry) (wa : saddr) (w : nat) (wv : expr) (kn : list kentry) (hints : list bool)
  : list kentry * list sidecond * list bool :=
  match kn with
  | [] => ([], [], hints)
  | K :: rest =>
      let '(kept, scs1, hs1) := prune1 allkn wa w wv K hints in
      let '(r, scs2, hs2) := prune allkn wa w wv rest hs1 in
      (kept ++ r, scs1 ++ scs2, hs2)
  end.

(* [comment removed for export] *)
Definition prune1p (allkn : list kentry) (sp : sprep) (wa : saddr) (w : nat) (wv : expr) (K : kentry) (hints : list bool)
  : list kentry * list sidecond * list bool :=
  let k := a_off wa in
  let diffbase (ka : saddr) (kl : expr) :=
    let apart := ranges_apart_p allkn sp (a_base wa) k (elen w) (a_base ka) (a_off ka) kl in
    if apart then ([K], [], hints) else
    match hints with
    | true :: hs => ([K], [SCDisj wa (elen w) ka kl], hs)   (* [comment removed for export] *)
    | false :: hs => ([], [], hs)                          (* [comment removed for export] *)
    | [] => ([], [], [])                                   (* [comment removed for export] *)
    end in
  match K with
  | KAlign _ _ => ([K], [], hints)
  | KRange _ _ _ => ([K], [], hints)
  | KWr _ _ => ([K], [], hints)
  | KDisj _ _ _ _ => ([K], [], hints)
  | KImg lo hi =>
      match a_base wa with
      | ELit 0 =>
          let r1 := if Z.ltb lo (Z.min k hi) then [KImg lo (Z.min k hi)] else [] in
          let lo2 := Z.max lo (k + Z.of_nat w) in
          let r2 := if Z.ltb lo2 hi then [KImg lo2 hi] else [] in
          (r1 ++ r2, [], hints)
      | _ => if Z.ltb (hi - lo) (2 ^ 64) then diffbase (SA (ELit 0) lo) (ELit (hi - lo))
             else ([], [], hints)
      end
  | KZero (SA kb kk) len =>
      prune_zf KZero allkn (a_base wa) k w K kb kk len
               (fun _ => ranges_apart_p allkn sp (a_base wa) k (elen w) kb kk len) hints (fun _ => diffbase (SA kb kk) len)
  | KFill (SA kb kk) len c =>
      prune_zf (fun a n => KFill a n c) allkn (a_base wa) k w K kb kk len
               (fun _ => ranges_apart_p allkn sp (a_base wa) k (elen w) kb kk len) hints (fun _ => diffbase (SA kb kk) len)
  | KUnk (SA kb kk) len =>
      prune_zf KUnk allkn (a_base wa) k w K kb kk len
               (fun _ => ranges_apart_p allkn sp (a_base wa) k (elen w) kb kk len) hints (fun _ => diffbase (SA kb kk) len)
  | KWord (SA kb kk) w' v =>
      if expr_eqb kb (a_base wa) then
        (if (Z.leb (kk + Z.of_nat w') k || Z.leb (k + Z.of_nat w) kk)%bool
         then ([K], [], hints) else (kword_cut kb kk w' v k w, [], hints))   (* [comment removed for export] *)
      else if ranges_apart_p allkn sp (a_base wa) k (elen w) kb kk (elen w') then ([K], [], hints)
      else if (Nat.eqb w 1 && Nat.eqb w' 1 && expr_eqb wv v)%bool
      then ([K], [], hints)   (* [comment removed for export] *)
      else diffbase (SA kb kk) (elen w')
  | KBlob (SA kb kk) len bk =>
      if expr_eqb kb (a_base wa) then
        match len with
        | ELit l0 =>
            let l := (l0 mod 2 ^ 64)%Z in
            (if (Z.leb (kk + l) k || Z.leb (k + Z.of_nat w) kk)%bool
             then ([K], [], hints) else ([], [], hints))
        | _ => if Z.leb (k + Z.of_nat w) kk then ([K], [], hints) else ([], [], hints)
        end
      else diffbase (SA kb kk) len
  end.

Fixpoint prunep (allkn : list kentry) (sp : sprep) (wa : saddr) (w : nat) (wv : expr) (kn : list kentry) (hints : list bool)
  : list kentry * list sidecond * list bool :=
  match kn with
  | [] => ([], [], hints)
  | K :: rest =>
      let '(kept, scs1, hs1) := prune1p allkn sp wa w wv K hints in
      let '(r, scs2, hs2) := prunep allkn sp wa w wv rest hs1 in
      (kept ++ r, scs1 ++ scs2, hs2)
  end.

(* [comment removed for export] *)
Definition ranges_apart_pc (kn : list kentry) (sp : sprep) (b1 : expr) (k1 : Z) (n1 : expr)
           (br2 : option (Z * Z)) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match n1, n2 with
  | ELit z1, ELit z2 =>
      let m1 := zlit64 z1 in let m2 := zlit64 z2 in
      if (match sp_rng sp, br2 with
          | Some (lo1, hi1), Some (lo2, hi2) =>
              (Z.leb (hi1 + k1 + m1) (lo2 + k2) || Z.leb (hi2 + k2 + m2) (lo1 + k1))%bool
          | _, _ => false
          end) then true
      else if in_sides kn (sp_D sp) b2 k2 m2 then true
      else lin_apart kn b1 k1 m1 b2 k2 m2
  | _, _ =>
    if (match sp_rng sp, br2, sp_h1 sp, xhi kn n2 with
        | Some (lo1, hi1), Some (lo2, hi2), Some h1, Some h2 =>
            if (Z.leb (hi1 + k1 + h1) (lo2 + k2) || Z.leb (hi2 + k2 + h2) (lo1 + k1))%bool then true
            else (* [comment removed for export] *)
            if match end_hi kn b1 k1 n1 lo1 hi1 h1 with Some e1 => Z.leb e1 (lo2 + k2) | None => false end then true
            else match end_hi kn b2 k2 n2 lo2 hi2 h2 with Some e2 => Z.leb e2 (lo1 + k1) | None => false end
        | _, _, _, _ => false
        end) then true
    else if in_sides_x kn (sp_Dx sp) b2 k2 n2 then true
    else if negb (shares_var b1 b2) then false
    else if lin_ge0 kn [(b2, k2)] [(b1, k1); (n1, 0%Z)] then true
    else lin_ge0 kn [(b1, k1)] [(b2, k2); (n2, 0%Z)]
  end.

(* [comment removed for export] *)
Definition kbase (K : kentry) : option expr :=
  match K with
  | KZero (SA kb _) _ | KWord (SA kb _) _ _ | KBlob (SA kb _) _ _ | KFill (SA kb _) _ _ | KUnk (SA kb _) _ => Some kb
  | _ => None
  end.

(* [comment removed for export] *)
Definition prune1pc (allkn : list kentry) (sp : sprep) (wa : saddr) (w : nat) (wv : expr) (K : kentry) (hints : list bool)
  (br2 : option (Z * Z)) : list kentry * list sidecond * list bool :=
  let k := a_off wa in
  let diffbase (ka : saddr) (kl : expr) :=
    let apart := ranges_apart_pc allkn sp (a_base wa) k (elen w) br2 (a_base ka) (a_off ka) kl in
    if apart then ([K], [], hints) else
    match hints with
    | true :: hs => ([K], [SCDisj wa (elen w) ka kl], hs)
    | false :: hs => ([], [], hs)
    | [] => ([], [], [])
    end in
  match K with
  | KAlign _ _ | KRange _ _ _ | KWr _ _ | KDisj _ _ _ _ | KImg _ _ => prune1p allkn sp wa w wv K hints
  | KZero (SA kb kk) len =>
      if expr_eqb kb (a_base wa) then prune1p allkn sp wa w wv K hints
      else if ranges_apart_pc allkn sp (a_base wa) k (elen w) br2 kb kk len then ([K], [], hints)
      else match kzero_cut allkn (a_base wa) k (elen w) kb kk len with
           | [] => diffbase (SA kb kk) len
           | cut => (cut, [], hints)
           end
  | KFill (SA kb kk) len c =>
      if expr_eqb kb (a_base wa) then prune1p allkn sp wa w wv K hints
      else if ranges_apart_pc allkn sp (a_base wa) k (elen w) br2 kb kk len then ([K], [], hints)
      else match kfill_cut c allkn (a_base wa) k (elen w) kb kk len with
           | [] => diffbase (SA kb kk) len
           | cut => (cut, [], hints)
           end
  | KUnk (SA kb kk) len =>
      if expr_eqb kb (a_base wa) then prune1p allkn sp wa w wv K hints
      else if ranges_apart_pc allkn sp (a_base wa) k (elen w) br2 kb kk len then ([K], [], hints)
      else match kunk_cut allkn (a_base wa) k (elen w) kb kk len with
           | [] => diffbase (SA kb kk) len
           | cut => (cut, [], hints)
           end
  | KWord (SA kb kk) w' v =>
      if expr_eqb kb (a_base wa) then prune1p allkn sp wa w wv K hints
      else if ranges_apart_pc allkn sp (a_base wa) k (elen w) br2 kb kk (elen w') then ([K], [], hints)
      else if (Nat.eqb w 1 && Nat.eqb w' 1 && expr_eqb wv v)%bool
      then ([K], [], hints)
      else diffbase (SA kb kk) (elen w')
  | KBlob (SA kb kk) len bk =>
      if expr_eqb kb (a_base wa) then prune1p allkn sp wa w wv K hints
      else diffbase (SA kb kk) len
  end.

Fixpoint br_lookup (c : list (expr * option (Z * Z))) (b : expr) : option (option (Z * Z)) :=
  match c with
  | [] => None
  | (b', r) :: rest => if expr_eqb b b' then Some r else br_lookup rest b
  end.

Fixpoint prunepc (allkn : list kentry) (sp : sprep) (wa : saddr) (w : nat) (wv : expr) (kn : list kentry) (hints : list bool)
  (cache : list (expr * option (Z * Z))) : list kentry * list sidecond * list bool :=
  match kn with
  | [] => ([], [], hints)
  | K :: rest =>
      let '(br2, cache') :=
        match kbase K with
        | Some kb => match br_lookup cache kb with
                     | Some r => (r, cache)
                     | None => let r := base_range allkn kb in (r, (kb, r) :: cache)
                     end
        | None => (None, cache)
        end in
      let '(kept, scs1, hs1) := prune1pc allkn sp wa w wv K hints br2 in
      let '(r, scs2, hs2) := prunepc allkn sp wa w wv rest hs1 cache' in
      (kept ++ r, scs1 ++ scs2, hs2)
  end.

(* [comment removed for export] *)
Fixpoint carry (log : list sentry) (kn : list kentry) (hints : list bool)
  : list kentry * list sidecond * list bool :=
  match log with
  | [] => (kn, [], hints)
  | SE a w v :: older =>
      let '(kn1, scs1, hs1) := carry older kn hints in
      let fk := facts_of kn1 in
      let '(kn2, scs2, hs2) := prunepc fk (mk_sprep fk (a_base a) (a_off a) (elen w)) a w v kn1 hs1 [] in   (* [comment removed for export] *)
      (KWord a w v :: kn2, scs1 ++ scs2, hs2)
  end.




End AX2.
