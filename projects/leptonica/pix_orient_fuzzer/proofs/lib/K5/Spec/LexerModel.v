(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import String Ascii ZArith Bool List Lia.
(* [comment removed for export] *)
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Spec Require Import Prelim.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_LexerModel () := "i69OSSVerify5KrLib2K54Spec:LexerModel:target_ops00C1?~~~~~~~~~~~~~~~k69OSSVerify5KrLib2K54Spec:LexerModel:target_ops01C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00c69OSSVerify5KrLib2K54Spec:LexerModel8memchr_nC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z6of_natC69OSSVerify5KrLib2K54Spec6Prelim4znthC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00K47Corelib4Init9Datatypes6option02C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic9False_indK47Corelib4Init9Datatypes3nat02C56Stdlib6ZArith6BinInt1Z8eqb_specC56Stdlib6ZArith6BinInt1Z3eqbI47Corelib4Init9Datatypes7reflect00K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2ltC47Corelib4Init5Logic7f_equalC56Stdlib6ZArith6BinInt1Z2leC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K47Corelib7Numbers7BinNums8positive02K46Stdlib9micromega7EnvRing5PExpr02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revK47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega5Tauto8GFormula03K47Corelib4Init5Logic3and01C47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z6eq_decI47Corelib4Init6Specif7sumbool00C47Corelib4Init5Logic8eq_ind_rK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula07C47Corelib4Init9Datatypes7nat_indK47Corelib4Init9Datatypes6option01C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z8inj_succK46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init9Datatypes3nat01I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01I47Corelib4Init9Datatypes4bool00K47Corelib7Numbers7BinNums8positive03C46Stdlib9micromega8ZifyInst7Inj_Z_ZK47Corelib7Numbers7BinNums1Z01I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega=RingMicromega3Op201C46Stdlib9micromega;ZifyClasses7rew_iffc69OSSVerify5KrLib2K54Spec:LexerModel6memchrC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natc69OSSVerify5KrLib2K54Spec:LexerModel=memchr_n_someC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00C56Stdlib6ZArith4Znat5Z2Nat2idC46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqc69OSSVerify5KrLib2K54Spec:LexerModel=memchr_n_noneC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K54Spec:LexerModel:skip_fwd_nC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4negbc69OSSVerify5KrLib2K54Spec:LexerModel8is_spaceC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4andbK47Corelib4Init9Datatypes4bool02C56Stdlib6ZArith6BinInt1Z3subK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega7EnvRing5PExpr04K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02K46Stdlib9micromega:ZMicromega;ZArithProof01c69OSSVerify5KrLib2K54Spec:LexerModelAskip_fwd_n_boundsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K54Spec:LexerModel8skip_fwdC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula06c69OSSVerify5KrLib2K54Spec:LexerModel?skip_fwd_n_exitC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K54Spec:LexerModel;skip_back_nC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K54Spec:LexerModelBskip_back_n_boundsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K54Spec:LexerModel9skip_backC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K54Spec:LexerModel@skip_back_n_exitC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K54Spec:LexerModel9strnstr_nC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54Spec6Prelim7zlengthC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8ltb_specC56Stdlib6ZArith6BinInt1Z3ltbI47Corelib4Init9Datatypes8BoolSpec00c69OSSVerify5KrLib2K54Spec:LexerModel;strncmp_litC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K54Spec:LexerModel<PEM_END_RESTC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K54Spec:LexerModel;strnstr_endC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K54Spec:LexerModel>strnstr_n_someC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K54Spec:LexerModel:count_nl_nC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K54Spec:LexerModel;memchr_someC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K54Spec:LexerModelAcount_nl_n_boundsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K54Spec:LexerModel8count_nlC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K54Spec:LexerModel6LexRun5tbindC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K54Spec:LexerModel;clear_stateC1?~~~~~~~~~~~~~~~i69OSSVerify5KrLib2K54Spec:LexerModel5token00C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K54Spec:LexerModel;next_resultC1?~~~~~~~~~~~~~~~i79OSSVerify5KrLib2K54Spec:LexerModel6LexRun5ttree00C1?~~~~~~~~~~~~~~~k69OSSVerify5KrLib2K54Spec:LexerModel6tevent01C1?~~~~~~~~~~~~~~~k69OSSVerify5KrLib2K54Spec:LexerModel6tevent02C1?~~~~~~~~~~~~~~~k69OSSVerify5KrLib2K54Spec:LexerModel6tevent04C1?~~~~~~~~~~~~~~~k69OSSVerify5KrLib2K54Spec:LexerModel6tevent06C1?~~~~~~~~~~~~~~~K46Stdlib7Strings5Ascii5ascii01K46Stdlib7Strings6String6string02C69OSSVerify5KrLib2K54Spec6Prelim3strC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appc79OSSVerify5KrLib2K54Spec:LexerModel6LexRun=target_eventsC1?~~~~~~~~~~~~~~~i69OSSVerify5KrLib2K54Spec:LexerModel6tevent00C1?~~~~~~~~~~~~~~~K46Stdlib7Strings6String6string01k69OSSVerify5KrLib2K54Spec:LexerModel6tevent03C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K54Spec:LexerModel<precond_textC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K54Spec:LexerModel=EXPR_FILENAMEC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K54Spec:LexerModel9FUNC_INITC1?~~~~~~~~~~~~~~~k69OSSVerify5KrLib2K54Spec:LexerModel6tevent05C1?~~~~~~~~~~~~~~~".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Fixpoint list_Zeqb (l1 l2 : list Z) : bool :=
  match l1, l2 with
  | [], [] => true
  | x :: l1', y :: l2' => (x =? y) && list_Zeqb l1' l2'
  | _, _ => false
  end.

(* [comment removed for export] *)
Fixpoint dec_digits_n (fuel : nat) (n : Z) (acc : list Z) : list Z :=
  match fuel with
  | O => acc
  | S f => if n <? 10 then (48 + n) :: acc
           else dec_digits_n f (n / 10) ((48 + n mod 10) :: acc)
  end.
Definition Zdecimal (n : Z) : list Z := dec_digits_n 64 n [].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition P11_MESSAGE_MAX : Z := 512.
Definition PEM_BEGIN : list Z := str "-----BEGIN ".          (* [comment removed for export] *)
Definition PEM_END_REST : list Z := str "-----END ".         (* [comment removed for export] *)
Definition FUZZ_INPUT : list Z := str "fuzz-input".         (* [comment removed for export] *)
Definition NULL_STR : list Z := str "(null)".               (* [comment removed for export] *)
Definition MSG_PEM : list Z := str "invalid pem block: no ending line".
Definition MSG_SECTION : list Z := str "invalid section header: missing braces".
Definition MSG_FIELD : list Z := str "invalid field line: no colon".
Definition FUNC_INIT : list Z := str "p11_lexer_init".
Definition FUNC_NEXT : list Z := str "p11_lexer_next".
Definition EXPR_FILENAME : list Z := str "lexer->filename != NULL".
Definition EXPR_SECTION : list Z := str "lexer->tok.section.name != NULL".
Definition EXPR_FIELD : list Z := str "lexer->tok.field.name != NULL".

(* [comment removed for export] *)
Definition precond_text (expr func : list Z) : list Z :=
  str "p11-kit: '" ++ expr ++ str "' not true at " ++ func ++ [10].
(* [comment removed for export] *)
Definition reached_text (func : list Z) : list Z :=
  str "p11-kit: shouldn't be reached at " ++ func ++ [10].

(* [comment removed for export] *)
Definition message_store_bytes (text : list Z) : list Z :=
  if zlength text <=? P11_MESSAGE_MAX - 2
  then text ++ [0]
  else ztake (P11_MESSAGE_MAX - 2) text ++ [0; 0].

(* [comment removed for export] *)
Definition is_space (c : Z) : bool := (c =? 32) || ((9 <=? c) && (c <=? 13)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive tevent : Type :=
| TMalloc (n : Z) (r : option nat)
| TFree (p : option nat)
| TStderr (bytes : list Z)
| TStdout (bytes : list Z)
| TMsgStore (bytes : list Z)
| TReturn (rc : Z)
| TUnreachable.

(* [comment removed for export] *)
Record target_ops (M : Type -> Type) (ptr : Type) : Type := mkOps {
  ret : forall A : Type, A -> M A;
  bind : forall A B : Type, M A -> (A -> M B) -> M B;
  unreachable : forall A : Type, M A;        (* [comment removed for export] *)
  lib_malloc : Z -> M (option ptr);          (* [comment removed for export] *)
  lib_free : option ptr -> M unit;           (* [comment removed for export] *)
  out_stderr : list Z -> M unit;             (* [comment removed for export] *)
  out_stdout : list Z -> M unit;             (* [comment removed for export] *)
  msg_store : list Z -> M unit               (* [comment removed for export] *)
}.
Arguments mkOps {M ptr}.
Arguments ret {M ptr} _ {A}.
Arguments bind {M ptr} _ {A B}.
Arguments unreachable {M ptr} _ {A}.
Arguments lib_malloc {M ptr}.
Arguments lib_free {M ptr}.
Arguments out_stderr {M ptr}.
Arguments out_stdout {M ptr}.
Arguments msg_store {M ptr}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Bytes.
Variable d : list Z.

(* [comment removed for export] *)
Fixpoint memchr_n (n : nat) (pos c : Z) : option Z :=
  match n with
  | O => None
  | S n' => if znth d pos =? c then Some pos else memchr_n n' (pos + 1) c
  end.
Definition memchr (pos c n : Z) : option Z := memchr_n (Z.to_nat n) pos c.

(* [comment removed for export] *)
Definition strncmp_lit (pos : Z) (lit : list Z) : bool :=
  list_Zeqb (ztake (zlength lit) (zdrop pos d)) lit.

(* [comment removed for export] *)
Fixpoint strnstr_n (fuel : nat) (s slen : Z) : option Z :=
  match fuel with
  | O => None
  | S f =>
      if slen <? 1 then None
      else let sc := znth d s in
           if sc =? 0 then None
           else if negb (sc =? 10) then strnstr_n f (s + 1) (slen - 1)
           else if slen - 1 <? zlength PEM_END_REST then None
           else if strncmp_lit (s + 1) PEM_END_REST then Some s
           else strnstr_n f (s + 1) (slen - 1)
  end.
Definition strnstr_end (s slen : Z) : option Z := strnstr_n (S (Z.to_nat slen)) s slen.

(* [comment removed for export] *)
Fixpoint skip_fwd_n (fuel : nat) (p e : Z) : Z :=
  match fuel with
  | O => p
  | S f => if negb (p =? e) && is_space (znth d p) then skip_fwd_n f (p + 1) e else p
  end.
Definition skip_fwd (p e : Z) : Z := skip_fwd_n (Z.to_nat (e - p)) p e.

(* [comment removed for export] *)
Fixpoint skip_back_n (fuel : nat) (p e : Z) : Z :=
  match fuel with
  | O => e
  | S f => if negb (p =? e) && is_space (znth d (e - 1)) then skip_back_n f p (e - 1) else e
  end.
Definition skip_back (p e : Z) : Z := skip_back_n (Z.to_nat (e - p)) p e.

(* [comment removed for export] *)
Fixpoint count_nl_n (fuel : nat) (pos e line : Z) : Z :=
  match fuel with
  | O => line
  | S f =>
      if pos <? e then
        match memchr pos 10 (e - pos) with
        | None => line
        | Some p => count_nl_n f (p + 1) e (line + 1)
        end
      else line
  end.
Definition count_nl (pos e line : Z) : Z := count_nl_n (Z.to_nat (e - pos)) pos e line.

(* [comment removed for export] *)
Fixpoint cstr (l : list Z) : list Z :=
  match l with
  | [] => []
  | c :: l' => if c =? 0 then [] else c :: cstr l'
  end.

(* [comment removed for export] *)
Definition strndup_bytes (p n : Z) : list Z :=
  let s := cstr (ztake n (zdrop p d)) in
  s ++ repeat 0 (Z.to_nat (n + 1 - zlength s)).

End Bytes.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section BytesFacts.
Variable d : list Z.

Lemma memchr_n_some : forall n pos c p,
  memchr_n d n pos c = Some p ->
  pos <= p < pos + Z.of_nat n /\ znth d p = c /\
  (forall q, pos <= q < p -> znth d q <> c).
Proof.
ltac2:(KReplay.run1 (kr_t_LexerModel ()) ["BytesFacts"] "p'0h01qh14__x1h24__x2h31Hh42Hqh57__arithh64__ffh78__varmaph85__with94__x3h:1ni001nh;1ph<1xh=2H0h>1ch?5cstr0h@1ei011ehA3poshB2IHhC4__p1hD1AhE1BhF1ChG1EhH2NEhI1bi021bhJ1mhK2n0hL1ri031rhM1si041shN1yi051oi061zp;1p;4p;3p;2p;6p;7p;<p;Bp;8p-1p10000R0p60620003R1p8P0p60621001P1p8p10014R0p6064110003P1p8P0p60651110002P1p8P0p606611101001P1p8P0p606611110000P1p8g0028R1j1{Tg002Zj4KTg003Zj38Tg0044R0j12Tg004Tj2=Tg005LR2j20Tg005gj1QTg006Ij6PTg006ej2zTg007DR3j1@Tg007cj2uTg008Ej2[Tg008bR4j2qTg009Ej1jTg009cR5j21Tg00:@R6j29Tg00:\j6dTg00;9j26Tg00;Uj1NTg00<3j4aTg00<Vj6RTg00=?j1LTg00=dj1`Tg00>Dj1_Tg00>dj2MTg00?Bj1^Tg00?`j4GTg00@>j1yTg00@\j1xTg00AGj2]Tg00Ajj1\Tg00BOj2FTg00C2j2pTg00CTj2ZTg00Cnj2oTg00DZj3mTg00E9j4lTg00Ekj4YTg00FVj1XTg00G;j6iTg00G_j4JTg00H:j1CTg00HSj2hTg00I3R7j2kTg00ISj7gTg00J1j4OTg00J\j6nTg00K@j4fTg00Kaj2eTg00LCl<WTg00LhlBrTg00MNl<sTg00N3j7tTg00NWj3cTg00O:j7vTg00O^j8wTg00PBR8f0R9'ep=Af4R:f3R;'6f2R<f1R=/19'9'0p=:A88=9p=416;<19=9'0p=5A88=9#Cp=31=<==889p=;16<=/09p=I%29,1=p=b19=9,0<p=H1Z89p=<g00P`R>P>P8P8P3P0P0P;g00Q?P<P=P9M<Wp=VP>P8P8P8P0P0f5R0P:P;P<P=P9M<Wp=UP8P8P8P8P8P8P5P9P=P<P5P;P:P0f6R5f7R3f8R?f9R@MBrp=TP8P8P6P3P6P5P0P:P;P<P=P9M<sp=SP8P=g00QcP9COp=EP=g00RJR6g00RiRAPAg00SIRBP9g00SiFtp=7Ac8=9p=>P8P=g00TIP9COp=DP<P6PAPAPBP=P9Fvp=?P;P6PAPAPBP<P=P9Gwp=B%{8RCp,1dRDP;P<P=CK%A9RE38P;P=P=P;%2:D:1=D=RF/4<P:P9P9P<C513F:[^08'0'0[^;8^>8^A8RGX:>PDg00U0RHP<P=CK=8CEPC%Q8P1P8p-0RIP9g00UORJg00Uln10110500021000000X@Cg00VH%A=P9EPPJP:P<P<P:%2HD:1=D<RH/4;P0P9P9P;C513F0[^08'0'0/z9b=W3X;8X>8XA8PD%@:P<P=CK=8CE1=D;RE/u<14E<1[E<'q1=D:/[;g00VdRKP4A;D0:PKPCP=%A3R4PDP@g00WDRL#jRM,13P5CKRNn0100000020000%A0RO58CP?P5P5P?f:RP#@#2D:1=D5RQ/43RR1993RS9I@913F@RT[^08'0'0]3P=14Q0RQA8C4OPCP8P1P8P8P9P9P@n10110500021010600X@C%A?%A5P9Ed14?514@3P8PPf;R1/69R4f=RU#@,b17H9A;D9Pf<RVP9P9P=C513FV[^08'0'0X;816PPRW%@VRX#2RY,1PRZ,9PR['0R\1=DPR]/4@R^1991R_,04R`13F1Ra[^08Rb'0P\%2VR\/1MRc,1PRd,9PRe,0WPWP[PWPe%NWP9X<8RW19=9Re#NXN8X<8R[PPPP%<PRfPZPdPWPWPWP8P8g00Wi11=9Ca#<XJ8X:8RdPPPPPfPYPcPWPW%29#<X<>RYPXPc119MRcX<8RXPVP\%<\CVEUM:TGSER%LVg00XMRf/6\g00XkR\#`Rg%_\R\P81M8<RhP=%^8RiCG%y8Rj%x8Rk1]8f%\LRl,F8Rm'E,7k%QARn1F8LRo/Eo,7k1]8MRp,>m,>o,Do,7k5?kCB1pkBRqP9P<g00YWRr,ZK1o9<=8KrdAm8f=ClRrb6b7b8X18X2816f=P=P=P=P=11<MRKD:[^18^28P9f>Rs#2PVP=O3b5b?CYP^PbP;PgP\P8P81M8=P<PiCGP<P8PhP<PiCGCGPjPk%\l,F8Ri%Xl,F8Rl'E,7k1Dli,7k5?kPnPkP6PAPAPBP:EiCBPqPrb6b7b8X18X28XCIAI9=eP;[^18^28^CIP913HVP<PUP=O4b5X4`X08CJCJP?P9EPW3P9O1b=W3WGP9O1%CQA8CNOP@11?MROP3P5P9O4POP5P5PO%2PD:11@MRO?I9SPT[^08,0R'0P2POP3P3PO%21D:A;D3?11PMP9P9P?C513FP[^08'0PPP?P?PZC5A;D?@AH49@Pa[^08'0'0P9111MRaP@P@Pa%2UD:14]111UM?I9_13FU[^08'0P2A;D1V11sMP9P9PVC513Fs[^08PsPVPVPsf@R1#@#2D:A;DVUf?RVP9P9PUC513FV[^08'0'0P9A;DUsfARs/1MP9P9PVC513Fs[^0816sVRUfCR2#@R_#2R],1sRa,9VR@'0R4A;DV1RDfBR?P9P9P1C5RZ13F?[^08R?'0P4%22R4/1MRP,1sRO,9VRR,0UPUP@PUPR%NUPWP[PVPV%<VPaPOPWPWPWPdPsPs%<sP]PPPWPWPYP_PPPXP2P4%<4CVEUM:TGSER%L216f4PgP\P8PhP=1M8;CGRhPjPk1>opR4/Em,7kRX%XL,F8RL,>4,Dm,7k5?kPn1Eom,7kR41>Lp,>o,Dm,7k5?kCBPqPrb6b7b8X18X28X98PcP=P=PcP<D:16=<Rc11;M,1=7H<[^18^28^98P9fERM#2PsP2P3O4b5b?CYPDP?P=1h=214=2R2%C2'kP7fDR7,4<R2%C213E7P914;MREP8fFR2fGR?P9P9PMC513F?]4X08P2P2P2P7C5P1W4P:P9P;FgW@P9O1%CEP0P:fHRE#L%2E,6fPgP\PhPjPkPkP6PAPAPBP8Pmg00Z7PoCO,7kEnPnPk1DmL,7kRL9?k4PnA?kXLCBCBPqPrb6b7b8X18X28X9814=9PJ[AHc<;PKP;P;P:C5[[^18^28^98P9P2P5PEP<P0O5b5b?O2WKP9O1n200110400021010111100bMX4ZX08CJCJWFWEP=P9O2n2001000000121000000W=WDP=P9O2n2001000000121000000bBW3WHP9O1n10210210300021110111100P<O1bIbLW3X;8X>8XA8XBGX:>P9CfX:>o"). Qed.

Lemma memchr_n_none : forall n pos c,
  memchr_n d n pos c = None -> forall q, pos <= q < pos + Z.of_nat n -> znth d q <> c.
Proof.
ltac2:(KReplay.run1 (kr_t_LexerModel ()) ["BytesFacts"] "p'0h01Hh12Hqh24__x1h34__x2h41ni001nh51qh61xh71ch83posh93Hq0h:7__arithh;4__ffh<4__p1h=8__varmaph>5__with?4__x3h@1ei011ehA1EhB2H0hC2H1hD2IHhE2NEhF1bi021bhG5cstr0hH1mhI2n0hJ1ri031rhK1si041shL1yi051op;1p;4p;3p;2p;6p;7p;<p;Bp;8g0028R0j1sTg002Zj4<Tg005gj1LTg003Zj35Tg00;9j26Tg0044R1j14Tg004Tj2:Tg00H:j13Tg009cR2j21Tg00:@R3j27Tg005Lj2=Tg00;Uj1ITg00<3j4jTg00CTj2GTg00<Vj6MTg00Z^j4RTg00=dj1ZTg00>Dj1XTg00>dj2DTg00?Bj1WTg00?`j4CTg00@>j1VTg00@\j1UTg00FVj1TTg00BOj2?Tg00Ajj1KTg00AGj2JTg00NWj3;Tg00G;j6STg00C2j2rTg00Cnj2qTg00DZj3pTg00E9j4oTg007DR4j1>Tg007cj2nTg008Ej2QTg008bR5j2iTg00Kaj2NTg009Ej1hTg006Ij6gTg006ej2fTg00HSj2bTg00I3R6j2`Tg00ISj7_Tg00=?j1^Tg00J1j4FTg00J\j6]Tg00K@j4\Tg00LCl<HTg00LhlBkTg00MNl<[Tg00N3j7lTg00O:j7mTg00O^j8YTf3R7f2R8f1R9f0R:'1'7'=p=2g00PBR;?59:p=01G;:p=8g00P`R<P;P;P;P1P1P7P8P9g00U0R=g00XMR>P:M<Hp=cP;P;P;P;P;P;P2P:P9P8P2P7f4R2f5R?f6R@f7RAf8RBf9RCMBkp=OP;P;P3PAP3P@P?P2P7P8P9P:M<[p=PP;P9g00QcP:CFp=AP9g00RJR3g00RiRDPDg00SIREP:g00SiFlp=9P;P9g00TIP:CFp=EP8P3PDPDPEP9P:Fmp=@P7P3PDPDPEP8P9P:GYp=B179:,=8p=aP<P<P;P;P4P1P1P7g00Q?P8P9P:M<Hp=dP<P;P;P;P1P1P?P2P7P8P9P:M<Hp=e%s;R1p,1dR4P8P9P:C<%L;RF35167:RGP:P7%42C21:49RH/07#3[^5;[^7;^8;RIX4<P4P=P9P:C<=51FPGP:P7%4=R=C21629RJ112=RK,79RL'=PJP9P2P>C2RMPJPLPJP:X6;RLP>O1RN,12RO,79%IJPL179:#IXL;X6;RJP9P9%89PKPOPLPLPLP;P;g00Wi119:Cj#8XH;X4;ROP2P2%82P=PNPLPL%4:#8X6<RN1G;>CcM:OGPEMP:CRPMp-0RMg00XkR=#ZRK%X=R=P;P;1D;8RPP8%W;CCP81D;9CC%V;RQ%U;RRg00WDRS#T,?;RT%KSRU#K,?;RV'A,9R1J;>9;;T,EV,9R5@R%LDRVPRP3PDPDPEP2ESCB1rRERWP:P8g00VdRXg00YWRY'G1q:8=5XYdAp;>9CoRYb;b=b>X2;X3;W<16:9RZP9P:P>C2P7[^2;^3;^<MP:1:47/0?#3P7P@P9O4b:b9W1X5;W0X7;X8;P4%>7P9P:C<=51FPGP:P7%>?#4C21:42RG/n710G71QG7'i1:4?/Q2PXP51:4@R5/0?PXP1P91N;BRXP4f:RG%hSR[,1BPAC<R\n0100000020000=51F105BR5#3R]]0P91:4A/0@R^A51XFP11N;GP0P;PMP:g00Ulg00UORMn10110500021000000X@1g00VHPFP9EgPM1fM:bCXB5P]eW0WAP:O1%3^A51\F1b@C10@CR@%3@'`P610AGRA%3A1:4B/0G#3P:f;RG,0BR4P;f<RAf=R6/6:P:P6f?R@#>#4C210H6#3]1X5;16AAf>RH#>R\#4RF,1AR17aAP?W1PCP:PBF_W@P:O1%34P611A[PGP7PC16ACRG17C1R6'=PGPCPA%4HR4/1[C2R?PGP6PGPL11:[X6;R6P4O1R^O1R],1AR5,7C%IGPLPJPCPC%8CP1P5PLPLPLPOPAPA%8APFP]PLPLPNP\P^P6PHP4%84CdEeM:OGPEMPBCRP?%^@%4@,6>PKP=P;PPP91D;7CCPQPR1?;SRS1?;URU'A,9R1J;[RQ9;;T9;;S,EU,9R5@RPVPRPRP3PDPDPEP;PUg00Z7PSCF,9RE]PVA;;SQRQ/AU,9RA;;QT,EU,9R5@RCBCBPWPYb;b=b>X2;X3;X?;PZP9P:118[R[C21089PM[16[7P7P[P2C2[[^2;^3;^?;P:fA#4PAP@P8P7O5b:bGb9O5WIP:O1n200110400021010111100bKW0WEP:O1n10210210300021010111100P2O1bFbJW1X5;W0X7;X8;XDIX4<P:C\X4<o"). Qed.

Lemma memchr_some : forall pos c n p, 0 <= n ->
  memchr d pos c n = Some p ->
  pos <= p < pos + n /\ znth d p = c /\ (forall q, pos <= q < p -> znth d q <> c).
Proof.
ltac2:(KReplay.run1 (kr_t_LexerModel ()) ["BytesFacts"] "h01xh11Hh21qh32H0h44__x1h51nh62Hnh77__arithh84__ffh98__varmaph:5__with;1ch<1mh=1ph>3posh?1yh@1zhA2z0p;2p;1p;4p;3p;5p;<p;6p;7p;8p;Bg00;9j22Tg0028j1\Tg00[Ej4GTg00Kaj2BTg003Zj36Tg00\CR0j1=Tg00\cj5UTg0044R1j19Tg009cR2j24Tg00:@R3j21Tg005Lj20Tg004Tj27Tg00H:j1;Tg00]hj28Tg00;Uj1:Tg00CTj25Tg00<3j4WTg00MNl<NTg00<Vj6<Tg00Z^j4FTg00^Ej2ETg00^gj2DTg00=dj1HTg00>Dj1ITg00>dj2CTg00@>j1JTg00@\j1KTg00AGj2ATg00BOj2LTg00J1j4MTg00N3j7@Tg005gj1OTg00O^j8PTg00C2j2?Tg00Cnj2RTg00DZj3STg00E9j4[Tg00_Aj2ZTg006Ij6YTg00LCl<>Tg00LhlBXTg00PBR4f1R5f0R636p=3P4g00P`R7P4P4P0f4R0P1f3R8g00__f2R9P5P6M<>p=VP7P4P4P4P1P1f5R1P0P8P9P5P6M<>p=TP4P4P4P4P4P4P2P6P5P9P2P8P0P1f6R2f7R:f8R;f9MBXp=Qg00XMR</25R=%\4p,1dR>P0P8P9CG1B4536%=8R?P1P0P9P6DU1219%9?,41,19'017>9/3012261168'017>5R?/32#;[^24'0'0P4%=0R@#9RA12:014:6,10'017>0/3212;61161'013?;#;[^24'0'0X@4P6P01228RB142ARC,18RD'0RE17>8/3112:61160'013?:#;[^24'0R?'018<0,42,18,0B/0?R:PEP?P6X04RE18<6X04R>P0O1RFO1RG,42RH,18RI,0BP?PBPDPBPI%:BP4P4P3PEP31156#:X?4X04P8P81548PCPHPEPEPEP4P4g00Wi1456CW,54X<4X54P2P21542PAPGPEPE%96,54X07P@PFPEP>P0P01540DVETM:QM<NE<%:?E<P6CFP:1E<111<118<1R:/31'0121<A64:<'0'D18<2P4g00XkR:#H%I:1C45%J4%K4R:g00RJR1g00RiR>P>g00SIREP:P1P>P>PEP41A4<g00Qcg00WD,L4CMg00SiF@R1%O>P1GP1?:EP6P9g00VdREg00YWR:'51R69=6E:dAS4<5C[b8b9b:X4412<6P=[^44P6P;P2O2b7bAb3b3,Z0EY1420,18,0B/0?P6b1b1W1W6X=4X54X;4X>4o"). Qed.

Lemma memchr_none : forall pos c n, 0 <= n ->
  memchr d pos c n = None -> forall q, pos <= q < pos + n -> znth d q <> c.
Proof.
ltac2:(KReplay.run1 (kr_t_LexerModel ()) ["BytesFacts"] "h01Hh14__x1h22Hnh32Hqh47__arithh54__ffh68__varmaph75__with81ch91nh:3posh;1qh<1zp;2p;1p;4p;3p;7p;8p;6g00;9j20Tg0028j1MTg00[Ej4<Tg005gj12Tg003Zj31Tg009cj24Tg00:@j23Tg005Lj25Tg00\Cj1:Tg0044j17Tg00=dj16Tg00>Dj18Tg00>dj29Tg00@>j1LTg00@\j1KTg00AGj2JTg00BOj2@Tg00J1j4?Tg00N3j7>Tg00O^j8=Tg00C2j2ATg00CTj2BTg00Cnj2;Tg00DZj3CTg00E9j4DTg00_Aj2ETg00ISj6FTg00`Lj6GTg004Tj2HTg00H:j1ITg00PBR0g00XMR1f0R2'0R3%M0p,1dR4f3R5f2R6f1R7C<%2031f5R8/021485,32'5f4R5#:R9f6P8P6P7P0P5f7R:/0614:2,36'5X<0P2%79g00XkR9#6%891907%L0%K0R9g00RJR:g00RiR;P;g00SIR<P9P:P;P;P<P01J01g00Qcg00WD,@0C?g00SiF>R:%2;P:G=1A9<P2P6g00VdR<g00YWR9'B1;26=1<9dAC017CDb5b6b7X101017\3^10P2P8P5O2b4,E5EFEG1H47=108#IP2b0W3X;0W0W2X90X80W:o"). Qed.

Lemma skip_fwd_n_bounds : forall f p e, p <= e -> p <= skip_fwd_n d f p e <= e.
Proof.
ltac2:(KReplay.run1 (kr_t_LexerModel ()) ["BytesFacts"] "p'0h04__x1h11Hh27__arithh34__x2h41ph54__ffh68__varmaph75__with81ei001eh91fh:2IHh;4__x3h<1bi011bh=2NEh>2e0h?1ri021ri031np;2p;4p;1p;3p;7p;6p;8g00;9j20Tg00aQj42Tg00=dj1GTg00>Dj1]Tg00>dj2=Tg00?Bj1RTg00?`j4ATg00@>j1JTg00@\j1HTg00BOj2:Tg00Ajj1ETg005gj1ZTg00C2j2VTg00CTj2UTg00Cnj2QTg003Zj36Tg00DZj3PTg00E9j4MTg007cj2LTg008Ej2@Tg008bR0j2ITg00bSj1;Tg004Tj2>Tg00c1j1?Tg00d1j28Tg009Ej1KTg009cj23Tg005Lj2<Tg00ISj7FTg00H:j1NTg00FVj1OTg00J1j4BTg00J\j6DTg00AGj2STg00NWj3TTg007Dj1\Tg00K@j4[Tg00N3j7YTg00O:j7WTg00O^j8XTf3R1f2R2'0f1R3f0R4'0'<p=1g00PBR5P3g00QcP4CBp=5P3g00RJR6g00RiR7P7g00SIR8P4g00SiFYp=4P2P6P7P7P8P3P4FWp=9P1P6P7P7P8P2P3P4GXp=71023/<4p=Cg00P`R91034R:P2p,1dR;P1P2P3C2R<P<P3C1[^85^45R<X99g00XkR=#GR>%]=R=P51=52R?P3%R5CA%J5R@%H5RAg00WDRB,:5RC%EB,:5RD'5,4ARE%Z7RF15CC,4ARG=9AEC71VA8RHP4P2g00VdRIg00YWRJ'U1Q42=6IJdg00XM=P53CMRKb5b6b7X05X35RL1043P3P3P3P2C1[^05^35RMP4P2P1P3O3b2P2P;g00U0P2P3C2RNPNP3C1eX1:X85X451L23A65231@23'I1@12PIP0f4R0=651f6RNPIP5%;31>;N#?RO'8P;f8RP%KBRQ,3NRRf5RSC2RTPNn0100000020000RUPUPSC1P3A65S0RUP5PS104NP3PIP5%;JRJ1>;3#?'8P;f:RV133Qf7RWC2P3n0100000020000RXPXPWC1]1X4510SSP>P=1=53P@A9AGGPHPKb5b6b7X051044RG/<G^05P4PWO1b2PNPIP518JOP;f9RJPRPNC2PNn0100000020000RRPRPNC1eW1PNP4P0FFW>P4O1%NUPOPIPIPPPIP5P4P;PV13PQRVPWC2RUPPn0100000020000RRPRPWC1P4PP13WQRRPNO210RNPVPUPUPWC1[P>P=P5P?P31=51CAP@PAPAP6P7P7P8P5PCg00Z7%OB,:5RBCB,4AEDPFPA15CB,4APFPAPA1S5Q9T5CRC/5B,4APF15CD,4A15DB,4ARB59AC7PFA9AEBC7C7C7PHPKb5b6b7X05X35X;5A6542g00UO[1031132Q/00131Q100SRK7C0[AC10K[[[^05^35^;5P4PPP;f;13JQPPC2PJP1PWP3O6b2b:PLPMP4PWPPPNO3b2n0110100020100b<PNPIP5g00dO#;/8OPTPNn0100000020000RNPNPSC1eW=P4O1n10210110200021010011103b<b?P2P;%\0P2P3C2R2P2P3C1eX1:X85X45X:<X99P4C[W9o"). Qed.

Lemma skip_fwd_n_exit : forall f p e, p <= e -> Z.of_nat f = e - p ->
  let r := skip_fwd_n d f p e in
  (r = e \/ is_space (znth d r) = false) /\ (forall q, p <= q < r -> is_space (znth d q) = true).
Proof.
ltac2:(KReplay.run1 (kr_t_LexerModel ()) ["BytesFacts"] "p'0h01qh14__x1h24__x2h33Hf0h47__arithh54__ffh68__varmaph75__with85cstr0h91Hh:2Hfh;2Hsh<4__x3h=1ph>1ri001rh?1xh@2HqhA4__p1hB1ei011ehC1fhD4__x4hE1bi021bhF2e0hG1AhH1BhI2IHhJ2NEhK1ahL1ni031nhM1si041shN1yp%0p&0p;2p;1p;4p;3p;6p;8p;7p;<g00;9j25Tg0044R0j11Tg00doj2:Tg00aQj49Tg00^gj2FTg003Zj1ij3;Tg00;Uk108Tg00CTj2QTg00Z^j4ATg00eLj1yTg00ejj2vTg007DR1j18Tg00fKj2WTg00g4j3bTg00g]j3dTg00hFj2aTg00=dj1pTg00i2j3gTg00>Dj1nTg00>dj2VTg00?Bj1lTg00?`j4CTg00@>j1kTg00@\j1jTg00AGj2`Tg00Ajj1_Tg00BOj2HTg00iRj3STg005gk107Tg00C2k206Tg00Cnk205Tg00DZk304Tg00E9k400Tg00j5j3hTg00FVj1~Tg00G;j6|Tg00G_j4LTg007cj2{Tg008Ej2fTg008bR2j2zTg00bSj1PTg00d1j2?Tg009Ej1xTg009cj24Tg00=?j1OTg00ISj8uj7rTg00H:j1JTg00NWj3cTg00HSj2tTg00I3S00j2sTg00jOj3wTg00K@j4qTg00:@j2eTg005LS01j2YTg004Tj2ZTg00c1j1TTg00LCl<]Tg00MNl<oTg00J1j4^Tg00N3k701Tg00O^j8mTg00O:k702Tg00J\k603Tg00PBR3f1R4f0R53;p=0f3R6f2R7'51e45'Yp=31Z45#Tp=>g00VdR8g00YWR97;5p=Df4R:=;361Z74#Tg00dOR;5;8'F/Y5p==A;85;p=Rg00XMR<=;35p=U1Q35p=7g00P`R=P3P3P3P0P0P6P7P4g00U0R>P<P5M<]p=}P3P3P5P4P7P6P:f5R?f6R@f7RAf8RBf9RCM<op=BP3P4g00Z7P5C^p=@P4g00RJRDg00RiREPEg00SIRFP5g00SiK01p=2P3P4g00QcP5C^p=GP6PDPEPEPFP7P4P5Gmp=6P3P4g00TIP5C^p=[P7PDPEPEPFP4P5K02p=MP:P61474P5C9p=<1e45,Y7p=EP=P=P3P3P1P0P0P6g00Q?P7P4P5M<]p=IP=P3P3P3P0P0P?P:P6P7P4P5M<]p=KP4PDPEPEPFP5J03p=N1Z45#T=;8;p=\A;374/F5p=X1545R0%161:47R1'0p,1dRGP:P6P7C9P3P5P6PGP5P?P5P5P4C31>G4#DRH[^03D=RIb>[[^B3^=3RJXC=%1>RK/011067RL1>G6RM#RRN'FP:P5P5P:C3ROPH[^031:76RP,0K%UPRQ%i3RRP5X?3RSPR1045RT$08XN3X?3RUPKPSP<O1RVPSPS%15#7X?=RW1Q3<C}RXPPPP%7PM:BP5CAPQg00XkRQg00WDRP#y,v3RY%8>#8RZ,W35b31W3>R[5d3g00jiR\'a%pQR]3g%nQR^P31V37R_P4%l3R`CCRa%k3Rb%j3Rc1`3<%_PRd,H3Re1H3PRf5S3'@,2c&07ERgPc1Gfe,2cRhPg1@fe,2cRiC6C6206cFRjP5P71Q8920557#DdB043<4H00Rkb5b6b7X13X231:45#U1547Rl1076[[^13^23P5P:P?P4P6O4b4b39hLN1::?RN,0K%UNRmPRPSPRPUPKPVPXPNPN%7NM:BP7CAPmp-0RmP]P^P3P`P4P_CCPbPc%~P,H3RN,Gf,2c1[Nf,2c5McPgPcPDPEPEPFP:E|RFC6PjPkb5b6b7X13X23WAS02P5P4P4P5C3P6[^13^23^AmREP5%DMRDP6PAP7O4b4b3VOX03CLPGP>P6P7C9P3PIb>eW:X90XB3X=3%8:#1/011{671f67,zL1f:6P8P210?:P8P3%P41>GAR2'?PGPCPA%xPRPP@D<S03PAn0100000020000R>P@PGP>15B5R>P8P3%P71>GBRO'?PGf:RX14BPRVPAC9RKPBn01000000200007E5PH[^03D=P410@?RnP3P@155Af;Ro#8#11:B4'0P8P3%P9R91>G7'?PGf<Rp147PRqPCC9P7n0100000020000RrPCPGPrP6P5P5P8P31?9MPGf=RMP6PPPXD<P6n0100000020000C3PH[^03D=]:]9X=315@@%8X#11:AA'010BBRr%RORs'F15C5Rt?E5CRuPH[^03%7B9hrs%8MRs#1Rr1:XXRv'0%1MRw/4P/0vRxPRPSPRPUPrPS145PRrX?3RyPwO1RzO1PSPSPWPsPzPyPMPw%7wCIEKPvPv%7vM:BP7CAPxf>Rx#O%1xRv,5<P]P^PaPbPc1[ef,2c9MchPgPFC6PjPkb5b6b7X13X23XAmPEP51>G:#DRmP:PMP6O4b4b8b3VuX03CLP8P31?9OPGPoPVPBC9PBn0100000020000RVPBPGPVP8P31>GCRV,?9PGPpPCPPPCD<PCn01000000200009Et5PH[^03D=eW:W9PAP5P?P:GuWFP5O1%JnP2P81Q85A;8O5P81>GXRn=;85P8P3P4PGPM14oPRtPXC9R9Pon0100000020000RuPXPGPuPpP5P5P8P3P7PGPx14pPRuPoC9RFPpn0100000020000C3PH[^03D=];P4%DVPo14XPRzPC%8pRs#1R{1:CXR|'0%1pR}/4P/0|R~PRPSPRPUP{PSPyP}O1R{O1PSPSPWPsP{PyPpP}%7}CIEKP|P|%7|M:BPACAR|P~%OMR}15<wRwP]P^PaPbPc1NciPgPcPhPg1`3PRi9c3fRa/Ge,2cR{C6C6PjPkb5b6b7X13X231054g00UORs[15q6\l[^13^23P5PpPMP@PoO4b4b8b3P|P~P}Pw%8Z,W39b3Y=d3[/a\=gQ]P^P3P_P41V36R_CCPbPcAS3eN,@a,2cPgPc1@Ne,2c,NcPgPc1GNe,2cPgAc3Ni9S3e,@f,2cC6C6C6PjPkb5b6b7X13X23X<310r1Ps\L15:614?P,::,06[[[^13^23^<3P5PMPpf?RL#1RrP7P@PoO6b4b8b3O4PGPpPzPCC9RzPCPGPzPtP5P5P9C3PH[^03D=Q011\G99X9XPuP5P5PFC3PH[^03PFPoPGPFPMP5P5PGPLPMPPPpD<RMC3PH[^03D=P51\GM9XMp14LPRMP5P5PGfARFPMPxC9RMC3PH[^031\GM9XMxf@RMP5P5PGfBRuPMPPPLD<C3R9PH[^03P41t4F104FRt%Jt'sQ00107uRu%JuPDP5fCRD,06RuP3fDRtfERzP5P5PGfGR1PzPPPtD<C3PH]@X03PtPtPtPGfFRiPtPPPDD<C3PoW@P:P5P6FrWFP5O1%JuP?P:%8iRu#1Ra1:DtRt'0%1iRD/4P/0tRQPRPSPRPUPaPSPyPDO1RaO1PSPSPWPuPaPyPiPD%7DCIEKPtPt%7tM:BPFCAPQ%O1%11,5<P]P^P3P31V3:P7P`CCP4P_CCPbPc1@ef,2c,NcPgPc1[eN,2cRN9MchPgPc%_d,H3Rd,@f,2c,NcPgPc1Gfd,2cPgAMc{NC6C6C6C6PjPkb5b6b7X13X23X<3XD3Ps\TAEl76107?Ps[156@14:PP?P?P@C3[[[[^13^23^<3^D3P5PiPGfIP1PPPiD<PAP1P6P@PMPzO8b4b8b3O2WLP5O1n200110400021010111103bMX@9X03CLWHWGP4P5O2n2001000000121000000bKW;%RV10XCRX%RnRn'FPoP5P5PoC3RVPH[^03AwXn5%8xRn#1RX1:opRp'014vP/0pRPPRPSPRPUPXPSPyPvO1RXO1PSPSPWPnPXPyPxPv%7vCIEKPpPp%7pM:BPCCAPP%OL15<rQ02PEP5PmP:PLP6O4b4b8b3VVX03CLW;n0110200020101P5O1b;bEP8P3%P;R;/?2Q03PAn0100000020000RAP@PGPAP8P31?;OPKPBn01000000200009E>5PH[^03D=eWJP5O1n10210210000021110111103bEb>PG%8?P6P7C9P3PIb>eW:X90XB3X=3XIJXC=P5CqXC=o"). Qed.

Lemma skip_fwd_bounds : forall p e, p <= e -> p <= skip_fwd d p e <= e.
Proof.
ltac2:(KReplay.run1 (kr_t_LexerModel ()) ["BytesFacts"] "h04__x1h14__x2h27__arithh34__ffh48__varmaph55__with61eh71pp;2p;1p;4p;7p;8p;3g00;9j20Tg00doj2HTg00\Cj13Tg00=dj12Tg00>Dj1GTg00>dj2:Tg00?Bj17Tg00?`j44Tg00@>j15Tg00@\j16Tg00BOj21Tg00Ajj18Tg00J1j49Tg00N3j7FTg005gj1ETg00O^j8;Tg00C2j2<Tg00CTj2=Tg00Cnj2>Tg003Zj3?Tg00DZj3@Tg00E9j4ATg00kUj4BTg00l^j3CTg005Lj2DTg00PBR0f1R1f0R2'0f2R3,H1#3P3P1g00XkR4#2%G4P01:03P1%70C4%50%60R4g00RJR5g00RiR6P6g00SIR7P4P5P6P6P7P0g00WDR5,10g00Qc%85,10C9g00SiFFR5%E6P5G;1<47P2P3g00VdR7g00YWR4'=1>23=?74dg00XM=@01CAb3b4b5X00X1010211013[^00^10P2P3f3P1O3b2CBp,1d?C31R2,031021'DeUX60W7o"). Qed.

Lemma skip_fwd_exit : forall p e, p <= e ->
  (skip_fwd d p e = e \/ is_space (znth d (skip_fwd d p e)) = false) /\
  (forall q, p <= q < skip_fwd d p e -> is_space (znth d q) = true).
Proof.
ltac2:(KReplay.run1 (kr_t_LexerModel ()) ["BytesFacts"] "h01xh14__p1h24__x1h34__x2h44__x3h51Hh62H0h77__arithh84__ffh98__varmaph:5__with;1eh<1ph=1qh>1yh?2z0p;2p;1p;<p;3p;4p;6p;7p;5p;8g00;9j25Tg00doj24Tg00\CR0j1ZTg0044R1j1ATg00]hj2?Tg003Zj1\j30Tg00;Uj1YTg00CTj2:Tg00MNl<JTg00^Ej2ITg00:@j2@Tg005Lj21Tg00^gj2=Tg007Dj1<Tg00fKj26Tg00g]j37Tg00hFj2;Tg00eLj1[Tg00ejj2XTg00g4j3WTg00=dj1VTg00i2j3>Tg00>Dj1UTg00>dj2CTg00?`j4RTg00@>j1QTg00@\j1PTg00G;j6KTg00BOj29Tg00Ajj1MTg00FVj1NTg00iRj3OTg00J1j43Tg00AGj2TTg00m^j7gTg005gj1fTg00C2j2eTg00Cnj2dTg00DZj3cTg00E9j4bTg00Ekj4aTg00nBj5`Tg00l^j3ETg004Tj2GTg00c1j1DTg00LCl<FTg00N3j7_Tg00O:j7^Tg00O^j8]Tg00PBR2f1R3f0R430p=2P2g00P`R5P2P2P0f4R0P1f3R6g00__f2R7P3P4M<Fp=SP5P2P2P2P1P1f5R1P0P6P7P3P4M<Fp=LP3g00RJR8g00RiR9P9g00SIR:P4g00SiF_p=8P7P8P9P9P:P3P4F^p=BP6P8P9P9P:P7P3P4G]p=H15341437R;#ZR<P7P3P4%A<R=/2;g00XMR>/?;R?/2;R@P2P2%\2RAP4X02RBPA1234#YX>2X02P=P?PBPB%A4,:2X05P<P?PB1?>4X02P;P;1:2;RBDSELP;P;PBM<J1I>;1@>;/1@15;>R@A02?>'1'=1476,?>P2p-0R?g00XkRBg00U0R<#<R5#<R=,62RA1625162<R<572572g00jiR5';%<=,62g00WDR=#[,X2=W2A=72<R<572/;51;<5%VB5>B5>B3>%UBP21C27P31C26CR%Q2%P2RBPBP8P9P9P:PBP8P9P9P:P1EKP2192=R8g00Z7R<%M=,92R5%N=,92R=5O2RAC3,8BRC5BBP2PAg00QcRA1T2>RDC3,8BP2P8P<PDC3,8B5BBFg%f9R9PBP2P=PAP5C3,8BP9PCCHCH1eB:P4P7g00VdRBg00YWR:':1d47=0B:dAc2>3Cbb8b9b:X22X32X42W1124;,16A024>,1@'=15671460,27[[^22^32^42^1?P41401,@>P1P0P3P7P6O6b7b?b6CaD`p,1dR0?E73R1/231G01#Dg00dO50B'=1564AE067,@4'11G03#D=0B:[^=2'1eW5X;2X<2o"). Qed.

Lemma skip_back_n_bounds : forall f p e, p <= e -> p <= skip_back_n d f p e <= e.
Proof.
ltac2:(KReplay.run1 (kr_t_LexerModel ()) ["BytesFacts"] "p'0h04__x1h11Hh27__arithh34__x2h41ph54__ffh68__varmaph75__with81ei001eh91fh:2IHh;4__x3h<1bi011bh=2NEh>2e0h?1ri021ri031np;2p;4p;1p;3p;7p;6p;8g00;9j20Tg00oIj43Tg00=dj1GTg00>Dj1]Tg00>dj2?Tg00?Bj1RTg00?`j4ATg00@>j1KTg00@\j1HTg00BOj2:Tg00Ajj1ETg005gj1ZTg00C2j2VTg00CTj2UTg00Cnj2QTg003Zj36Tg00DZj3PTg00E9j4MTg007cj2LTg008Ej2@Tg008bR0j2JTg00bSj1<Tg009Ej1ITg00doj25Tg004Tj2=Tg00c1j1;Tg00d1j28Tg005Lj2>Tg00ISj7FTg00H:j1NTg00FVj1OTg00J1j4BTg00J\j6DTg00AGj2STg00iRj3TTg007Dj1\Tg00K@j4[Tg00N3j7YTg00O:j7WTg00O^j8XTf3R1f2R2'0f1R3f0R4'0'>p=1g00PBR5P3g00QcP4CBp=4P3g00RJR6g00RiR7P7g00SIR8P4g00SiFYp=2P2P6P7P7P8P3P4FWp=9P1P6P7P7P8P2P3P4GXp=71034,>2p=Cg00P`R91034R:P2p,1dR;P1P2P3C3R<P<P3C1[^85^45R<X99g00XkR=#GR>%]=R=P51?52R?P3%R5CA%K5R@%H5RAg00WDRB,:5RC%EB,:5RD'4,2ARE%Z7RF14DD,2A99AEC71VA8RGP4P2g00VdRHg00YWRI'U1Q42=6HIdg00XM=P53CMRJb5b6b7X05X35RK1043P3P2P2P2C1[^05^35RLP4P2P1P3O3b2P2P;g00U0P2P3C3RMPMP3C1eX1:X85X451L23A65231@23'J1@12PHP0f4R0=651f6RMPHP5%<3f5RN%IBRO'5RP,=;#;RQ'8P;f8RRPMPPC3RSPNn0100000020000RTPTPNC1P3A65N0RTP5PN104MP3PHP5%<IRIf7RU/5ORV,=;#;'8P;f:RWP3PVC3PUn0100000020000RXPXPUC1]1X4510NNP>P=1?53P@14CC,2ARX=9AXPGPJb5b6b7X051044RX/>X^05P4PUO1b2PMPHP515MORX,=;#;,8IP;f9RIPMPXC3PMn0100000020000RYPYPMC1eW1PMP4P0FFW>P4O1%NTPQPHPHPRPHP5P4P;PWPRPVC3RWPUn0100000020000RTPTPUC1P4PRPUPXO210UXPRPWPWPVC1[P>P=P5P?P31?51CAP@PAPAP6P7P7P8P5PCg00Z7%OB,:5RBCB,2AEDPFPA14CB,2APFPAPA1S5O9T5BR8,4C,2APF14D8,2A99AEC7PF14DB,2A99AEC7C7C7PGPJb5b6b7X05X35X;5A6542g00UO[1031150O,021010RJ?C0P[ACJ0N[[[^05^35^;5P4PRP;f;PI15ROC3PIP1PUP3O6b2b:PKPLP4PUPRPMO3b2n0110100020100b<PMPHP5g00dO#</8QPSPNn0100000020000RSPSPNC1eW=P4O1n10210110200021010011103b<b?P2P;%\0P2P3C3R2P2P3C1eX1:X85X45X:<X99P4C[W9o"). Qed.

Lemma skip_back_n_exit : forall f p e, p <= e -> Z.of_nat f = e - p ->
  let r := skip_back_n d f p e in
  (r = p \/ is_space (znth d (r - 1)) = false) /\ (forall q, r <= q < e -> is_space (znth d q) = true).
Proof.
ltac2:(KReplay.run1 (kr_t_LexerModel ()) ["BytesFacts"] "p'0h01qh14__x1h24__x2h33Hf0h47__arithh54__ffh68__varmaph75__with85cstr0h91Hh:2Hfh;2Hsh<4__x3h=1ei001eh>1ri011rh?1xh@2HqhA4__p1hB1fhC1phD4__x4hE1bi021bhF2e0hG1AhH1BhI2IHhJ2NEhK1ahL1ni031nhM1si041shN1yp%0p&0p;2p;1p;4p;3p;6p;8p;7p;<g00;9j25Tg0044R0j14Tg00doj20Tg00oIj42Tg009Ek101Tg00^gj2FTg00:@j2GTg003Zk107j3;Tg00;Uk100Tg00CTj2MTg00Z^j4?Tg00eLj1uTg00ejj2tTg007DR1j18Tg00fKj2VTg00g4j3bTg00g]j3fTg00hFj2gTg00=dj1lTg00i2j3aTg00>Dj1kTg00>dj2JTg00?Bj1jTg00?`j4CTg00@>j1iTg00@\j1hTg00AGj2`Tg00BOj2ITg00Ajj1_Tg00iRj3HTg005gk108Tg00C2k206Tg00Cnk205Tg00DZk304Tg00E9j4~Tg00j5j3eTg00FVj1}Tg00G;j6|Tg00G_j4TTg007cj2{Tg008Ej2dTg008bR2j2yTg00bSj1KTg00d1j2=Tg009cj2DTg00=?j1LTg006Ij8xTg00H:j1OTg00NWj3sTg00HSj2rTg00I3S00j2vTg00ISj7wTg00jOj3qTg00K@j4pTg005LS01j2STg004Tj2YTg00c1j1[Tg00LCl<ZTg00MNl<oTg00J1j4\Tg00N3k702Tg00O^j8nTg00O:j7mTg00J\k603Tg00PBR3f1R4f0R53;p=1f2R61G45'Sp=c1Y45#[p=:g00VdR7g00YWR87;5p=Ef5R9f4R:5;3f3R;1064'Y#[g00dOR<5;7'F/S5p=<A;75<p=X1564/S5p=Bg00XMR==;35p=^1M35p=7g00P`R>P3P3P3P0P0P;P6P4g00U0R?P=P5M<Zp=zP3P3P5P4P6P;P:P9f6R@f7RAf8RBf9RCM<op=@P3P4g00Z7P5C\p=>P4g00RJRDg00RiREPEg00SIRFP5g00SiK02p=3P3P4g00QcP5C\p=AP;PDPEPEPFP6P4P5Gnp=6P3P4g00TIP5C\p=UP6PDPEPEPFP4P5Fmp=Q15;61G45'Sp=9P>P>P3P3P1P0P0P;g00Q?P6P4P5M<Zp=RP>P3P3P3P0P0P9P:P;P6P4P5M<Zp=PP4PDPEPEPFP5J03p=N1045,Y6#[=;7<p=]A;364/F5p=W1545R0%4;1046R1'1p,1dRGP:P;P6C2P3P5P:PGP5g00WDRH$01RIAc05:1:G4#ERJ[^03E<RKb>[[^=3^C3RLXB>%4?RM/11116;RN106IRO,:GRP#XRQ'F1G5;RR9B;5RSPJ[^03106;RT,1M%^TRU&073RVP5X?3RWPV1145$00XN3X?3RXPMPWP=O1RYPWPW%45#7X?>RZ1M3=CzR[PTPT%7TM:@P5C?PUg00XkRU%uH,t3RT%8?#8R\,V35b31V3?R]5f3g00jiR^'g%lUR_3a%kUR`P31J36RaP4%j3S02CCRb%i3Rc%h3Rd1`3=1I3HRe%_HRf,I3Rg5H3'>,3d&08ERhPd1Age,3dPh1>eg,3dRiC6C6206dFRjP5P61M7820556#EdB043=4C~Rkb5b6b7X13X231054#^1564PN[[^13^23P5P9P:P4P;O4b4b39eNQ10:9RQ,1M%^QRNPVPWPVPXPMPYP[PQPQ%7QM:@P6C?PNp-0RNP_P`P31J34P6PaCCPcPd%}H,I3RH,Ag,3d1UHg,3d5QdPhPdPDPEPEPFP:E|RFC6PjPkb5b6b7X13X23WAS03P5P4P4P5C9P;[^13^23^ANREP51:G;#ERDP;P@P6O4b4b3VSX03CTPGP?P;P6C2P3PKb>eW:X90X=3XC3%8:#4/111{;611;6R?1d;6'y1d:;P7P2119:R2P7P3%K410@IRS,:GRQ'=PGPCPAPSC2S04P@n0100000020000R[PAPGP[PIP7P3%K610AIR[,:GRY'=PGf:RMPBP[C2S05PAn01000000200001G5AR[7B5PJ[^03E<P411@9RlP3PA15B5f;Rm#8#4104C'1P7P3%K8R8/=PPGf<RPPMPOC2P6n0100000020000RnPMPGPnPIP7P310;IRn,:G,=8PGf=RoPmPnC2P;n0100000020000?B5RPJ[^03E<]:]9X=315AA%8M#410BB'111CCRR10CIRp,:GRq#XRr'F1G5MRs9BM5RtPJ[^03Ru%7C9eRr%8oRR#4Rv10mmRw'1%4oRx/DI/1wRyPVPWPVPXPvPW1D5IRvX?3RzPxO1R{O1PWPWPZPRP{PzPoPx%7xCREPPwPw%7wM:@P6C?Pyf>Ry#L%4yRw,5=P_P`PbPcPd1Aeg,3dR{1Uge,3d5QdPhPFC6PjPkb5b6b7X13X23XANPEP51:G:#EP:PyP;O4RNb4b8b3VtX03CTP7P31=8qPGPmPCPpC2PCn0100000020000RFPCPGPFPIP7P310MIRF,:G,=8PGPPPMPFC2PMn0100000020000?B5sPJ[^03E<eW:W9P@P5P9P:GxWFP5O1%OlPQP71M75A;7Y5P7A;7q5P7P3P4PGPoPmPFC2RqPMn0100000020000RlPmPGPlPIP7P3P6PGPyPP10mIRlC2RsPmn0100000020000P5P5PmC9PJ[^03E<];P410BI,:GRB#EPmPMPp%8PR8#4RR10CMR|'1%4PR}/DI/1|R~PVPWPVPXPRPWPzP}O1RRO1PWPWPZP8PRPzPPP}%7}CREPP|P|%7|M:@PAC?R|P~%LoR}15=xRxP_P`PbPcPd1NdiPhPdP{Ph1`3IRi9H3gRb,Ae,3dC6C6PjPkb5b6b7X13X231154g00UORR[1546R8156n[[^13^23P5PPPoP@PmO4b4b8b3P|P~P}Px%8\,V39b3T=f3]/g^=aU_P`P3PaP41J3;RaCCPcPdAs3eiAH3gH'>,3dPhPd1>Hg,3d,NdPhPd1AHg,3dPhAH3bH,>e,3dC6C6C6PjPkb5b6b7X13X23X<311v1PR\?15:;10:I/09,1;[[[^13^23^<3P5PoPPf?R?#4RvP6P@PmO6b4b8b3O4PGPPPMPpC2RpPMPGPpPIPqP5P5PFC9PJ[^03E<Q01A]GqI9WqmPsP5P5PlC9PJ[^03PsPPPGPsPIPGP?Po10PIC2RsP5P5PPC9PJ[^03E<P5A]GsI9WsoPGfARsP?10yIRoC2RlP5P5PoC9PJ[^03A]GlI9Wl?PGfBRlf@Ro10?IC2P5P5P?C9RqPJ[^03P410oIRF,r4114FRF%OF'vQ0010sI,16RF%OFPDP510lI,1;RlP3fCRD/0IRFPGfGRpfER1fDRe/0IC2P5P5PeC9PJ]@X03PGfFRbPePFC2PFPFPDC9PmW@P:P5P;FwWFP5O1%OlP9P:%8bRl#4RF10DeRe'1%4bRD/DI/1eRUPVPWPVPXPFPWPzPDO1RFO1PWPWPZPlPFPzPbPD%7DCREPPePe%7eM:@PsC?PU%Lp%4p,5=P_P`P3P31J3:P6Q02CCP4PaCCPcPdAH3HiRi,>g,3d,NdPhPd1UgH,3d9Qd{PhPd%_f,I3Rf/>H,3d,NdPhPd1AfH,3dPh1Ugi,3d9Qd{C6C6C6C6PjPkb5b6b7X13X23X<3XD3114OPR[Ac86;PR\215@9P:P9P9PSC9[[[[^13^23^<3^D3P5PpPbPAPGfIPp10bIC2P;P@PoP1O8b4b8b3O2WLP5O1n200110400021010011103bMX@qX03CTWHWGP4P5O2n2001000000121000000bKW;%XB11CMRM/FrPuAqMr5%8yRM#4Rr10mPRP'11DwI/1PRmPVPWPVPXPrPWPzPwO1RrO1PWPWPZPMPrPzPyPw%7wCREPPPPP%7PM:@PCC?Pm%L?15=vQ03PEPNb4b8b3VtX03CTW;n0110200020101P5O1b;bEP7P3%K<R</=QQ04P@n0100000020000R@PAPGP@PIP7P31=<YQ05PAn0100000020000?B5[PJ[^03E<eWJP5O1n10210210100021110011103bEb>PG%89P;P6C2P3PKb>eW:X90X=3XC3XILXB>P5CpXB>o"). Qed.

Lemma skip_back_bounds : forall p e, p <= e -> p <= skip_back d p e <= e.
Proof.
ltac2:(KReplay.run1 (kr_t_LexerModel ()) ["BytesFacts"] "h04__x1h14__x2h27__arithh34__ffh48__varmaph55__with61eh71pp;2p;1p;4p;7p;8p;3g00;9j20Tg00doj2HTg00\Cj13Tg00=dj12Tg00>Dj1GTg00>dj2:Tg00?Bj17Tg00?`j44Tg00@>j15Tg00@\j16Tg00BOj21Tg00Ajj18Tg00J1j49Tg00N3j7FTg005gj1ETg00O^j8;Tg00C2j2<Tg00CTj2=Tg00Cnj2>Tg003Zj3?Tg00DZj3@Tg00E9j4ATg010Lj4BTg011Vj3CTg005Lj2DTg00PBR0f1R1f0R2'0f2R3,H1#3P3P1g00XkR4#2%G4P01:03P1%70C4%50%60R4g00RJR5g00RiR6P6g00SIR7P4P5P6P6P7P0g00WDR5,10g00Qc%85,10C9g00SiFFR5%E6P5G;1<47P2P3g00VdR7g00YWR4'=1>23=?74dg00XM=@01CAb3b4b5X00X1010211013[^00^10P2P3f3P1O3b2CBp,1d?C31R2,031021'DeUX60W7o"). Qed.

Lemma skip_back_exit : forall p e, p <= e ->
  (skip_back d p e = p \/ is_space (znth d (skip_back d p e - 1)) = false) /\
  (forall q, skip_back d p e <= q < e -> is_space (znth d q) = true).
Proof.
ltac2:(KReplay.run1 (kr_t_LexerModel ()) ["BytesFacts"] "h01xh14__p1h24__x1h34__x2h44__x3h51Hh62H0h77__arithh84__ffh98__varmaph:5__with;1eh<1ph=1qh>1yh?2z0p;2p;1p;<p;3p;4p;6p;7p;5p;8g00;9j28Tg00doj23Tg00\CR0j1ZTg0044R1j1ATg00]hj2=Tg003Zj1\j32Tg00;Uj1YTg00CTj2:Tg00MNl<JTg00^Ej2ITg00:@j2@Tg005Lj20Tg00^gj2;Tg007Dj1>Tg00fKj25Tg00g]j37Tg00hFj2<Tg00eLj1[Tg00ejj2XTg00g4j3WTg00=dj1VTg00i2j3?Tg00>Dj1UTg00>dj2CTg00?`j4RTg00@>j1QTg00@\j1PTg00G;j6KTg00BOj29Tg00Ajj1MTg00FVj1NTg00iRj3OTg00J1j44Tg00AGj2TTg00m^j7hTg005gj1gTg00C2j2fTg00Cnj2eTg00DZj3dTg00E9j4bTg00Ekj4aTg012Wj5`Tg011Vj3FTg009Ej1_Tg004Tj2ETg00c1j1DTg00LCl<GTg00N3j7^Tg00O:j7]Tg00O^j8cTg00PBR2f1R3f0R432p=1P2g00P`R5P2P2P0f4R0P1f3R6g00__f2R7P3P4M<Gp=SP5P2P2P2P1P1f5R1P0P6P7P3P4M<Gp=LP3g00RJR8g00RiR9P9g00SIR:P4g00SiF^p=6P7P8P9P9P:P3P4F]p=BP6P8P9P9P:P7P3P4Gcp=H18341337R;#ZR<P7P3P4%A<R=/1;g00XMR>/=;R?/1;R@P2P2%\2RAP4X02RBPA1134#YX>2X02P=P?PBPB%A4,:2X05P<P?PB1=>4X02P;P;1:2;RBDSELP;P;PBM<J1I>;1@>;/0@18;>R@A22?>'0';1376,=>P2p-0R?g00XkRBg00U0R<#>R5#>R=,52RA1525152<R<572572g00jiR5'<%>=,52g00WDR=#[,X2=W2A=72<R<572/<51<<5%VB5?B5?B3?%UBP21C27P31C26CR%Q2%P2RBPBP8P9P9P:PBP8P9P9P:P1EKP2192=R8g00Z7R<%M=,92R5%N=,92RA5O2RCC4,6BRD5BBP2PCg00QcRC1T2>REC4,6BP2P8P<PEC4,6B5BBFh%g9R9PBP2PAPCP5C4,6BP9PDCHCH1fB:P4P7g00VdRBg00YWR:':1e47=2B:dAd2>3Cbb8b9b:X22X32X42W1114;,06A224>,0@';18671360,17[[^22^32^42^1?P41301,@>P1P0P3P7P6O6b7b?b6CaD`p,1dR0?F73R1/17%_=,31,E0#Dg00dO52B';AF067/841@47'01E03#D=2B:[^=2'0eW5X;2X<2o"). Qed.

Lemma strnstr_n_some : forall f s slen p,
  strnstr_n d f s slen = Some p ->
  s <= p /\ p + 1 + zlength PEM_END_REST <= s + slen /\
  znth d p = 10 /\ strncmp_lit d (p + 1) PEM_END_REST = true /\
  (forall q, s <= q < p -> znth d q <> 0).
Proof.
ltac2:(KReplay.run1 (kr_t_LexerModel ()) ["BytesFacts"] "p'0h01qh11Hh24__x1h34__x2h47__arithh54__x3h62H1h74__ffh88__varmaph95__with:2Hqh;2H2h<1bi001bh=2Hch>4__x4h?1ei011eh@1phA2H0hB2IHhC1fhD1si021shE4slenhF1AhG1BhH1ChI1DhJ1EhK4__p1hL2b0hM1ni031nhN1ri041rhO2s0hP2E0hQ3E10hR3NE0hS4NE10i051oi061zp%0p&0p;1p;4p;3p;2p;6p;7p;8g0028R0k107Tg013_j4ETg003Zj31Tg009Ej1pTg009cj20Tg014`j2zTg004Tj28Tg00Ajj1TTg00FVj1_Tg00H:j1>Tg005gj1nTg006Ij6QTg006ej2UTg007Dj1yTg015[j2jTg00:@j27Tg00;9j23Tg016=j2HTg016ZR1j3eTg008Ej2GTg00bSj1STg00doj25Tg007cj2cTg008bR2j2bTg00CTj2aTg00:\k606Tg005LR3j22Tg00=dk105Tg00>Dk104Tg00>dj2XTg00@>k103Tg00@\k102Tg00BOj2oTg00C2j2~Tg00Cnj2}Tg00DZj3|Tg00E9j4{Tg00AGj2\Tg00iRj3lTg00?Bj1xTg00J1j4WTg00G;j6wTg00HSj2fTg00I3S00j2kTg00ISj7iTg00K@j4uTg00Kaj2tTg017>j3]Tg00N3j7mTg00?`j4sTg00NWj3rTg00O^k800Tg00O:k701Tg00G_j4dTg00J\j6qTg00PBR4f0R5'tp=6f1R6g018AR77]5p==f3R8f2R9'31765'2p=4g00XMR:9145p=IA1489g00VdR;g00YWR<716/25'2p=Rf6R=f5R>'3f4R?/081096'3/25'2p=:A]967=1;</25p=D1889=146/25p=AA1465p=<1896=145p=9A]657=1;<p=@1396/25p=?1265,29p=;13>?1096,38/25'2p=OA1;6</25p=YA1;5<p=`1096/35p=NP9g00RJR@g00RiRAPAg00SIRBP4P6g00QcP5CWg00SiRCFmp=FP4P9P6P5Csp=C1o45p=LAr465p=MP8P@PAPAPBP9P6P5L00p=B1065,39p=VP6P@PAPAPBP5PCFmp=PP9P@PAPAPBP6P5K01p=^P=P>P?P8P9P6P5CdCdp=J1096,38/25p=h1765,29p=g13>?1089/36/25'2p=v1089/36/25p=KP4P6g00Z7P5CWp=ZP6P@PAPAPBP5Eqp=[g00P`RC&074RDp,1dREP8P9P6CE%65RF31P8P6g00WDRG#pRH,06RI1z47R7P8P918E6RJ%TGRK#_S01#T#pRL1=EIP?P5P5P9C4%IJ#>RJ[^04CRF:[^@4^E4^D4S02XCCPEg00U0P9P6CE=1DFPD%n4RMP0P4p-0RNP5g00UOROg00Uln10110500021000000X?DRPg00VHRQ%66P5EQPOP?P9109HRRP7P?P818E9S03PL1=ERP>P5P5P8C4PJ[^04CRF:/U5bAW1X@4XE4XD4Q02PE%y?P9P6CE=1DF1j9H179H13H91H9H3e1H8HP;P117?H13H?P;PDP6PMP;PDf7RF,8ERS/G:PMP;PD1GSL#SPEf9RT10FHRU15=HRVCERWP;PD1HV7PMP;PD1=EURV%6FPWn0100000020000n0100000020000n0100000020000n0100000020000RWn0100000020000%6>RX51Df8RYP=10=HRZP7PYPFPEP=PLPTP5P5PFC4PJ[^049DEZCAF:]1P617>HA1DMXPDPMPPPQ%6=P5EQPOPTPFPUP7PTPYPSPLPVf:RVP5P5PYC4PJ[^04CRF:/U5b6W1WAP5O113H>A1DWX18EYRX/c:%IX1GX:'b18ET/G:P;P218EV#IP;PDP6PMP;PDf<RT,8ERX/GL#SPEf>RW10THRSf;RU/5HRFCERZP;PD1HF7PMP;PD1=ESRF%6TPZn0100000020000n0100000020000n0100000020000RZn0100000020000%6VR[51Df=R\PU10UHR]P7P\PT18EUR^PL1=E]PWP5P5PTC4PJ[^04CRF:]1P6%I^R^A1DM[PDPMPPPQ%6UP5EQPOPWPTPSP7PWP\PXPLPFf?RFP5P5P\C4PJ[^04CRF:/U5b6W1WPP5O1%>^A1DZ[18E\R\/cL1<\L1G\L'b18EW/GLP;P2A9EFLP;PD%S6PEfCR2fAR\/0HS04f@R[/5HRZCES05P;PD1HZ7PMP;PDQ04,=ES06%6\Q05n0100000020000n0100000020000S07n0100000020000%6FRF51DfBRZP[10[HR^/07S08PZP\A9E[LRX1@E^S09175\S0:9?25PJ[^043;EO]1P6P;PD%S<Q05Q07n0100000020000=1DF15\HR^/j717^7137^1H^73e15ZHS0;/H7P;P1152HR1/771371P;PDP6PMP;PDfFR1/0HRS,=ERU%61PEfHR]PSfER_/5HS0<CEn0100000020000R`n0100000020000fDRa#6Rb51DfGRcP_10_HRd/07S0=PcP1A9E_LS0>1@EdS0?1751S0@9?]5PJ[^043;EO]1P615aHRe/77A1DMbPDPMPPPQ%6_P5EQPOP]P1PSP7P]PcPEP1PLfIRQP5P5PcC4PJ[^04,YUCAF:S0A/U5b;W1W6P5O1137eA1D`b10cHRc,=EP;1a;510]HS0B,=ES0C=1;5P;fJRb/0HR`,=ERe=1;5P;PDP6fKRU#6RPPEfMRM10UHRf15bHS0DCEn0100000020000%6QRg51DfLRhPb10`7S0EPhPUA9EbLS0F%`eS0G175US0H9?M5PJ[^043;EOS0I]1]=P610QHRe,=ERi#`Rj%6b%6]Rk51DPDP4P0P4P4P5P5Phn10110500021010600X?DPPPgP5J061<UQ1<hbP4PMfNRg/35RP105HR010gM7N7PEP5PLfORlP5P5P6C4PJ[^049DE0CA3;X@413MM10MHRm/07S0J10MhS0K'3RnA9EMLRo1@EmRp175gRq,2PRrPJ[^04S0L'2S0M'2Rs'2g00XkRt$05Ru&04tRt1X46Rv&034Rw&024Rx1o4GRy;Fy1~xBRzP5P91a;<1}59#`dA|4:6C{R<b7b8b9X241355^24P5PgO1b4PnPsPuPt1X49Rs1X48S0N7C6S0OPwPx%LKRn%_GRG#LR{1\4HR|5l45Fx%nAR}1My|S0P/MnR~1My{5FxCBPzP<b7b8b9X24X34X54159H,3610I9S0Q?V68[^24^34^54P5PMP7PgPYO4b4PoQ0MPTPpQ0LP8PuPt%x4RT?C9sACv9T7C9PwPxQ01#LRv%TG#LRY5FxP4PYg00TIS01PvCW,Px5^xP}PxP@PAPAPBP?EwCBPzP<b7b8b9X24X34XKNP5P6P6P5C4P8[^24^34^KNP5Q03#I#>P9fPRNP6O4b4VrX04FJFJPUP5EQW1P5O1b;W1W=g00dOS0391;iPEPhP`15QHCE=1DkPhPfQ0DPQP5O4PfPQPeP7PfQ0DA9EQLS0D10hHRkP5P5PbC4PJ[^04,2jS0L'2F:P313kbQ0EPk15UHQ0FQ0GQ0H9?m5PJ[^043;ChPMPUPfP7Q0KA9EULS0K1@EfAgP5hPJ[^043;EvP510gHRP/3hQ0J10lHRh15gH10NHRU??5qPJ[^04S0J9;opChP310P7S0G15lH7VUA9EgLS0F1@EPS0HfQRP/0HRo175lS0E7?5PJ[^043;PPPlPhP7PPPNPEPlPL1@EhS0MfRRqP5P5PNC4PJ[^04'2CAF:P510qHRm15PH'09NU7A9EPLRU1@EoRbfTRjPHP5175qS0RCKPJ[^043;P3A9EqLfUR`/0HRiP5P5fSRrC4PJ[^049DEmP`Pr10rHRmP7P`PjPEPrPLfVRBP5P5PjC4PJ[^049DEmCAF:P5A9EjLfXRA/0HR@P5P5PBC4PJ[^049DEiP310BH,@EfYRiPHP5fWRv,75S0SCKPJ[^04PiPv10vHRYP7PiPAPEPvPLfZRIP5P5PAC4PJ[^049DEYCAF:P51@E@f\R@PHP5175ICKPJ[^0413@I10IHS0Tf[RY,0@7N7S0UA9EILS0VQ0T,@ES0Tf]RIP5P5PYC4S0WPJ[^04S0X'2S0Y'2S0Z'2PuPtACs6TPwPxQ0P=FxnS0PP}AFxynS0[CBPzP<b7b8b9X24X34S0\13061369S0][^24^34S0^P5PYPIPWO3b4Q0UQ0ZPuPt1X4?S0Z?C9TQ0N7C6PwPx1M{|%TK#LRK=l4|'M9Fx~P}1M{K9Fx~CBPzP<b7b8b9X24X34X54X>4S0N158H,0R9N06Q0Q?V8?[^24^34^54^>4R0P5P@PIP7PYPVO5b4Q0VQ0YP>Q0TQ0XP6Q0Wf^RY,f61<6YRY%>Y'kQ00f_RY,<9RI%>I18E8#I#>RIP5f`R@,<8R~P4faRKfbR|P5P5P@C4PJ]:X04PKPKPKPYC4PBW:P?P5P8FiW?P5O1%>~P>P?PuPtQ0OPwPx1Zny,Px,[xRyP}PxQ0[P4PnQ01P{CW,PxR{5^xRnP}Q0P=^x{R{CBCBPzP<b7b8b9X24X34X541<65PO[R~Q0]?g98RYPRP8P8P?C4[[^24^34^54P5P@P>P|P6P?O5b4O2WMP5O1n200110200021010111103bOW:X04FJFJWJWIP6P5O2n2001000000121000000W;WHP6P5O2n2001000000121000000W;WGP6P5O2n2001000000121000000W;WFP6P5O2n2001000000121000000bBW1W=n0110000020101P5P9O2b=b<W1W6P5O1n200210000000021000011000P9O1bLb<W1XQXP5O1%>XP;PDQ03#SQ05Q07n0100000020000=1DFP210ZHRFP^P[P5O4PFP[Q08PFP^Q09102HR^Q0:7?5PJ[^045;XEOP313^\Q04P7Q0;,0^PEP\PLQ0610aHR\P5P5PZC4PJ[^04'YCACKPaPZPFP7PaP2PEPZPLP_P5P5P2C4PJ[^049DEFCAF:P513d2P\P7Q0<,0SPEPaPLPcP5P5P_C4PJ[^049DE\CACKP3Q0=151H7VcQ0>Q0?Q0BQ0@7?5PJ[^043;Q0AP515]H,0e9Nc7PEP]PLQ0CPfP5P5PQC4PJ[^04'YCAP3Q0DQ0LQ0IP5Q0KPhP5P5PMC4PJ[^049DEkP3PpQ0JPNPgQ0GPNPlQ0FQ0HQ0E9?P5PJ[^043;EOP5Q0MPmP5P5PPC4PJ[^0413rP10rq9No7RoQ0R9?j5RPPJ[^04Rm,2bRl,2URN'2Q0\Q0^P5PqPjPWO3b4PoPNQ0NP0P5PrPjP7PqPVO5b4PUPlP>PbPmP61f6`1<6`R`%>`'kQ001<9BR`%>`PIP51<8vRIP4PAQ0S9?i5PJ]:X04PAPAPAPBC4PMW:P?P5P8FiW?P5O1%>IP>P?PuPtQ0Z9CT89Cs6PwPxPyP}PxPnP}Px%_G#LRG1\4L'Z,Px,[xP}Px1\4:,ZG,Px,[xP}P{CBCBCBCBPzP<b7b8b9X24X34X54X>41<>LPO[%I=PO[P?PHP>17>=CK[[\Y\~^24^34^54^>4P518EiPvP>PiP6P?P]PMO8b4O2WMP5O1n200110200021010111103bOX:PX04FJFJWJWIP6P5O2n2001000000121000000W6WHP6P5O2n2001000000121000000W6WGP6P5O2n2001000000121000000W6WFP6P5O2n2001000000121000000bBW1WSP5O1n10210010400021110111103P9O1b<bNW1WRP5O1n10210010400021010111103P9O1b<bNW1WAP5O1n200210000000021000011000P9O1bLb<W1X@4XE4XD4WBXCCP5CuWCo"). Qed.

Lemma strnstr_end_some : forall s slen p,
  strnstr_end d s slen = Some p ->
  s <= p /\ p + 10 <= s + slen /\ znth d p = 10 /\ strncmp_lit d (p + 1) PEM_END_REST = true.
Proof.
ltac2:(KReplay.run1 (kr_t_LexerModel ()) ["BytesFacts"] "h01qh11Hh24__x1h34__x2h44__x3h51Ah61Bh71Ch81Dh92_Hh:7__arithh;4__ffh<8__varmaph=5__with>1ph?1sh@4slenp;1p;3p;2p;5p;4p;8p;7g0028j1^Tg019Ej3]Tg00Kaj2PTg003Zj36Tg00\Cj1\Tg007Dj1UTg01:Hj5QTg009Ej1;Tg009cj20Tg014`j2LTg004Tj2ATg00Ajj1?Tg00FVj1@Tg00H:j1VTg005LR0j21Tg00;9j27Tg00=dj1OTg00>Dj1NTg00>dj2DTg00?`j4MTg00@>j1KTg00@\j1JTg00BOj2<Tg00AGj2=Tg00NWj39Tg00J1j4CTg005gj1ITg00O^j8HTg00C2j2GTg00CTj2RTg00Cnj2STg00DZj3ZTg00E9j4XTg00G_j4BTg017>j3FTg00:@j2WTg00N3j7YTg00VdR1f1R2f0R3g018AR43Fg00YWR536p=:f3R6f2R7'71W23'1p=4g00PBR8?672/13p=T1772/13p=21A67=682/13p=51023=F74=615p=31072/73p=81A72=683p=>P2g00RJR9g00RiR:P:g00SIR;P3g00SiFYp=EA6135p=[%^8p,1dR<?]721P8336%\7#UP6P7P2P3DQg00WDR=#;R>,02R?1L84R4'010671A<2R@%?=RA#@#?#;RB1:<?f4R?P3P3P7C4g00XMRC968@#VR@[^08'13T329262P017?7107>RD/0410?6P<P7PB1:<Df5RDP3P3P6C4P@[^08'1C532106B10D?P<P6PBA3<6>C53292D6P3f6RE/7?10D>R?/04f7RF/0EP<PDPB1:<?f8R?P3P3PEC4P@[^08'1C532P010E>RG10?F784P<PEPB1:<Gf9RGP3P3PFC4P@[^08'1C510FB10G?P<PFPBA3<F>C53292GFP310?>f:R?/0G784P<PGPBA3<G>f<RGP3P3P?C4P@[^08'1C5P0A><?BA3<?>f=R4P3P3f;RFC4P@[^08'110FB104GP<PFPBA3<F>C532924FP3A><GBA3<4>f@RGP3P3f>RFC4P@[^08'1P0A3<F>fARFP3P3f?R0C4P@[^08100B10FGP<P0PBA3<0>C53292F0P3A3<G>fDRGP3P3fBR0C4P@[^0817G0fCR@,0G980BRFA><0BREA3<0>R0'1R<'1P4PFP<g00XkR<#O%N<P81D87P21D86CM%K8%J8R<P9P:P:P;P81<8=R91=8>598%?A#@#;RF,=8598g00QcR41<8A%@=,<8598R=CC,E<%I:P81=8B9989P4P=CC,E<GH1G<;P3P71R151S37#[dAZ8C2CXb;b<b=X28X38X48103>102778F1076982B[^28^38^48P3PGfEP@P?O4b:PEP0PDP2CBCBCBW9W8P2P3O2n2001000000121000000W1W7P2P3O2n2001000000121000000W1W6P2P3O2n2001000000121000000W1W5P2P3O2n2001000000121000000b1W1X>8X@8X?8o"). Qed.

Lemma count_nl_n_bounds : forall f pos e line,
  pos <= e -> line <= count_nl_n d f pos e line <= line + (e - pos).
Proof.
ltac2:(KReplay.run1 (kr_t_LexerModel ()) ["BytesFacts"] "p'0h04__x1h14__x2h22Hmh37__arithh41qh54__x3h64__ffh78__varmaph85__with91eh:1fh;4lineh<3posh=1Hh>2H0h?2IHh@4__x4hA4__x5hB1AhC2H1hD2_HhE3_H0hF1bi001bhG2b0hH1oi011ohI1pi021pi031xi041zp;2p;5p;1p;4p;3p;6p;7p;8g00;9j22Tg01;Nj57Tg00doj21Tg009cj20Tg00=dj1_Tg00>Dj1\Tg00>dj2@Tg00?`j4<Tg00@>j1VTg00@\j1TTg00FVj1FTg00BOj2>Tg00Ajj1ETg005gj1KTg00iRj3BTg00C2j2[Tg00CTj2JTg00Cnj2ZTg003Zj34Tg00DZj3YTg00E9j4XTg015[j2WTg00:@j2CTg016=j2ITg016ZR0j3UTg009Ej1HTg00[Ej4:Tg0028R1j1STg00Kaj2RTg00?Bj1PTg00AGj2GTg01<Pj6QTg004Tj2?Tg00H:j1OTg005LR2j28Tg007Dj1;Tg00fKj2DTg00g]j3NTg00hFj2eTg00i2j3dTg00J1j4LTg00K@j4^Tg00N3j7MTg00NWj3`Tg00O:j7]Tg00O^j8aTf3R3f2R4'2f1R5f0R6'2'8p=5P4g00RJR7g00RiR8P8g00SIR9g00PBR:P5g00QcP6CLg00SiR;FMp=3A`:56p=9P4P7P8P8P9P5P6F]p=AP3P7P8P8P9P4P5P6Gap==12341C56'8p=6P5P7P8P8P9P6P;FMp=c1256,84p=bg00P`R;1245R7P5p,1dR<f4R=P3P4P5D7R>P>1143R>,05R?C5[^;:^9:^<:R@X:;g00XkRA#_RB%\ARCP:1@:4RDP51@:3C<%V:RE%T:RFg00WDRG#F,>:RH%EGRI,>:RJ53F%K8R81>:GRK=3FKAB:JH,9K93FK5AFC=1[F9R9P6P4g00VdRLg00YWRM'J1Z64=4LMdg00XMRM=Y:5CXRNb6b7b8X0:X1:X5:ROP5P5P5P?C5\7^0:^1:^5:RPP6P=P3P4P5O4b3P5P<g00U0RQP3P4P5D7RRPRP?C5eX=7X;:X9:X<:1W341C341243RR1I343U1I=3PLP0f5R0/C=12=0P0PLP:P5P1P:P:P<f7RL%FIRS#E#HRTf6RU/1LRVC:RWP<f:RX%HGRG,06RYPL10UGRZD7P0n10110300021010200P0n0100000020000R[P[100VC5P51CU0PW%S:RW1JW6P<f8RVPT11LVC:=4W6P1P:P<PXPTf9R[/1XC:=4W6P[P1P:P:P5P<f>R1PYf;RY10XGR\D7P[n10110300021010200R]P]11XYR],0[C5]2P5P<PYPTP]C:1R:654Wf<R]PT11Y]R^P5PBPCP:PDP5%P:RDC<PEPFA3FJKP81G:MAB:KJ53FC=P9PNb6b7b8X0:X1:12561154,2M[^0:^1:P6f=RMP]PXO3b3P6EQP]P5P510]^C61?<5=4:TR^PMP6P6P4C6%O^R^[^4:'8'8P2PMP4P411]M,0MC61?<4=4:TP1P6P6P3C6P^[^4:'8P]P<f@R_103GPM10]GR`D7RaPa11M1,0]C5P6f?RMP=P=111M,0MC61?<0=4:TfARMP6P6PUC6P^[^4:'8P21?<U=4:TfBR2P6P6PLC6P^[^4:P_P<fDR110LGPM10_GD7RaPa11M2,0_C5P61?<V=4:TfER_P6P6PXC6P^[^4:fFR^P\P1fC/0GO312\1101GR1P<fH10YGR\P_P1D7R2P211_\,01C5[%;QR1#;#;#;,D:1D:11D:Q5N:5N:g00ji'e=dABPCP:P:1@:=P4PDC<P5P:1@:0P3PDC<C<PEPF%EI,>:RI1>:SRS53FP:PSg00TIAB:HIRE,9ICL,cF5AFP8PFPF1G:GRI,9SRS=3FHP819KIRI=3FJAB:HS,9I93FJ5AFC=P8A3FKJ19KE93FJ5AFC=C=P9PNb6b7b8X0:X1:X5:X@:XA:P3P=P=103>C6100G/23104GR>P3P311=Z,0>C5[11=0,049bR3[[^0:^1:^5:^@:^A:P6P]fGP^P<fIP`P^10_GD7P_PLP5O7b3b?WEWDP5P6O2n2001000000121000000WCWBP5P6O2n2001000000121000000b2W2XI:P6O1P<P[PT11V[C:%K:54WPOPPP6PYPXP[PVO4b3W2n10110100021110400P6O1b2bHW>P6O1120UPOPPP6PVPLPUP0O4b3W>P6O1n200210000000021100010000bGbFP5P<%;0P3P4P5D7R5P5P?C5eX=7X;:X9:X<:X?@X:;P6C^W:o"). Qed.

Lemma count_nl_bounds : forall pos e line, pos <= e -> line <= count_nl d pos e line <= line + (e - pos).
Proof.
ltac2:(KReplay.run1 (kr_t_LexerModel ()) ["BytesFacts"] "h04__x1h14__x2h27__arithh34__ffh48__varmaph55__with61eh74lineh83posp;2p;1p;4p;7p;8p;3p;5g00;9j20Tg00doj2ITg00\Cj13Tg00=dj12Tg00>Dj1HTg00>dj2:Tg00?Bj17Tg00?`j44Tg00@>j15Tg00@\j16Tg00BOj21Tg00Ajj18Tg00J1j49Tg00N3j7GTg005gj1FTg00O^j8;Tg00C2j2<Tg00CTj2=Tg00Cnj2>Tg003Zj3?Tg00DZj3@Tg00E9j4ATg01=Sj5BTg01>\j4CTg009cj2DTg005Lj2ETg00PBR0f2R1f1R2'0f3R3,I1R4#3P3P1P2g00XkR5#2%H5P01:01P2%70C4%50%60R5g00RJR6g00RiR7P7g00SIR8P5P6P7P7P8P0g00WDR6,10g00Qc%86,10C9g00SiFGR6%F7P6G;1<58f0R8P1g00VdR5g00YWR6'=1>81=?56dg00XM=@02CAb3b4b5X00X1010821021[^00^10P8P3f4P2O3b2DBp,1dP3P1P2CCR1,021D24,01'EeUX70X60W8o"). Qed.

End BytesFacts.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Target.
Context {M : Type -> Type} {ptr : Type}.
Variable ops : target_ops M ptr.

Local Notation "x <- m ;; k" := (bind ops m (fun x => k))
  (at level 100, m at next level, right associativity).
Local Notation "m ;;; k" := (bind ops m (fun _ => k))
  (at level 100, right associativity).

(* [comment removed for export] *)
Inductive token : Type :=
| TokEOF                                   (* [comment removed for export] *)
| TokSection (name : ptr)                  (* [comment removed for export] *)
| TokField (name : ptr) (value : ptr)      (* [comment removed for export] *)
| TokPem (begin_ : Z) (len : Z).           (* [comment removed for export] *)

Record lexer : Type := mkLexer {
  lx_filename : option ptr;   (* [comment removed for export] *)
  lx_line : Z;                (* [comment removed for export] *)
  lx_at : Z;                  (* [comment removed for export] *)
  lx_remaining : Z;           (* [comment removed for export] *)
  lx_complained : bool;
  lx_tok : token
}.

Variable d : list Z.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition clear_state (lx : lexer) : M lexer :=
  match lx_tok lx with
  | TokField n v => lib_free ops (Some n) ;;; lib_free ops (Some v)
  | TokSection n => lib_free ops (Some n)
  | TokPem _ _ | TokEOF => ret ops tt
  end ;;;
  ret ops (mkLexer (lx_filename lx) (lx_line lx) (lx_at lx) (lx_remaining lx) false TokEOF).

(* [comment removed for export] *)
Definition lexer_msg_text (lx : lexer) (msg : list Z) : list Z :=
  (match lx_filename lx with Some _ => FUZZ_INPUT | None => NULL_STR end)
    ++ [58] ++ Zdecimal (lx_line lx) ++ [58; 32] ++ msg.

Definition lexer_msg (lx : lexer) (msg : list Z) : M lexer :=
  if lx_complained lx then ret ops lx
  else match lx_tok lx with
       | TokEOF =>
           msg_store ops (message_store_bytes (lexer_msg_text lx msg)) ;;;
           ret ops (mkLexer (lx_filename lx) (lx_line lx) (lx_at lx) (lx_remaining lx) true TokEOF)
       | _ => unreachable ops
       end.

(* [comment removed for export] *)
Definition next_result : Type := (bool * bool * lexer)%type.

Definition set_tok (lx : lexer) (t : token) : lexer :=
  mkLexer (lx_filename lx) (lx_line lx) (lx_at lx) (lx_remaining lx) (lx_complained lx) t.

(* [comment removed for export] *)
Definition line_body (k : lexer -> M next_result) (lx : lexer) (end_ : Z) (lx2 : lexer) : M next_result :=
    let line := lx_at lx in
    (* [comment removed for export] *)
    let line1 := skip_fwd d line end_ in
    let end1 := skip_back d line1 end_ in
    (* [comment removed for export] *)
    if (line1 =? end1) || (znth d line1 =? 35) then k lx2
    else if znth d line1 =? 91 then
      (* [comment removed for export] *)
      if negb (znth d (end1 - 1) =? 93) then
        lx' <- lexer_msg lx2 MSG_SECTION ;;
        ret ops (false, true, lx')
      else
        (* [comment removed for export] *)
        r <- lib_malloc ops ((end1 - line1) - 2 + 1) ;;
        match r with
        | None => out_stderr ops (precond_text EXPR_SECTION FUNC_NEXT) ;;;
                  ret ops (false, false, lx2)
        | Some p => ret ops (true, false, set_tok lx2 (TokSection p))
        end
    else
      (* [comment removed for export] *)
      match memchr d line1 58 (end1 - line1) with
      | None =>
          lx' <- lexer_msg lx2 MSG_FIELD ;;
          ret ops (false, true, lx')
      | Some colon =>
          let value := skip_fwd d (colon + 1) end1 in
          let colon1 := skip_back d line1 colon in
          (* [comment removed for export] *)
          r1 <- lib_malloc ops ((colon1 - line1) + 1) ;;
          match r1 with
          | None => out_stderr ops (precond_text EXPR_FIELD FUNC_NEXT) ;;;
                    ret ops (false, false, lx2)
          | Some pn =>
              (* [comment removed for export] *)
              r2 <- lib_malloc ops ((end1 - value) + 1) ;;
              match r2 with
              | None => lib_free ops (Some pn) ;;;
                        out_stderr ops (reached_text FUNC_NEXT) ;;;
                        ret ops (false, false, lx2)
              | Some pv => ret ops (true, false, set_tok lx2 (TokField pn pv))
              end
          end
      end.

(* [comment removed for export] *)
Definition pem_body (lx : lexer) : M next_result :=
  let at_ := lx_at lx in
  let rem := lx_remaining lx in
    match strnstr_end d at_ rem with
    | None =>
        lx' <- lexer_msg lx MSG_PEM ;;
        ret ops (false, true, lx')
    | Some pos =>
        (* [comment removed for export] *)
        let end_ := match memchr d (pos + 1) 10 (rem - (pos - at_) - 1) with
                    | Some e => e + 1
                    | None => at_ + rem
                    end in
        let line' := count_nl d at_ end_ (lx_line lx) in
        ret ops (true, false,
                 mkLexer (lx_filename lx) line' end_ (rem - (end_ - at_)) (lx_complained lx)
                         (TokPem at_ (end_ - at_)))
    end.

(* [comment removed for export] *)
Definition split_line (lx : lexer) : Z * lexer :=
  let at_ := lx_at lx in
  let rem := lx_remaining lx in
      match memchr d at_ 10 rem with
      | None => (at_ + rem,
                 mkLexer (lx_filename lx) (lx_line lx) (at_ + rem) 0 (lx_complained lx) (lx_tok lx))
      | Some e => (e,
                   mkLexer (lx_filename lx) (lx_line lx + 1) (e + 1) (rem - (e - at_) - 1)
                           (lx_complained lx) (lx_tok lx))
      end.

(* [comment removed for export] *)
Fixpoint next_loop (fuel : nat) (lx : lexer) : M next_result :=
  match fuel with
  | O => unreachable ops
  | S fuel' =>
  if lx_remaining lx =? 0 then ret ops (false, false, lx)                 (* [comment removed for export] *)
  else
  (* [comment removed for export] *)
  if (11 <=? lx_remaining lx) && strncmp_lit d (lx_at lx) PEM_BEGIN then pem_body lx
  else
    let '(end_, lx2) := split_line lx in
    line_body (next_loop fuel') lx end_ lx2
  end.

(* [comment removed for export] *)
Definition lexer_next (lx : lexer) : M next_result :=
  lx1 <- clear_state lx ;;
  next_loop (S (Z.to_nat (lx_remaining lx1))) lx1.

(* [comment removed for export] *)
Definition lexer_init (len : Z) : M lexer :=
  r <- lib_malloc ops (zlength FUZZ_INPUT + 1) ;;
  match r with
  | None => out_stderr ops (precond_text EXPR_FILENAME FUNC_INIT)
  | Some _ => ret ops tt
  end ;;;
  ret ops (mkLexer r 0 0 len false TokEOF).

(* [comment removed for export] *)
Definition lexer_done (lx : lexer) : M unit :=
  lx1 <- clear_state lx ;;
  lib_free ops (lx_filename lx1).

(* [comment removed for export] *)
Fixpoint lex_all (fuel : nat) (lx : lexer) : M lexer :=
  match fuel with
  | O => unreachable ops
  | S fuel' =>
      r <- lexer_next lx ;;
      let '(ok, _, lx') := r in
      if ok then lex_all fuel' lx' else ret ops lx'
  end.

(* [comment removed for export] *)
Definition fuzz_one : M Z :=
  lx <- lexer_init (zlength d) ;;
  lx' <- lex_all (S (Z.to_nat (zlength d))) lx ;;
  lexer_done lx' ;;;
  ret ops 0.

(* [comment removed for export] *)
Fixpoint run_calls (n : nat) (rc : Z) : M Z :=
  match n with
  | O => ret ops rc
  | S n' =>
      rc' <- fuzz_one ;;
      out_stdout ops (Zdecimal rc' ++ [10]) ;;;       (* [comment removed for export] *)
      run_calls n' rc'
  end.

(* [comment removed for export] *)
Definition target_run (cfg : list Z) : M Z :=
  let c := match cfg with [] => 0 | b :: _ => b end in       (* [comment removed for export] *)
  let calls := Z.to_nat (Z.land c 3 + 1) in
  let plen := zlength d in
  (* [comment removed for export] *)
  a <- (if plen =? 0 then ret ops (Some None)
        else r <- lib_malloc ops plen ;;
             ret ops (match r with None => None | Some p => Some (Some p) end)) ;;
  match a with
  | None => ret ops 2                                          (* [comment removed for export] *)
  | Some owned =>
      rc <- run_calls calls 0 ;;
      lib_free ops owned ;;;                                   (* [comment removed for export] *)
      ret ops (if rc =? 0 then 0 else 1)
  end.

End Target.

Arguments TokEOF {ptr}.
Arguments TokSection {ptr}.
Arguments TokField {ptr}.
Arguments TokPem {ptr}.
Arguments mkLexer {ptr}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Module LexRun.

(* [comment removed for export] *)
Inductive ttree (A : Type) : Type :=
| TRet (a : A)
| TUnr
| TEv (e : tevent) (k : ttree A)
| TMallocQ (n : Z) (k : option nat -> ttree A).
Arguments TRet {A}.
Arguments TUnr {A}.
Arguments TEv {A}.
Arguments TMallocQ {A}.

Fixpoint tbind {A B} (m : ttree A) (f : A -> ttree B) : ttree B :=
  match m with
  | TRet a => f a
  | TUnr => TUnr
  | TEv e k => TEv e (tbind k f)
  | TMallocQ n k => TMallocQ n (fun r => tbind (k r) f)
  end.

Definition tree_ops : target_ops ttree nat :=
  mkOps (fun A (a : A) => TRet a)
        (fun A B m f => tbind m f)
        (fun A => TUnr)
        (fun n => TMallocQ n (fun r => TRet r))
        (fun p => TEv (TFree p) (TRet tt))
        (fun bs => TEv (TStderr bs) (TRet tt))
        (fun bs => TEv (TStdout bs) (TRet tt))
        (fun bs => TEv (TMsgStore bs) (TRet tt)).

Definition target_tree (cfg payload : list Z) : ttree Z :=
  target_run tree_ops payload cfg.

(* [comment removed for export] *)
Fixpoint run_tree {A} (t : ttree A) (oracle : list bool) (next : nat) (acc : list tevent)
  : list tevent * option A :=
  match t with
  | TRet a => (rev acc, Some a)
  | TUnr => (rev (TUnreachable :: acc), None)
  | TEv e k => run_tree k oracle next (e :: acc)
  | TMallocQ n k =>
      let '(ok, oracle') := match oracle with
                            | [] => (true, [])
                            | b :: o' => (b, o')
                            end in
      let r := if ok then Some next else None in
      run_tree (k r) oracle' (S next) (TMalloc n r :: acc)
  end.

Definition target_events (cfg payload : list Z) (oracle : list bool) : list tevent :=
  let '(evs, r) := run_tree (target_tree cfg payload) oracle 0%nat [] in
  evs ++ match r with Some rc => [TReturn rc] | None => [] end.

End LexRun.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Module LexerModelTests.
Import LexRun.

(* [comment removed for export] *)
Example ex_basic :
  target_events [0] (str "[sec]" ++ [10] ++ str "key: value" ++ [10]) []
  = [TMalloc 17 (Some 0%nat);                       (* [comment removed for export] *)
     TMalloc 11 (Some 1%nat);                       (* [comment removed for export] *)
     TMalloc 4 (Some 2%nat);                        (* [comment removed for export] *)
     TFree (Some 2%nat);                            (* [comment removed for export] *)
     TMalloc 4 (Some 3%nat);                        (* [comment removed for export] *)
     TMalloc 6 (Some 4%nat);                        (* [comment removed for export] *)
     TFree (Some 3%nat); TFree (Some 4%nat);        (* [comment removed for export] *)
     TFree (Some 1%nat);                            (* [comment removed for export] *)
     TStdout [48; 10];                              (* [comment removed for export] *)
     TFree (Some 0%nat);                            (* [comment removed for export] *)
     TReturn 0].
Proof.
ltac2:(KReplay.run1 (kr_t_LexerModel ()) [] "p;1p;2p;3p;8p10014R0p4p7511100R1p101?\R2p4p710p8P0p4p76111010R3P2p4p7210p8p101@`R2p4p7201R4p10000R5p4p7201p8p101Acp4p710R6P5p4p7200R7p8P6P5p4p7210p8P6P0p4p741100p8P6P1p8P6P3p8P6P0p4p76111100R0p8P6P2p4p7200R2p8P6p101Bbp4p711R6p8P6P7p8P6P1p8P6P3p8P6P0p8P6P2p8p101Cep4p710R6P4p8P7P2p8P2P7p8P7P6p8P6P7p8P2P7p8P7P2p8P2P6p8P6P2p8g00>Dj1DTg00Ajj11Tg00FVj19Tg009Ej13Tg00Kaj28Tg01Dkj25Tg007Dj1:Tg01Ekj16Tg00=dj1;Tg00i2j37Tg01Fkj1@Tg01Gkj1?Tg00CTj2CTg01Hkj80Tg01IJj2=Tg01Ikj1>Tg01Jbj3<Tg01K?j3BTg003Zj3ATg01LKR2f2R6f1R7f0R457237p=41=74,=6p=2%D2R6g00WDR4#1R7#1R0#1#9#3g00P`R3g00U0R1'8R5'5%97R7#9#3%:1R1,83R8'5%30R0%:1R1,83R9'5%69%:1R1,83R9,50%94#1R4#3%:1,83R3'5%69%63%68g00PBR8%14#1#1#3%17#3%;8R7578R437#@%65g00XMR5#?%;2343434343434R2'CA7857g00YWR5P5g00dOR7P5P5P7P5P7G0P5P5P7P7P5P5P5P7G0P5P7P5P7P7P5P5P7G0R3P5P5P7P7P7P5P5P7G0P5P7P5P5P5P7P5P7G0g01MKR9'=3232#>P5P5P7P5P7P5P5P7G0P5P7P7P5P5P5P5P7G0P7P5P7P5P5P5P7P7G0P7P7P7P7P7P5P7P7G0P7P5P5P7P5P5P5P7G0P5P7P7P7P7P5P5P7G0P7P7P5P5P7P5P5P7G0P5P7P5P7P5P5P5P7G0?239323232723#>=<849<845<8g00Vd#;3B=A62do"). Qed.

(* [comment removed for export] *)
Example ex_empty_fail :
  target_events [1] [] [false]
  = [TMalloc 11 None;
     TStderr (precond_text EXPR_FILENAME FUNC_INIT);
     TFree None;                                    (* [comment removed for export] *)
     TStdout [48; 10];
     TMalloc 11 (Some 1%nat);
     TFree (Some 1%nat);
     TStdout [48; 10];
     TFree None;                                    (* [comment removed for export] *)
     TReturn 0].
Proof.
ltac2:(KReplay.run1 (kr_t_LexerModel ()) [] "p;1p;2p;3g00>Dj1ITg00Ajj11Tg00FVj10Tg009Ej17Tg005gj1HTg01Dkj2;Tg00=dj1:Tg01Mlj1=Tg01Ekj1<Tg01Fkj1GTg007Dj1FTg00Kaj2ETg01Gkj1DTg00CTj2BTg00i2j32Tg01K?j3ATg01Nlj2@Tg003Zj3?Tf0R0#1#7p=5%00#7p=6g00PBR1f1R2#7;20p=3A2120p=>f2R3A2120521p=9f4f3A21209213521521p=4g01LKR4?220p=CA24209243p=8%I4R3g00WDR2#1R0#0R5#0R6#7R7g00P`R8#HR9';R:%02R;#0R<#1R=#1R>#1#5R?%1;R;#1R@#1RA#6RBPB%16#6RC%0;R;#1RD#0#0%1D#6RD%0=#1R=#5RE%10R0#1#1RF#5RG%00#0R0#0RH#7RI%0;R;#1RJ#5RK%0@R@#1#6RL%0<R<#1RM#1#5RNPL%0>#5R>PC%0<#1%0@#1PDPKPL%0;R;#5R@%1ARA#6R<%6JPLPG%0F%0M%5H%15R5#0#1#0%10#5R0P0PIPGP@%6;PEPG%0=PLPGP<PEPGP?PBPB%06#0#6R6PKPLPNPLP>P6PD%:1R1,35R5,>E99@DD4D4D4D4'399E>D4D4'359G'3'3D4D4'3'3D4D4,3=39'3D4#=%<9R913A5#GR5g00U0#F,E8R8,;7%<8g00XM#D%:4'C98593838R538'B1321g00VdR2g00dO%:2327A1g01P0g01Q5'@#==8:55?3do"). Qed.

(* [comment removed for export] *)
Example ex_msg_null :
  target_events [] (str "# c" ++ [10] ++ str " oops " ++ [10]) [true; false]
  = [TMalloc 11 (Some 0%nat);
     TMalloc 11 None;
     TStderr (precond_text EXPR_FILENAME FUNC_INIT);
     TMsgStore (str "(null):2: invalid field line: no colon" ++ [0]);
     TFree None;
     TStdout [48; 10];
     TFree (Some 0%nat);
     TReturn 0].
Proof.
ltac2:(KReplay.run1 (kr_t_LexerModel ()) [] "p;1p;2p;3p;8g00>Dj1NTg00Ajj11Tg00FVj10Tg009Ej17Tg00Kaj2MTg01Dkj2BTg005gj1JTg00=dj1@Tg01Mlj1ETg00i2j34Tg01R6j1DTg01Ekj1CTg01Fkj1LTg01Gkj1ITg00CTj2HTg01Hkj82Tg01IJj29Tg01Ikj1>Tg01Jbj3<Tg01K?j3GTg01Nlj2FTg003Zj3KTf0R0#1#7p=5%00#7p=:g00PBR1f1R2#7;40p==f4R3f3R4f2R5A4120541541541p=3%74A41209415541p=8A41209415p=Ag01LKR6A4620745p=;1920,95p=?1920,95,94,93p=6%N6R3g00WDR4#1R5#0R2#0R0#7R7g00P`R8g00U0'MR9'BR:%J8R8,B7R7%04R4#0R;#1R<#1R=#1#5R>%14R4#1R?#1R@#0RA#7RBPB%10#:RC%04R4#1RD#0#0%1D#:RD%0<R<#1RE#5RF%7ERG%15R5#1#1RH#5RI%05#0R5#0RJ#7RK%04R4#1RL#5RM%0?R?#1RN#:RO%0;R;#1RP#1#5RQPO%0=#5R=PC%0;#5%0?#5R?PDPMPO%04R4#5R;%1@R@#:RC%0LPOPI%0H%0PPI%5J%12R2#0#1#0%15#5R5P5PKPIP;%:4R4PFPIPFP=%:EREPOPIPCPFPIP>PBPB%00#0#:R0PMPOPQPOP=P0PDP;PDPF%@1RF,=2R0D3D3D3D3D3D3D3C8C8'=C8D3D3D3D3C8D3#E%12R2#1P;PE%02PG%7NPGPIPDP;%0<#1PCPMPD%5NRNPIP?PDPOPMPNPIPMPDP;POPGPIP;%0AP4PMg00XMRA=41FRG9A4;C89A4ID3D3D3D3C8D3C89AMMC8#D%C81=@0#L%C9%IA%@63;3;R63;3;'Hg00YWRAPAg00dOR9P9P9PAP9P9G2P9P9P9P9P9PAP9P9G2R@PAPAP9P9P9PAPAP9G2R8g01MKRM'93?#>P@PAPAPAPAP9PAPAP9G2R4P4P9P9P9P9PAPAPAP9G2PAPAP9P9PAPAPAP9G2??@MD6#>=<109<105<1g00VdR0%@0940974A5GFg01P0g01Q5'F#EP9P9P9PAP9PAP9P9G2P9PAPAPAP9PAPAP9G2RFPAP9PAP9PAPAPAP9G2P9P9PAPAP9PAPAP9G2R0P0PAP9P9PAP9PAP9P9G2P9PAP9PAPAPAP9P9G2RIP9PAP9P9PAPAP9P9G2PIP@PAP9P9PAP9PAPAP9G2R;PFP9PAPAP9PAPAPAP9G2PAP9P9P9P9PAPAP9G2P0P;P9P9PAP9P9PAPAP9G2ROP@P9PAPAP9P9PAPAP9G2P;PAP9PAP9P9PAPAP9G2R9P0POP@P0P;PFP9PIP@PFP4P@P8P4P0A?4FMD6D6D6D6D6D6D6D6D6#>=<1G#D;;69;:75K3do"). Qed.

(* [comment removed for export] *)
Example ex_copy_fail :
  target_events [3] [65] [false] = [TMalloc 1 None; TReturn 2].
Proof.
ltac2:(KReplay.run1 (kr_t_LexerModel ()) [] "p;1p;2p;3g00>Dj1;Tg009Ej12Tg005gj17Tg01Dkj25Tg00Ajj11Tg01Gkj1:Tg00=dj13Tg00i2j30Tg00CTj26Tg00FVj14Tg01K?j38Tg003Zj39Tg01LKR0#;R1g00WDR2#2g00P`#7'5%12R3#2#:%30500500R0'6g00PBR4%42#2%34R230%13#1#1#1#4#2=042g00VdR2g00dO%323038=910do"). Qed.

End LexerModelTests.
