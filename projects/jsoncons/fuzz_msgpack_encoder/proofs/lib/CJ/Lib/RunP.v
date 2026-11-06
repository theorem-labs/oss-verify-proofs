(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_RunP () := "c69OSSVerify5KrLib2CJ3Lib4RunP:ceil_rangeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2CJ3Lib4RunP8ceil_valC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01c69OSSVerify5KrLib2CJ3Lib4RunP7CEIL_LOC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2CJ3Lib4RunP7CEIL_HIC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib7Numbers7BinNums8positive03K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1Z01c69OSSVerify5KrLib2CJ3Lib4RunP=alloc_ceilingC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2CJ3Lib4RunPCalloc_ceiling_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega5Tauto8GFormula03K47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07I47Corelib4Init5Logic4True00K46Stdlib9micromega=RingMicromega3Op205c69OSSVerify5KrLib2CJ3Lib4RunP<secret_rangeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2CJ3Lib4RunP<canary_rangeC1?~~~~~~~~~~~~~~~".
Local Open Scope Z_scope.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition CEIL_LO : Z := 0x7fff7f800000.
Definition CEIL_HI : Z := 0x7fffff800000.

Class RunP : Type := mkRunP {
  ceil_val : Z;
  ceil_range : CEIL_LO <= ceil_val <= CEIL_HI;
  secret_val : Z;
  secret_range : 0 <= secret_val < 2^64;
  canary_val : Z;
  canary_range : 0 <= canary_val < 2^64
}.

Section RUNP.
Context {RUNp : RunP}.

Definition alloc_ceiling : Z := ceil_val.

Lemma alloc_ceiling_range : 0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000.
Proof.
ltac2:(KReplay.run1 (kr_t_RunP ()) ["RUNP"] "h04__x1h11Hh27__arithh34__ffh48__varmaph55__witp;1p;2p;4p;7p;8p;3g0000j1NTg000kj1MTg001dj21Tg002@j24Tg002[j1LTg003;j1CTg003[j2@Tg0049j1?Tg004Wj1=Tg005Bj10Tg005gj1:Tg006Ej29Tg006hj2BTg007Kj48Tg0086j12Tg008[j7ATg009?j1>Tg009aj8DTg00:Ej2ETg00:gj2FTg00;Aj2GTg00;mj3HTg00<Gj3ITg00<fj4JTg00=Xj7KTf0R0#2#2p=<%20#2#2#2p=3%00#0p=6%00#0#0#0p=;%00#0#0#0#0#0#0#0p=5f1R1g00><R2g00>[R3P3g00?;R4P0g00?[FKp=7p,4RUNpR5#Ng00@;%M5R5'1g00A3,15'4g00AkR6g00BIR7#L%C71@61%?6%=6R7P2P3P3P4P7P2P3P3P4P6g00C5R2#<#3#3#3R8#0#3#3#0#6#;#5#5#:R9,96g00CZR:1B62R2C8,77P6P2P:%28#3#3#0#6#;#5#5#:R8,96C8,77FAR:%>3P:GD1E74P0f2R7g00DAR4g00DaR:'F1G07=H4:dg00EA=I61CJb3b4b5W011901108'411911118'4[^06P0P5P1O2b211951158'4eb1g00E_R5,191158'4eo"). Qed.
Lemma alloc_ceiling_lo : 0x7fff7f800000 <= alloc_ceiling.
Proof.
ltac2:(KReplay.run1 (kr_t_RunP ()) ["RUNP"] "h01Hp;1p;2g005Bj10Tg005gj16Tg001dj25Tg0086j11Tf0R0#1#1p=8%10#1#1#1p=2%00#0p=4%00#0#0#0p=7%00#0#0#0#0#0#0#0p=3g002@g00C5#8#2#2#2R1#0#2#2#0#4#7#3#3#6g00E_R2'5R3%11#2#2#0#4#7#3#3#6,52P3g00F]f1n2001000000120000000P3P0b0o"). Qed.
Lemma alloc_ceiling_hi : alloc_ceiling <= 0x7fffff800000.
Proof.
ltac2:(KReplay.run1 (kr_t_RunP ()) ["RUNP"] "h01Hp;1p;2g005Bj10Tg005gj16Tg001dj25Tg0086j11Tf0R0#1#1p=8%10#1#1#1p=2%00#0p=4%00#0#0#0p=7%00#0#0#0#0#0#0#0p=3g002@g00C5#8#2#2#2R1#0#2#2#0#4#7#3#3#6g00E_R2'5%11#2#2#0#4#7#3#3#6,52R2P2g00F]P0n2001000000120000000P2P0b0o"). Qed.
Lemma alloc_ceiling_lt63 : alloc_ceiling < 2^63.
Proof.
ltac2:(KReplay.run1 (kr_t_RunP ()) ["RUNP"] "h02Hah14__p1h24__x1h31Hh47__arithh54__ffh66__sat0h76__sat1h88__varmaph95__witp;1p;2p;3p;6p;4p;7p;8g0086j12Tg005Bj10Tg005gj14Tg001dj23Tg002@j29Tg00Gaj2ATg00HIj26Tg00Hej2>Tg00IBj3=Tg002[j1RTg003;j1QTg003[j2PTg0049j1MTg004Wj1LTg00Ifj6KTg006hj2ETg006Ej28Tg007Kj47Tg008[j7DTg009?j1CTg00JJj1BTg00Jhj3FTg009aj8GTg00:Ej2HTg00:gj2ITg00;Aj2JTg00;mj3@Tg00<Gj3?Tg00<fj4NTg00=Xj7OTf0R0#2#2#2#2p=1%00#0p=;%00#0#0#0p=<%00#0#0#0#0#0#0#0p=5f1R1g00><R2g00>[R3P3g00?;R4P0g00?[FOp=:g00F]g00C5R5#2#1R6#2#1#1R7#0#1#1#0#;#<#5#5#4g00E_R8'3R9%27#1#1#0#;#<#5#5#4R7,38'9%05#4R:%46R;'Ag00EAR</6:13<;1>:;R=,6<[[13<:R>g00KKR?A=:;1UW013<=\?^0>p-0R>g00AkR?g00BIR;#R%Q;1P?1%M?%L?R;P2P3P3P4P;P2P3P3P4P;P2P3P3P4f3R2EKP?1E?5R5g00CZ18?7C7,:;FD%C3P?P5g00Kg18?:%B65F?C7,:;GG1H;4P0f2R;g00DAR4g00DaR6'I1J0;=@46dA??<1CNb5b8b9W2W11307,91161=[^2?^1>P0P9P8P2O3b4b6b7b3o"). Qed.
Lemma alloc_ceiling_pos : 0 < alloc_ceiling.
Proof.
ltac2:(KReplay.run1 (kr_t_RunP ()) ["RUNP"] "h04__p1h14__x1h21Hh37__arithh44__ffh58__varmaph65__witp;1p;2p;4p;6p;7p;8p;3g005Bj10Tg005gj17Tg001dj24Tg0086j11Tg002@j2:Tg002[j1>Tg003;j1=Tg003[j2<Tg0049j1MTg004Wj1LTg006Ej28Tg006hj2ITg007Kj49Tg00Ifj6FTg008[j7ETg009?j1CTg009aj8BTg00:Ej2ATg00:gj2DTg00;Aj2@Tg00;mj3GTg00<Gj3HTg00<fj4?Tg00HIj2JTg00=Xj7KTf0R0#1#1p=N%10#1#1#1p=2%00#0p=5%00#0#0#0p=;%00#0#0#0#0#0#0#0p=3f1R1g00><R2g00>[R3P3g00?;R4P0g00?[FKp=6g00F]g00C5R5#N#2#2#2R6#0#2#2#0#5#;#3#3#7R7g00E_R8'4%16#2#2#0#5#;#3#3#7,48R6':p-0R9g00AkR:g00BIR;#>%=;1<:1%M:%L:R;P2P3P3P4P;P2P3P3P4P:18:7g00CZ1I:5R5C9,6;P;P2P3P3P4f3EFFE%C3P:g00EAR3,8:g00KgP5C9,6;GB1A;4P0f2R;g00DAR4g00DaR5'D1@0;=G45dAH:31C?b4b5b6W1W01470/:11J31[^1:^09P0P6P8P1O3b3b2o"). Qed.
Lemma secret_val_range : 0 <= secret_val < 2^64.
Proof.
ltac2:(KReplay.run1 (kr_t_RunP ()) ["RUNP"] "p;1g00LNj10Tp,4RUNp#0o"). Qed.
Lemma canary_val_range : 0 <= canary_val < 2^64.
Proof.
ltac2:(KReplay.run1 (kr_t_RunP ()) ["RUNP"] "p;1g00MKj10Tp,4RUNp#0o"). Qed.

End RUNP.

Lemma alloc_ceiling_mkRunP : forall c Hc s Hs k Hk, @alloc_ceiling (mkRunP c Hc s Hs k Hk) = c.
Proof.
ltac2:(KReplay.run1 (kr_t_RunP ()) [] "h02Hch12Hkh22Hsh31ch41kh51sp;2p;1g001dj21Tg002@j23Tg005Bj10Tg005gj12Tg00Hej26Tg00HIj25Tg00:gj24Tg00AkR0g00@;f0R1'1g00A3,11'3g00EA/11g00C5#0R2#2%02#0#0#0#0#2'6,51'3R1f5,40X11X40W2X50W0W3o"). Qed.

(* [comment removed for export] *)
Ltac fix_runp :=
  try (let i := constr:(_ : RunP) in
       repeat match goal with
              | |- context [?R] => is_evar R; lazymatch type of R with RunP => unify R i end
              end).
(* [comment removed for export] *)
Ltac pose_ceil :=
  fix_runp;
  lazymatch goal with
  | _ : _ <= alloc_ceiling <= _ |- _ => idtac
  | _ => let H := fresh "CEIL_RANGE__" in pose proof alloc_ceiling_range as H
  end.
(* [comment removed for export] *)
Ltac pose_secret :=
  fix_runp;
  lazymatch goal with
  | _ : 0 <= secret_val < _ |- _ => idtac
  | _ => let H := fresh "SECRET_RANGE__" in pose proof secret_val_range as H
  end.
Ltac pose_canary :=
  fix_runp;
  lazymatch goal with
  | _ : 0 <= canary_val < _ |- _ => idtac
  | _ => let H := fresh "CANARY_RANGE__" in pose proof canary_val_range as H
  end.
