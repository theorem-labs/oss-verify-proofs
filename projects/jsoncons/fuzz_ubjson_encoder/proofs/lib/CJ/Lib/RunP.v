(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_RunP () := "c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4RunP:ceil_rangeC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4RunP8ceil_valC13~~~C56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4RunP7CEIL_LOC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4RunP7CEIL_HIC13~~~I47Corelib7Numbers7BinNums1Z00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib7Numbers7BinNums8positive03K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1Z01c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4RunP=alloc_ceilingC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4RunPCalloc_ceiling_rangeC13~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega5Tauto8GFormula03K47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07I47Corelib4Init5Logic4True00K46Stdlib9micromega=RingMicromega3Op205c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4RunP<secret_rangeC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4RunP<canary_rangeC13~~~".
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
ltac2:(KReplay.run1 (kr_t_RunP ()) ["RUNP"] "h04__x1h11Hh27__arithh34__ffh48__varmaph55__witp;1p;2p;4p;7p;8p;3g0000j1NTg001Aj1MTg002Pj21Tg002lj24Tg003Gj1LTg003gj1CTg004Gj2@Tg004ej1?Tg005Cj1=Tg005nj10Tg006Sj1:Tg0071j29Tg007Tj2BTg0087j48Tg008bj12Tg009Gj7ATg009kj1>Tg00:Mj8DTg00;1j2ETg00;Sj2FTg00;mj2GTg00<Yj3HTg00=3j3ITg00=Rj4JTg00>Dj7KTf0R0#2#2p=<%20#2#2#2p=3%00#0p=6%00#0#0#0p=;%00#0#0#0#0#0#0#0p=5f1R1g00>hR2g00?GR3P3g00?gR4P0g00@GFKp=7p,4RUNpR5#Ng00@g%M5R5'1g00B5,15'4g00CCR6g00CaR7#L%C71@61%?6%=6R7P2P3P3P4P7P2P3P3P4P6g00DMR2#<#3#3#3R8#0#3#3#0#6#;#5#5#:R9,96g00E2R:1B62R2C8,77P6P2P:%28#3#3#0#6#;#5#5#:R8,96C8,77FAR:%>3P:GD1E74P0f2R7g00EYR4g00F9R:'F1G07=H4:dg00FY=I61CJb3b4b5W011901108'411911118'4[^06P0P5P1O2b211951158'4eb1g00G7R5,191158'4eo"). Qed.
Lemma alloc_ceiling_lo : 0x7fff7f800000 <= alloc_ceiling.
Proof.
ltac2:(KReplay.run1 (kr_t_RunP ()) ["RUNP"] "h01Hp;1p;2g005nj10Tg006Sj16Tg002Pj25Tg008bj11Tf0R0#1#1p=8%10#1#1#1p=2%00#0p=4%00#0#0#0p=7%00#0#0#0#0#0#0#0p=3g002lg00DM#8#2#2#2R1#0#2#2#0#4#7#3#3#6g00G7R2'5R3%11#2#2#0#4#7#3#3#6,52P3g00HKf1n2001000000120000000P3P0b0o"). Qed.
Lemma alloc_ceiling_hi : alloc_ceiling <= 0x7fffff800000.
Proof.
ltac2:(KReplay.run1 (kr_t_RunP ()) ["RUNP"] "h01Hp;1p;2g005nj10Tg006Sj16Tg002Pj25Tg008bj11Tf0R0#1#1p=8%10#1#1#1p=2%00#0p=4%00#0#0#0p=7%00#0#0#0#0#0#0#0p=3g002lg00DM#8#2#2#2R1#0#2#2#0#4#7#3#3#6g00G7R2'5%11#2#2#0#4#7#3#3#6,52R2P2g00HKP0n2001000000120000000P2P0b0o"). Qed.
Lemma alloc_ceiling_lt63 : alloc_ceiling < 2^63.
Proof.
ltac2:(KReplay.run1 (kr_t_RunP ()) ["RUNP"] "h02Hah14__p1h24__x1h31Hh47__arithh54__ffh66__sat0h76__sat1h88__varmaph95__witp;1p;2p;3p;6p;4p;7p;8g008bj12Tg005nj10Tg006Sj14Tg002Pj23Tg002lj29Tg00Iej2ATg00JMj26Tg00Jij2>Tg00KFj3=Tg003Gj1RTg003gj1QTg004Gj2PTg004ej1MTg005Cj1LTg00Kjj6KTg007Tj2ETg0071j28Tg0087j47Tg009Gj7DTg009kj1CTg00LNj1BTg00Llj3FTg00:Mj8GTg00;1j2HTg00;Sj2ITg00;mj2JTg00<Yj3@Tg00=3j3?Tg00=Rj4NTg00>Dj7OTf0R0#2#2#2#2p=1%00#0p=;%00#0#0#0p=<%00#0#0#0#0#0#0#0p=5f1R1g00>hR2g00?GR3P3g00?gR4P0g00@GFOp=:g00HKg00DMR5#2#1R6#2#1#1R7#0#1#1#0#;#<#5#5#4g00G7R8'3R9%27#1#1#0#;#<#5#5#4R7,38'9%05#4R:%46R;'Ag00FYR</6:13<;1>:;R=,6<[[13<:R>g00MOR?A=:;1UW013<=\?^0>p-0R>g00CCR?g00CaR;#R%Q;1P?1%M?%L?R;P2P3P3P4P;P2P3P3P4P;P2P3P3P4f3R2EKP?1E?5R5g00E218?7C7,:;FD%C3P?P5g00Mk18?:%B65F?C7,:;GG1H;4P0f2R;g00EYR4g00F9R6'I1J0;=@46dA??<1CNb5b8b9W2W11307,91161=[^2?^1>P0P9P8P2O3b4b6b7b3o"). Qed.
Lemma alloc_ceiling_pos : 0 < alloc_ceiling.
Proof.
ltac2:(KReplay.run1 (kr_t_RunP ()) ["RUNP"] "h04__p1h14__x1h21Hh37__arithh44__ffh58__varmaph65__witp;1p;2p;4p;6p;7p;8p;3g005nj10Tg006Sj17Tg002Pj24Tg008bj11Tg002lj2:Tg003Gj1>Tg003gj1=Tg004Gj2<Tg004ej1MTg005Cj1LTg0071j28Tg007Tj2ITg0087j49Tg00Kjj6FTg009Gj7ETg009kj1CTg00:Mj8BTg00;1j2ATg00;Sj2DTg00;mj2@Tg00<Yj3GTg00=3j3HTg00=Rj4?Tg00JMj2JTg00>Dj7KTf0R0#1#1p=N%10#1#1#1p=2%00#0p=5%00#0#0#0p=;%00#0#0#0#0#0#0#0p=3f1R1g00>hR2g00?GR3P3g00?gR4P0g00@GFKp=6g00HKg00DMR5#N#2#2#2R6#0#2#2#0#5#;#3#3#7R7g00G7R8'4%16#2#2#0#5#;#3#3#7,48R6':p-0R9g00CCR:g00CaR;#>%=;1<:1%M:%L:R;P2P3P3P4P;P2P3P3P4P:18:7g00E21I:5R5C9,6;P;P2P3P3P4f3EFFE%C3P:g00FYR3,8:g00MkP5C9,6;GB1A;4P0f2R;g00EYR4g00F9R5'D1@0;=G45dAH:31C?b4b5b6W1W01470/:11J31[^1:^09P0P6P8P1O3b3b2o"). Qed.
Lemma secret_val_range : 0 <= secret_val < 2^64.
Proof.
ltac2:(KReplay.run1 (kr_t_RunP ()) ["RUNP"] "p;1g00NRj10Tp,4RUNp#0o"). Qed.
Lemma canary_val_range : 0 <= canary_val < 2^64.
Proof.
ltac2:(KReplay.run1 (kr_t_RunP ()) ["RUNP"] "p;1g00Oej10Tp,4RUNp#0o"). Qed.

End RUNP.

Lemma alloc_ceiling_mkRunP : forall c Hc s Hs k Hk, @alloc_ceiling (mkRunP c Hc s Hs k Hk) = c.
Proof.
ltac2:(KReplay.run1 (kr_t_RunP ()) [] "h02Hch12Hkh22Hsh31ch41kh51sp;2p;1g002Pj21Tg002lj23Tg005nj10Tg006Sj12Tg00Jij26Tg00JMj25Tg00;Sj24Tg00CCR0g00@gf0R1'1g00B5,11'3g00FY/11g00DM#0R2#2%02#0#0#0#0#2'6,51'3R1f5,40X11X40W2X50W0W3o"). Qed.

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
