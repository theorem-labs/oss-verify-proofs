(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk AsanPopFree.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_AsanPopFreeAsanK () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C45stdpp9bitvector;definitions7Z_to_bvC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordK47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00C45stdpp9bitvector;definitions9bv_eq_decC35stdpp6option=option_eq_decC35stdpp4base:decide_relK47Corelib4Init5Logic2eq01C35stdpp9decidable;bool_decideC35stdpp9decidableEbool_decide_eq_true_1K47Corelib7Numbers7BinNums8positive03C79OSSVerify8jsonconsCfuzz_ubjson_encoder6images4Asan1M?loaded_segmentsC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@AsanPopFreeAsanKAasan_popfree_headC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;AsanPopFree3PW0C13~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;AsanPopFree3PW1C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;AsanPopFree3PW2C13~~~K47Corelib7Numbers7BinNums8positive01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;AsanPopFree3PW3C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;AsanPopFree3PW4C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;AsanPopFree3PW5C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;AsanPopFree3PW6C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;AsanPopFree3PW7C13~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundI47Corelib4Init5Logic3and00K46Stdlib9micromega5Tauto8GFormula04C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;AsanPopFreeDpopfree_spec_of_codeC13~~~C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@AsanPopFreeAsanK>asanreflect_fxC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@AsanPopFreeAsanK3PF0C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@AsanPopFreeAsanK3PF1C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@AsanPopFreeAsanK3PF2C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@AsanPopFreeAsanK3PF3C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@AsanPopFreeAsanK3PF4C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@AsanPopFreeAsanK3PF5C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@AsanPopFreeAsanK3PF6C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@AsanPopFreeAsanK3PF7C13~~~K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;AsanPopFree@popfree_loop_runC13~~~".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

#[local] Notation ASEGS0 := Asan.M.loaded_segments (only parsing).

(* [comment removed for export] *)
Definition asan_popfree_head : Z := 0x58238.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Lemma PF0 : fetch_word ASEGS0 (Z_to_bv 64 asan_popfree_head) = Some PW0.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPopFreeAsanK ()) [] "p;1p;2p;3p;6g0000j10Tg000Uj12Tg0013j14Tg001Vj13Tg0028j2>Tg002^j2;Tg003`j2:Tg004Bj31j15Tg004\j16Tg005Dj27Tg005aj68Tg0069j29Tg006Sj2=Tg0071j3<Tg007Y#0#0#0#0#0R0#2R1#4R2#3R3g008>%00#2g009K'>';R0g00:h,:2R431R5P3P3%53%61,72P0P4E8R4g00<2R0g00<RR2'91=54=102d3<o"). Qed.
Lemma PF1 : fetch_word ASEGS0 (Z_to_bv 64 (asan_popfree_head + 4)) = Some PW1.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPopFreeAsanK ()) [] "p;1p;2p;3p;6g0000j10Tg000Uj12Tg0013j14Tg001Vj13Tg00=2j1@Tg00=Pj2;Tg0028j2:Tg002^j25Tg003`j26Tg004Bj31j17Tg004\j18Tg005Dj29Tg005aj6?Tg0069j2>Tg006Sj2=Tg0071j3<Tg007Y#0#0R0#0#0#0R1#2R2#4R3#3R4g008>%01#2g009K%@0';':'5R0g00=m,63R131R5P4P4%74%82,93P0P1E?R1g00<2R0g00<RR3'>1=51=103d3<o"). Qed.
Lemma PF2 : fetch_word ASEGS0 (Z_to_bv 64 (asan_popfree_head + 8)) = Some PW2.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPopFreeAsanK ()) [] "p;1p;2p;3p;6g0000j10Tg000Uj12Tg0013j14Tg001Vj13Tg00=2j1@Tg00=Pj2;Tg0028j2:Tg002^j25Tg003`j26Tg004Bj31j17Tg004\j18Tg005Dj29Tg005aj6?Tg0069j2>Tg006Sj2=Tg0071j3<Tg007Y#0#0#0R0#0#0R1#2R2#4R3#3R4g008>%01#2g009K%@0';':'5R0g00?7,63R131R5P4P4%74%82,93P0P1E?R1g00<2R0g00<RR3'>1=51=103d3<o"). Qed.
Lemma PF3 : fetch_word ASEGS0 (Z_to_bv 64 (asan_popfree_head + 12)) = Some PW3.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPopFreeAsanK ()) [] "p;1p;2p;3p;6g0000j10Tg000Uj12Tg0013j14Tg001Vj13Tg00@Aj1ATg00=2j1;Tg00=Pj2:Tg0028j25Tg002^j26Tg003`j27Tg004Bj31j18Tg004\j19Tg005Dj2@Tg005aj6?Tg0069j2>Tg006Sj2<Tg0071j3=Tg007YR0#0#0#0#0#0R1#2R2#4R3#3R4g008>%01#2g009K%A0#0#0#;':'5'6R0g00@f,73R131R5P4P4%84%92,@3P0P1E?R1g00<2R0g00<RR3'>1<51=103d3=o"). Qed.
Lemma PF4 : fetch_word ASEGS0 (Z_to_bv 64 (asan_popfree_head + 16)) = Some PW4.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPopFreeAsanK ()) [] "p;1p;2p;3p;6g0000j10Tg000Uj12Tg0013j14Tg001Vj13Tg00=2j1@Tg00=Pj2;Tg0028j2:Tg002^j25Tg003`j26Tg004Bj31j17Tg004\j18Tg005Dj29Tg005aj6?Tg0069j2>Tg006Sj2=Tg0071j3<Tg007Y#0#0#0#0R0#0R1#2R2#4R3#3R4g008>%01#2g009K%@0';':'5R0g00B0,63R131R5P4P4%74%82,93P0P1E?R1g00<2R0g00<RR3'>1=51=103d3<o"). Qed.
Lemma PF5 : fetch_word ASEGS0 (Z_to_bv 64 (asan_popfree_head + 20)) = Some PW5.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPopFreeAsanK ()) [] "p;1p;2p;3p;6g0000j10Tg000Uj12Tg0013j14Tg001Vj13Tg00@Aj1ATg00=2j1;Tg00=Pj2:Tg0028j25Tg002^j26Tg003`j27Tg004Bj31j18Tg004\j19Tg005Dj2@Tg005aj6?Tg0069j2>Tg006Sj2<Tg0071j3=Tg007Y#0R0#0#0#0#0R1#2R2#4R3#3R4g008>%01#2g009K%A0#0#0#;':'5'6R0g00C:,73R131R5P4P4%84%92,@3P0P1E?R1g00<2R0g00<RR3'>1<51=103d3=o"). Qed.
Lemma PF6 : fetch_word ASEGS0 (Z_to_bv 64 (asan_popfree_head + 24)) = Some PW6.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPopFreeAsanK ()) [] "p;1p;2p;3p;6g0000j10Tg000Uj12Tg0013j14Tg001Vj13Tg00@Aj1ATg00=2j1;Tg00=Pj2:Tg0028j25Tg002^j26Tg003`j27Tg004Bj31j18Tg004\j19Tg005Dj2@Tg005aj6?Tg0069j2>Tg006Sj2<Tg0071j3=Tg007YR0#0#0#0#0#0R1#2R2#4R3#3R4g008>%01#2g009K%A0#0#0#0#;':'5'6R0g00DD,73R131R5P4P4%84%92,@3P0P1E?R1g00<2R0g00<RR3'>1<51=103d3=o"). Qed.
Lemma PF7 : fetch_word ASEGS0 (Z_to_bv 64 (asan_popfree_head + 28)) = Some PW7.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPopFreeAsanK ()) [] "p;1p;2p;3p;6g0000j10Tg000Uj11Tg0013j18Tg001Vj14Tg00@Aj13Tg00=2j1<Tg00=Pj2;Tg0028j27Tg002^j25Tg003`j26Tg004Bj32j19Tg004\j1:Tg005Dj2ATg005aj6@Tg0069j2?Tg006Sj2=Tg0071j3>Tg007YR0#0#0#0#0#0R1#1R2#8R3#4R4g008>%01#1g009K%30#3#0#0#<';'7'5R0g00EN,63R132R5P4P4%94%:2,A3P0P1E@R1g00<2R0g00<RR3'?1=51=203d3>o"). Qed.

Theorem asan_popfree_spec : popfree_spec Asan.M.loaded_segments asan_popfree_head.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPopFreeAsanK ()) [] "h02Hah17__arithh24__ffh36__sat0h46__sat1h58__varmaph65__witp;1p;2p;3p;4p;7p;<g0000j12Tg00=2j13Tg00FXj2>Tg00G@j25Tg00G\j24Tg00H8j2MTg00HUj3BTg00I9j1@Tg00IYj1?Tg00J9j1=Tg00JWj1<Tg00K5j1;Tg00@Aj10Tg00K`j26Tg00LCj4:Tg00Lnj3OTg000Uj1NTg00MQj3LTg00N4j7HTg00NXj2GTg0069j2ATg00O:j2CTg004Bj3DTg00Ofj3ETg00PEj4FTg00=Pj29Tg00Q7j27Tg00QRj7JTg00R6l<KTf0R0#2#2p=1f1R1g00SQR2g00T0R3P3g00TPR4P0g00U0FJp=8g00UPg008>g009KR5P0g00Vjg00X9g00YHg00ZWg00[fg00]5g00^Dg00_SM<Kp=Ig007YR6#2R7#3R8%17#1R9#2R:#3R;'>g00`bR</5814<;1M8;R=,5<[[14<8R>g00a@R?AB8;1UW014<=\?^0>g00a\R>#@%?>g00bHR>#=%<>%;>R?P2P3P3P4P>%06#0#1#3R6,6>g00bf%07#0#1#1#1#0#0#0#0#2#0#2#1#3R7,6>R3C:,8?P>%39R9,6>9O>3g00cM16>8%N:5L>C:,8?FH1G?4P0f2R?g00<2R4g00<RR:'A1C0?=D4:dAE><1CFb2b5b614671979/5='7P0b1b3b414651959/5='7e#Io"). Qed.

(* [comment removed for export] *)
Theorem asan_popfree_loop_run : forall regs mem rom i e c s n,
  getr regs 10 = Z_to_bv 64 i -> getr regs 11 = Z_to_bv 64 e -> getr regs 12 = Z_to_bv 64 c ->
  getr regs 21 = Z_to_bv 64 s -> getr regs 19 = Z_to_bv 64 n ->
  (0 <= i)%Z -> (i < n)%Z -> (4 * n <= e)%Z -> (e < 2 ^ 64)%Z ->
  (0 <= c)%Z -> (0 <= s)%Z -> (c + (n - i) * s < 2 ^ 64)%Z ->
  (forall d (m : nat), (0 <= d)%Z -> (d + Z.of_nat m <= 4 * (n - i))%Z ->
     RiscvSemantics.store_ok ASEGS0 mem (Z_to_bv 64 (e - 4 * n + d)) m = true) ->
  exists regs',
    msteps ASEGS0 (mkst regs (Z_to_bv 64 asan_popfree_head) mem rom)
                (mkst regs' (Z_to_bv 64 (asan_popfree_head + 32)) (pf_mem mem e c s i (Z.to_nat (n - i))) rom)
    /\ getr regs' 10 = Z_to_bv 64 n /\ getr regs' 11 = Z_to_bv 64 e
    /\ getr regs' 12 = Z_to_bv 64 (c + (n - i) * s)
    /\ getr regs' 21 = Z_to_bv 64 s /\ getr regs' 19 = Z_to_bv 64 n
    /\ getr regs' 14 = Z_to_bv 64 ((c + (n - i - 1) * s) / 16) /\ getr regs' 15 = Z_to_bv 64 (e - 4 * n)
    /\ (forall r : reg, r <> 10 -> r <> 12 -> r <> 14 -> r <> 15 -> getr regs' r = getr regs r).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPopFreeAsanK ()) [] "h02Hah17__arithh24__ffh36__sat0h46__sat1h58__varmaph65__witp;1p;2p;3p;4p;7p;<g0000j12Tg00=2j13Tg00FXj2>Tg00G@j25Tg00G\j24Tg00H8j2MTg00HUj3BTg00I9j1@Tg00IYj1?Tg00J9j1=Tg00JWj1<Tg00K5j1;Tg00@Aj10Tg00K`j26Tg00LCj4:Tg00Lnj3OTg000Uj1NTg00MQj3LTg00N4j7HTg00NXj2GTg0069j2ATg00O:j2CTg004Bj3DTg00Ofj3ETg00PEj4FTg00=Pj29Tg00Q7j27Tg00QRj7JTg00d4l<KTf0R0#2#2p=1f1R1g00SQR2g00T0R3P3g00TPR4P0g00U0FJp=8g00UPg008>g009KR5P0g00Vjg00X9g00YHg00ZWg00[fg00]5g00^Dg00_SM<Kp=Ig007YR6#2R7#3R8%17#1R9#2R:#3R;'>g00`bR</5814<;1M8;R=,5<[[14<8R>g00a@R?AB8;1UW014<=\?^0>g00a\R>#@%?>g00bHR>#=%<>%;>R?P2P3P3P4P>%06#0#1#3R6,6>g00bf%07#0#1#1#1#0#0#0#0#2#0#2#1#3R7,6>R3C:,8?P>%39R9,6>9O>3g00cM16>8%N:5L>C:,8?FH1G?4P0f2R?g00<2R4g00<RR:'A1C0?=D4:dAE><1CFb2b5b614671979/5='7P0b1b3b414651959/5='7e#Io"). Qed.
