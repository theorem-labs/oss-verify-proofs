(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.pix_orient_fuzzer.images Require Import AsanUbsan.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AS Require Import PropExec CatExec CatSim SeqExec StoreOk AsanPopFree.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AS Require Import PropExec.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_AsanPopFreeAsan () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C45stdpp9bitvector;definitions7Z_to_bvC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordK47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00C45stdpp9bitvector;definitions9bv_eq_decC35stdpp6option=option_eq_decC35stdpp4base:decide_relK47Corelib4Init5Logic2eq01C35stdpp9decidable;bool_decideC35stdpp9decidableEbool_decide_eq_true_1K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrImgJTgt_pix_orient_fuzzer_both1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB23?AsanPopFreeAsanAasan_popfree_headC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS;AsanPopFree3PW0C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib2K52AS;AsanPopFree3PW1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS;AsanPopFree3PW2C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C69OSSVerify5KrLib2K52AS;AsanPopFree3PW3C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS;AsanPopFree3PW4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS;AsanPopFree3PW5C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS;AsanPopFree3PW6C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS;AsanPopFree3PW7C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundI47Corelib4Init5Logic3and00K46Stdlib9micromega5Tauto8GFormula04C69OSSVerify5KrLib2K52AS;AsanPopFreeDpopfree_spec_of_codeC1?~~~~~~~~~~~~~~~C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01c69OSSVerify5KrLib2K55ASB23?AsanPopFreeAsan3PF0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB23?AsanPopFreeAsan3PF1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB23?AsanPopFreeAsan3PF2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB23?AsanPopFreeAsan3PF3C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB23?AsanPopFreeAsan3PF4C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB23?AsanPopFreeAsan3PF5C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB23?AsanPopFreeAsan3PF6C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB23?AsanPopFreeAsan3PF7C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205C69OSSVerify5KrLib2K52AS;AsanPopFree@popfree_loop_runC1?~~~~~~~~~~~~~~~".  (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.

#[local] Notation ASEGS := AsanUbsan.M.loaded_segments (only parsing).

(* [comment removed for export] *)
Definition asan_popfree_head : Z := 0xa66f8.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Lemma PF0 : fetch_word ASEGS (Z_to_bv 64 asan_popfree_head) = Some PW0.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPopFreeAsan ()) [] "p;1p;2p;3p;6g0000j10Tg000Uj12Tg0013j14Tg001Vj13Tg0028j2>Tg002^j2;Tg003`j2:Tg004Bj31j15Tg004\j16Tg005Dj27Tg005aj68Tg0069j29Tg006Sj2=Tg0071j3<Tg007Y#0#0#0#0#0R0#2R1#4R2#3R3g008>%00#2g009P'>';R0g00:_,:2R431R5P3P3%53%61,72P0P4E8R4g00;YR0g00<9R2'91=54=102d3<o"). Qed.
Lemma PF1 : fetch_word ASEGS (Z_to_bv 64 (asan_popfree_head + 4)) = Some PW1.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPopFreeAsan ()) [] "p;1p;2p;3p;6g0000j10Tg000Uj12Tg0013j14Tg001Vj13Tg00<Yj1@Tg00=7j2;Tg0028j2:Tg002^j25Tg003`j26Tg004Bj31j17Tg004\j18Tg005Dj29Tg005aj6?Tg0069j2>Tg006Sj2=Tg0071j3<Tg007Y#0#0R0#0#0#0R1#2R2#4R3#3R4g008>%01#2g009P%@0';':'5R0g00=T,63R131R5P4P4%74%82,93P0P1E?R1g00;YR0g00<9R3'>1=51=103d3<o"). Qed.
Lemma PF2 : fetch_word ASEGS (Z_to_bv 64 (asan_popfree_head + 8)) = Some PW2.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPopFreeAsan ()) [] "p;1p;2p;3p;6g0000j10Tg000Uj12Tg0013j14Tg001Vj13Tg00<Yj1@Tg00=7j2;Tg0028j2:Tg002^j25Tg003`j26Tg004Bj31j17Tg004\j18Tg005Dj29Tg005aj6?Tg0069j2>Tg006Sj2=Tg0071j3<Tg007Y#0#0#0R0#0#0R1#2R2#4R3#3R4g008>%01#2g009P%@0';':'5R0g00>N,63R131R5P4P4%74%82,93P0P1E?R1g00;YR0g00<9R3'>1=51=103d3<o"). Qed.
Lemma PF3 : fetch_word ASEGS (Z_to_bv 64 (asan_popfree_head + 12)) = Some PW3.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPopFreeAsan ()) [] "p;1p;2p;3p;6g0000j10Tg000Uj12Tg0013j14Tg001Vj13Tg00?Hj1ATg00<Yj1;Tg00=7j2:Tg0028j25Tg002^j26Tg003`j27Tg004Bj31j18Tg004\j19Tg005Dj2@Tg005aj6?Tg0069j2>Tg006Sj2<Tg0071j3=Tg007YR0#0#0#0#0#0R1#2R2#4R3#3R4g008>%01#2g009P%A0#0#0#;':'5'6R0g00?m,73R131R5P4P4%84%92,@3P0P1E?R1g00;YR0g00<9R3'>1<51=103d3=o"). Qed.
Lemma PF4 : fetch_word ASEGS (Z_to_bv 64 (asan_popfree_head + 16)) = Some PW4.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPopFreeAsan ()) [] "p;1p;2p;3p;6g0000j10Tg000Uj12Tg0013j14Tg001Vj13Tg00<Yj1@Tg00=7j2;Tg0028j2:Tg002^j25Tg003`j26Tg004Bj31j17Tg004\j18Tg005Dj29Tg005aj6?Tg0069j2>Tg006Sj2=Tg0071j3<Tg007Y#0#0#0#0R0#0R1#2R2#4R3#3R4g008>%01#2g009P%@0';':'5R0g00@g,63R131R5P4P4%74%82,93P0P1E?R1g00;YR0g00<9R3'>1=51=103d3<o"). Qed.
Lemma PF5 : fetch_word ASEGS (Z_to_bv 64 (asan_popfree_head + 20)) = Some PW5.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPopFreeAsan ()) [] "p;1p;2p;3p;6g0000j10Tg000Uj12Tg0013j14Tg001Vj13Tg00?Hj1ATg00<Yj1;Tg00=7j2:Tg0028j25Tg002^j26Tg003`j27Tg004Bj31j18Tg004\j19Tg005Dj2@Tg005aj6?Tg0069j2>Tg006Sj2<Tg0071j3=Tg007Y#0R0#0#0#0#0R1#2R2#4R3#3R4g008>%01#2g009P%A0#0#0#;':'5'6R0g00Aa,73R131R5P4P4%84%92,@3P0P1E?R1g00;YR0g00<9R3'>1<51=103d3=o"). Qed.
Lemma PF6 : fetch_word ASEGS (Z_to_bv 64 (asan_popfree_head + 24)) = Some PW6.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPopFreeAsan ()) [] "p;1p;2p;3p;6g0000j10Tg000Uj12Tg0013j14Tg001Vj13Tg00?Hj1ATg00<Yj1;Tg00=7j2:Tg0028j25Tg002^j26Tg003`j27Tg004Bj31j18Tg004\j19Tg005Dj2@Tg005aj6?Tg0069j2>Tg006Sj2<Tg0071j3=Tg007YR0#0#0#0#0#0R1#2R2#4R3#3R4g008>%01#2g009P%A0#0#0#0#;':'5'6R0g00B[,73R131R5P4P4%84%92,@3P0P1E?R1g00;YR0g00<9R3'>1<51=103d3=o"). Qed.
Lemma PF7 : fetch_word ASEGS (Z_to_bv 64 (asan_popfree_head + 28)) = Some PW7.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPopFreeAsan ()) [] "p;1p;2p;3p;6g0000j10Tg000Uj11Tg0013j18Tg001Vj14Tg00?Hj13Tg00<Yj1<Tg00=7j2;Tg0028j27Tg002^j25Tg003`j26Tg004Bj32j19Tg004\j1:Tg005Dj2ATg005aj6@Tg0069j2?Tg006Sj2=Tg0071j3>Tg007YR0#0#0#0#0#0R1#1R2#8R3#4R4g008>%01#1g009P%30#3#0#0#<';'7'5R0g00CU,63R132R5P4P4%94%:2,A3P0P1E@R1g00;YR0g00<9R3'?1=51=203d3>o"). Qed.

Theorem asan_popfree_spec : popfree_spec AsanUbsan.M.loaded_segments asan_popfree_head.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPopFreeAsan ()) [] "h02Hah17__arithh24__ffh36__sat0h46__sat1h58__varmaph65__witp;1p;2p;3p;4p;7p;;g0000j11Tg00<Yj13Tg00DOj2>Tg00E7j25Tg00ESj24Tg00Eoj2MTg00FLj3BTg00G0j1@Tg00GPj1?Tg00H0j1=Tg00HNj1<Tg00Hlj1;Tg00?Hj10Tg00IWj26Tg00J:j4:Tg00Jej3OTg000Uj1NTg00KHj3LTg00Kkj7HTg00LOj2GTg0069j2ATg00M1j2CTg004Bj3DTg00M]j3ETg00N<j4FTg00=7j29Tg00Nnj27Tg00OIj7JTg00Oml;KTf0R0#1#1p=2f1R1g00Q8R2g00QWR3P3g00R7R4P0g00RWFJp=8g008>g009PR5P0g00S7g00T8g00U9g00V:g00W;g00X<g00Y=g00Z>M;Kp=Ig007YR6#1R7#3R8%27#2R7#1R9#3R:'>g00[?R;/5814;:1M8:R<,5;[[14;8R=g00[]R>AB8:1UW014;<\>^0=g00\9R=#@%?=g00\eR=#=%<=%;=R>P2P3P3P4P=%06#0#2#3R3,6=g00]C%16#0#2#0#0#2#0#0#1#0#0#0#0#0#1#2#3R6,6=R2C:,8>P=%37R7,6=9O=2g00]j16=8%N95L=C:,8>FH1G>4P0f2R>g00;YR4g00<9R9'A1C0>=D49dAE=;1CFb2b5b614361967/5<'7P0b1b3b414351957/5<'7e#Io"). Qed.

(* [comment removed for export] *)
Theorem asan_popfree_loop_run : forall regs mem rom i e c s n,
  getr regs 10 = Z_to_bv 64 i -> getr regs 11 = Z_to_bv 64 e -> getr regs 12 = Z_to_bv 64 c ->
  getr regs 21 = Z_to_bv 64 s -> getr regs 19 = Z_to_bv 64 n ->
  (0 <= i)%Z -> (i < n)%Z -> (4 * n <= e)%Z -> (e < 2 ^ 64)%Z ->
  (0 <= c)%Z -> (0 <= s)%Z -> (c + (n - i) * s < 2 ^ 64)%Z ->
  (forall d (m : nat), (0 <= d)%Z -> (d + Z.of_nat m <= 4 * (n - i))%Z ->
     RiscvSemantics.store_ok ASEGS mem (Z_to_bv 64 (e - 4 * n + d)) m = true) ->
  exists regs',
    msteps ASEGS (mkst regs (Z_to_bv 64 asan_popfree_head) mem rom)
                (mkst regs' (Z_to_bv 64 (asan_popfree_head + 32)) (pf_mem mem e c s i (Z.to_nat (n - i))) rom)
    /\ getr regs' 10 = Z_to_bv 64 n /\ getr regs' 11 = Z_to_bv 64 e
    /\ getr regs' 12 = Z_to_bv 64 (c + (n - i) * s)
    /\ getr regs' 21 = Z_to_bv 64 s /\ getr regs' 19 = Z_to_bv 64 n
    /\ getr regs' 14 = Z_to_bv 64 ((c + (n - i - 1) * s) / 16) /\ getr regs' 15 = Z_to_bv 64 (e - 4 * n)
    /\ (forall r : reg, r <> 10 -> r <> 12 -> r <> 14 -> r <> 15 -> getr regs' r = getr regs r).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPopFreeAsan ()) [] "h02Hah17__arithh24__ffh36__sat0h46__sat1h58__varmaph65__witp;1p;2p;3p;4p;7p;;g0000j11Tg00<Yj13Tg00DOj2>Tg00E7j25Tg00ESj24Tg00Eoj2MTg00FLj3BTg00G0j1@Tg00GPj1?Tg00H0j1=Tg00HNj1<Tg00Hlj1;Tg00?Hj10Tg00IWj26Tg00J:j4:Tg00Jej3OTg000Uj1NTg00KHj3LTg00Kkj7HTg00LOj2GTg0069j2ATg00M1j2CTg004Bj3DTg00M]j3ETg00N<j4FTg00=7j29Tg00Nnj27Tg00OIj7JTg00^Ql;KTf0R0#1#1p=2f1R1g00Q8R2g00QWR3P3g00R7R4P0g00RWFJp=8g008>g009PR5P0g00S7g00T8g00U9g00V:g00W;g00X<g00Y=g00Z>M;Kp=Ig007YR6#1R7#3R8%27#2R7#1R9#3R:'>g00[?R;/5814;:1M8:R<,5;[[14;8R=g00[]R>AB8:1UW014;<\>^0=g00\9R=#@%?=g00\eR=#=%<=%;=R>P2P3P3P4P=%06#0#2#3R3,6=g00]C%16#0#2#0#0#2#0#0#1#0#0#0#0#0#1#2#3R6,6=R2C:,8>P=%37R7,6=9O=2g00]j16=8%N95L=C:,8>FH1G>4P0f2R>g00;YR4g00<9R9'A1C0>=D49dAE=;1CFb2b5b614361967/5<'7P0b1b3b414351957/5<'7e#Io"). Qed.
