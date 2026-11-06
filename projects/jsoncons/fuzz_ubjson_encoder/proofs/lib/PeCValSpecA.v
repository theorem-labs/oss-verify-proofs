(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PropExec StoreOk ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceAEx L5Defs L5Core
     L5KnA L5LazyA L5DefsA L5CoreA PmLayout PmLayoutA PmModel PmStatics PmStaticsA PmSpecs PmSpecsA PeCLayout.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require LibIfaceAB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_PeCValSpecA () := "c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;PeCValSpecA6PECVSAAvalidate_fun_specC13~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA6vml_ofC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA6ri_invC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4asan7L5CoreA4L5CA9amodel_okC13~~~K47Corelib4Init9Datatypes4list01C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PmSpecsA5PMSPA6entryAC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PmSpecsA5PMSPA7ffroomAC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PmSpecsA5PMSPA5ffrsAC13~~~K47Corelib7Numbers7BinNums1Z02K45stdpp9bitvector;definitions2bv01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec4getrC13~~~C45stdpp9bitvector;definitions7Z_to_bvI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00I47Corelib4Init5Logic2or00C56Stdlib6ZArith6BinInt1Z3addC89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Defs2L57definedC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA4aaccC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA4ahidC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA1SC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PmSpecsA5PMSPA6pm_scrC13~~~C56Stdlib6ZArith6BinInt1Z3subC89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:PmStaticsA5PMSTA8base_okAC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Defs2L58bytes_atC13~~~C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natI47Corelib5Lists7ListDef6Forall00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9HeapIface>regs_preservedC13~~~K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes4list02C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Defs2L59frame_butC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7StoreOk9mem_growsC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA8model_rtC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Defs4SCFGC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PmSpecsA5PMSPA3cfgC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SpinAlg9srealizesC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec6UbjRef:utf8_validC13~~~C47Corelib4Init5Logic3iffI47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01I79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7FPState00C13~~~K47Corelib7Numbers7BinNums8positive03I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg4TSetC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA6fframeC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9HeapIface6creditC13~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00K47Corelib4Init5Logic4True01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib5BMode;bm_off_instC13~~~K47Corelib4Init9Datatypes4bool01".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PECVSA.
Section Specs.
Context {SCFG_P : ScfgP}.
Variable segs : list Segment.
Variable A : pm_addrs.
Variable L : asan_layout.
Variable ar : asan_run.
Variable HI : asan_iface.

Abbreviation entryA := (PMSPA.entryA A L ar).
Abbreviation ffroomA := PMSPA.ffroomA.
Abbreviation ffrsA := PMSPA.ffrsA.
Abbreviation pm_scr := PMSPA.pm_scr.
Abbreviation cfg := (@PMSPA.cfg segs).

Definition validate_fun_spec (pc : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (p n sp r : Z) (l : list Z),
    ri_inv HI LB FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] -> entryA R M sp r 0 -> ffroomA 0 FF LK -> ffrsA FF sp ->
    getr R 10%bv = Z_to_bv 64 p -> getr R 11%bv = Z_to_bv 64 n -> 0 <= n < 2 ^ 26 -> 0 <= p -> (n = 0 \/ 0 < p) -> p + n <= 2 ^ 47 ->
    L5.defined M p n -> aacc M p n -> (forall a, p <= a < p + n -> ahid Aw model (Z_to_bv 64 a) = false /\ ahid Aw model (Z_to_bv 64 (S a)) = false) ->
    (n = 0 \/ sp <= p \/ p + n <= sp - pm_scr 0) ->
    PMSTA.base_okA segs A M ->
    L5.bytes_at segs M p l -> Z.of_nat (length l) = n -> Forall (fun b => 0 <= b < 256) l ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (v : Z),
        regs_preserved R R' -> L5.frame_but [(sp - pm_scr 0, pm_scr 0)] M M' -> mem_grows M M' -> model_rt model model' -> L5CA.amodel_ok Aw model' ->
        ri_inv HI LB FF LK cr Aw M' (vml_of model') ->
        getr R' 11%bv = Z_to_bv 64 v -> 0 <= v < 7 -> (v = 0 <-> utf8_valid l = true) ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R pc M model) K.

(* [comment removed for export] *)
Lemma scan_of_fun pc : validate_fun_spec pc ->
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (p n sp r : Z) (l : list Z),
    ri_inv HI LB FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] -> entryA R M sp r 0 -> ffroomA 0 FF LK -> ffrsA FF sp ->
    getr R 10%bv = Z_to_bv 64 p -> getr R 11%bv = Z_to_bv 64 n -> 0 <= n < 2 ^ 26 -> 0 <= p -> (n = 0 \/ 0 < p) -> p + n <= 2 ^ 47 ->
    L5.defined M p n -> aacc M p n -> (forall a, p <= a < p + n -> ahid Aw model (Z_to_bv 64 a) = false /\ ahid Aw model (Z_to_bv 64 (S a)) = false) ->
    (n = 0 \/ sp <= p \/ p + n <= sp - pm_scr 0) ->
    PMSTA.base_okA segs A M ->
    L5.bytes_at segs M p l -> Z.of_nat (length l) = n -> Forall (fun b => 0 <= b < 256) l ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model),
        regs_preserved R R' -> L5.frame_but [(sp - pm_scr 0, pm_scr 0)] M M' -> mem_grows M M' -> model_rt model model' -> L5CA.amodel_ok Aw model' ->
        ri_inv HI LB FF LK cr Aw M' (vml_of model') ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R pc M model) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PeCValSpecA ()) ["Specs"] "h02M'h12R'h23fx'h36model'h42pch52Awh62FFh72H1h83H10h93H11h:3H12h;3H13h<3H14h=3H15h>3H16h?3H17h@3H18hA3H19hB2H2hC3H20hD2H3hE2H4hF2H5hG2H6hH2H7hI2H8hJ2H9hK1KhL4KONThM2LBhN2LKhO1MhP2P1hQ2P2hR2P3hS2P4hT2P5hU2P6hV1RhW2VFhX2_HhY3_H0hZ3_H1h[1ah\1bh]2crh^2fxh_1lh`5modelha1nhb1phc1rhd2sphe1vp;1p;2p;8p;3p;4p;6p;5g0000j1aTg001Oj10Tg0024j13Tg002Yj18Tg0037j1LTg003Zj2YTg004Fj1WTg004hj2VTg005Hj1>Tg005hj1@Tg0074j8;Tg008@j2<Tg009Vj1ITg00:6j8`Tg00;Fj3_Tg00<Wj2]Tg00=fj14Tg00>Dj3GTg00>gj2:Tg00?oj27Tg00@Uj31Tg00@oj22Tg00AKj2DTg00Ahj25Tg00BDj26Tg00B_j2?Tg00C9j2CTg00CVj3UTg00Dbj3TTg00Elj3ATg00G6j1PTg00H=j1OTg00IMj29Tg00Ijj3NTg00K>j4QTg00LKj2RTg00Lkj1MTg00MKj3STg00Mlj2BTg00O?j4KTg00O_j3ETg00P?j3FTg00QMj2HTg00RYj2JTg00Sgj1^Tg00Tmj6\Tg00V:j5ZTg00WFj1[Tg00XWj2XTg00Y0R0f0R1g00YNR231p==%a1g00YlR3g00[9R4#0R5#3R6#8R7%05#0R8#0#0#0R9#8R:#LR;'YR<%88#L#W\;R8g00[^R=g00\T1V00R>#>R?g00]\#>R@g00^h%>0p,2HIRAf9RBf8RCf7RDf5REf6RFf<RGf;RH#@G;1<DGPGg00`3#IO1p,1ARIp,1Lp,2arf@RJf?RKPEf4RLP2G`A_2GHf=RM/]DfCRN%06#4g00`iRO5G7':f:RP,7:RQ51;fDRR%36R6#4=G7ORO':=1;Q122H%45R5%34R4#0#3#0#4'D,5H'6122M%=Mf>RQ,52'?1CKQ%36#3#4,D5'2fHR5?UJKfIR6fAR7;TJ12N1fBRS,CNRT,51'6g00aERUfFRVfKRWf1RX,7:3Ag00aeRY31%PX,7:9AVW=1UY'6[^[0%=S127N%O2RY,97,2T'?'?p,4segsRTfLRZ7NIPTfMRIfER[P7CQ1R0S#M=10[1221%09#0#4,51'6X\0=S0NfUR9f2R\'BP0P019WYPYCK%I>R]5E>?F9\fVR^f3R_'H1J^_fRR`/<LPAP^P9fTRaP`fSRbPF%@EG;g00bEPTp,6SCFG_P#^PTPBPCfORTPDPFE\fXRcDZ[[[[[[^3=^08^1<^23PaPbP`fQfPPTfNPIPZPWfJP6P5fGPVP[PRPNPSP7PJPKPQPMPGPHPPPBPCPDPFPEPLP_P\PXfWRX/B_P0P019IYPYCK=E>]?FX_1HcL1JcL1<aEPAPcPXP^PaP9PD%@FG;1:BO17:F51;122D%34#4,5D'6%=C%[`g00cQ51U'XPQPMPGPHPPPCPDPFPEPLP_O:WZWYWXWUWTWSWRWQWPXe0X3=X08X1<X23OTWLWCWAW@W?W>W=W<W;W:W9W8WJWIWHWGWFWEWDWBW7W_Xc0Xd0Xa0Xb0W]X5?XN@W6WMWKW`WOWVW^WWX40P1O1X40o"). Qed.
End Specs.
End PECVSA.
