(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceAEx L5Defs L5Core
     L5KnA L5LazyA L5DefsA L5CoreA PmLayout PmLayoutA PmModel PmStatics PmStaticsA PmSpecsA PgSrc PgV8 PgSrcA PgV8A PnLayout PnModel PnRun PeRunBA PeSpecsAX.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_PeSpecsAX8 () := "C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA6fframeC13~~~C46Stdlib5Lists4List4inclK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA:shadow_blkC13~~~K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3divC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA;shadow_zeroC13~~~C56Stdlib6ZArith6BinInt1Z6moduloC47Corelib4Init5Logic3notC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA1SC13~~~C56Stdlib6ZArith6BinInt1Z3addC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA7byte_atC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PmSpecsA5PMSPA4annAC13~~~K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3mulI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC47Corelib4Init5Logic9False_indK47Corelib4Init5Logic3and01K46Stdlib9micromega5Tauto8GFormula04I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNSAX8.
(* [comment removed for export] *)
Lemma ann_full_of_blk (M : word -> option byte) (b c : Z) : shadow_blk M b c -> PMSPA.annA M b c c.
Proof.
ltac2:(KReplay.run1 (kr_t_PeSpecsAX8 ()) [] "h01Hh11Mh24__p1h34__x1h44__x2h51bh61ch71jh82H0h92H1h:2H2h;2H3h<2H4h=2H5h>2H6h?2H7h@2H8hA2HjhB2P1hC2Z0hD7__arithhE4__ffhF6__sat2hG6__sat3hH6__sat4hI8__varmaphJ5__withK1qhL2q0hM1rhN2r0p;1p;3p;2p;4p;7p;6p;8p10000p4p70p1001<p4p710p8g001Uj14Tg002:j1MTg002Xj1KTg003;j1RTg003]j3aTg004mj1?Tg005Kj22Tg005hj3>Tg0079j20Tg007Yj1;Tg0082j1<Tg0099j21Tg009Vj3=Tg00:cj4]Tg00<1j1:Tg00<Vj29Tg00=2j25Tg00=NR0j26Tg00=ij2VTg00>Zj2JTg00?Kj2FTg00?lj2ETg00@Ij37Tg00@cj2CTg00AJj2GTg00B1j2HTg00BWj2BTg00C=j1TTg00C]j1STg00D=j2ATg00D[j4QTg00E9j1PTg00EWj1OTg00FBj2@Tg00Fej4DTg00GPj7NTg00H4j1UTg00HVj6`Tg00I:j8_Tg00I^j2^Tg00J@j2\Tg00JZj2[Tg00KFj3YTg00Kej4XTg00LWj2ZTg00M6j4LTg00MQj7WTg00N5R1f0R2g00NSR337p=81932p=3f1R4g00O1R5g00OPR6P6g00P0R7P2g00PPFWp=Ig00Q0R8#4R9#4#4R:#4#4#4#M#K%M:#K#R[R;f2R<?a42P0f3R0%?:R:,247><104:#8#;f4R=%<012<:'110<:3=[P=P0P<P<C]P2f5R>120:7>=10=:#8#;f7R?f6R@#<12>:RA'110>:R>3=[A>?@A%8>#;f8R>%<?12@:'110@:3=[RA%:8R8#:RB#?RC,1@/2:R@/92152@'6R@f9RD%<>/14%:B#:#:#4#4#?3=RB[^71RE'6P4PAPEP21V?:%3?%3:R?10D:#3[[1J>:%3>f:R>/2:#3\?[11DCRE/J:%3Ef;/1CRE/2:RA#3\?[11>C/F:%8:R>#;R?1E:A10E:'1971E[1CE:153:REf</1CRA/0:RF#315F:'6[1GA:15:3RAf=/1CRF/0:RG,5:19G3'6[1HF:f>/1CRF/2:#8\>1BF:f?/1CRF/0:=71F\>12F:P1f@/1C/0:P1fA/F:fBRC12C:,E:10C:'1571\?1CC:fCR?/0:RF#315F:'6\E1G?:fDRE/0:RF,5:19F3'6\A1HE:fERE/2:#8\>1BE:fFRE/0:=71E\>12E:P1fG/0:P1p-0R:g00QURE#T%SEP11A14P<1A1<CQ%P1%O1REP5P6P6P7PEP5P6P6P7P11@19R9g00RA1@18R8CD,IEP1P8g00RhP9CD,IEFN%U6PEP5P6P6P7P=E`G_1^E7P2P<g00SOREg00SoR7'\1[2<=7E7dAY134CXbEbIbJX31X41W219241542'6P0[^31^41^2:P2g00TOP?PDPCO4bDbNbLb@b?b>b=b<bMbKb;b:b9b8b0bFbGbH,ZBXA@X71CLCLWBWCP4P2O2n2001000000121000000W0X61X51X1;P<P4P2O3X61X51W1o"). Qed.

Section Specs.
Context {SCFG_P : ScfgP}.
Variable segs : list Segment.
Variable A : pm_addrs.
Variable L : asan_layout.
Variable ar : asan_run.
Variable HI : asan_iface.

Local Abbreviation v8_at := (PGV8.v8_at segs PMSPA.accA PMSPA.annA).
Local Abbreviation v8_hdr := (PNSAX.v8_hdr segs).

Definition ann_increase_v8_spec (pc : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (v k : Z) (x : PGV8.v8) (sp r : Z),
    ri_inv HI (PGV8.v8_own x ++ LBX) FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
    PMSPA.entryA A L ar R M sp r 0 -> PMSPA.ffrsA FF sp ->
    getr R 10%bv = Z_to_bv 64 v -> getr R 11%bv = Z_to_bv 64 k -> PMSPA.aobjA FF v 24 -> v mod 8 = 0 -> PMSPA.accA M v 24 ->
    v8_at M v x -> 0 <= k -> PGV8.v8_size x + k <= PGV8.v8_cap x ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)),
        regs_preserved R R' ->
        v8_hdr M' v x -> PMSPA.accA M' v 24 ->
        (forall b n c, x = PGV8.V8Blk b n c -> PMSPA.accA M' b (n + k) /\ PMSPA.annA M' b (n + k) c) ->
        (forall b n c a, x = PGV8.V8Blk b n c -> b <= a < b + c -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
        L5CA.ahpres L ar LBX FF sp (PMSPA.pm_scr 0) [] M M' ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' ->
        ri_inv HI (PGV8.v8_own x ++ LBX) FF LK' cr Aw' M' (vml_of model') ->
        srealizes segs SCFG (@PMSPA.cfg segs fx' R' r M' model') K) ->
    srealizes segs SCFG (@PMSPA.cfg segs fx R pc M model) K.

Definition ann_new_v8_spec (pc : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (v sz : Z) (x : PGV8.v8) (sp r : Z),
    ri_inv HI (PGV8.v8_own x ++ LBX) FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
    PMSPA.entryA A L ar R M sp r 0 -> PMSPA.ffrsA FF sp ->
    getr R 10%bv = Z_to_bv 64 v -> getr R 11%bv = Z_to_bv 64 sz -> PMSPA.aobjA FF v 24 -> v mod 8 = 0 -> PMSPA.accA M v 24 ->
    v8_hdr M v x -> PGV8.v8_size x = sz ->
    (forall b n c, x = PGV8.V8Blk b n c -> PMSPA.annA M b c c) ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)),
        regs_preserved R R' -> v8_at M' v x ->
        (forall b n c a, x = PGV8.V8Blk b n c -> b <= a < b + c -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
        L5CA.ahpres L ar LBX FF sp (PMSPA.pm_scr 0) [] M M' ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' ->
        ri_inv HI (PGV8.v8_own x ++ LBX) FF LK' cr Aw' M' (vml_of model') ->
        srealizes segs SCFG (@PMSPA.cfg segs fx' R' r M' model') K) ->
    srealizes segs SCFG (@PMSPA.cfg segs fx R pc M model) K.

End Specs.
End PNSAX8.
