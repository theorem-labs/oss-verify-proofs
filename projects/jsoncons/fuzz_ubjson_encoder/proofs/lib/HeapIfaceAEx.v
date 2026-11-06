(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PropExec StoreOk ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceANull L5Defs.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_HeapIfaceAEx () := "C46Stdlib5Lists4List2hdC47Corelib5Lists7ListDef3mapI47Corelib5Lists7ListDef6Forall00C47Corelib4Init9Datatypes3fstC35stdpp4base6ElemOfI35stdpp4base<list_elem_of00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA6fframeC13~~~C47Corelib4Init9Datatypes3appI35stdpp4base5NoDup00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA:shadow_blkC13~~~C56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<HeapIfaceAEx3HAJ:ann_shadowC13~~~I47Corelib4Init5Logic2ex00K47Corelib4Init5Logic2or01K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3divC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA;shadow_zeroC13~~~C56Stdlib6ZArith6BinInt1Z6moduloC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA1SC13~~~K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3addK47Corelib4Init5Logic3and01C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3mulI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC47Corelib4Init5Logic3iffC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA7byte_atC13~~~K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Section AIfaceB.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable scfg : SpuriousCfg.
Variable HI : asan_iface.
Record asan_iface_okB : Prop := AIOKB {
  aiob_malloc : amalloc_spec L ar scfg HI;
  aiob_aligned : aaligned16_spec L ar scfg HI;
  aiob_free : afree_spec L ar scfg HI;
  aiob_stack_malloc : forall k, In k [1; 3] -> astack_malloc_spec L ar scfg HI k;
  aiob_release : rt_release_frame L ar HI;
  aiob_leak : rt_leak_frames HI;
  aiob_no_return : ahandle_no_return_spec L ar scfg HI;
  aiob_memset : amemset_spec L ar scfg HI;
  aiob_memcpy : amemcpy_spec L ar scfg HI;
  aiob_memmove : amemmove_spec L ar scfg HI;
  aiob_frame : rt_frame L ar HI;
  aiob_wf : rt_wf L ar HI;
  aiob_lazy : rt_lazy L ar HI;
  aiob_perm : rt_perm HI;
  aiob_statics : rt_statics L C HI;
  aiob_flagptr : rt_flagptr L HI;
  aiob_small_high : rt_small_high HI
}.
End AIfaceB.

Module HAJ.

(* [comment removed for export] *)
Definition ann_shadow (M : word -> option byte) (b u c : Z) : Prop :=
  shadow_zero M b (u / 8) /\ (u mod 8 <> 0 -> byte_at M (S b + u / 8) (u mod 8))
  /\ (forall j, (u + 7) / 8 <= j < (c + 7) / 8 -> byte_at M (S b + j) 252).
(* [comment removed for export] *)
Definition shadow_blkR (M : word -> option byte) (u n : Z) : Prop :=
  shadow_blk M u n \/ (exists m, 0 <= m <= n /\ ann_shadow M u m n).

Lemma shadow_blkR_of (M : word -> option byte) u n : shadow_blk M u n -> shadow_blkR M u n.
Proof.
ltac2:(KReplay.run1 (kr_t_HeapIfaceAEx ()) [] "h01Mh11nh21uh31Hh41mp;1p;3p;2p;4p-1R0p10000p4p710R1p8P0p1000GR2p4p710R3p8P0P2p4p7210p8P0p1000cp4p710R2p8P0p1001DR4p4p710p8P0P4p4p7210p8P0p1001aR4p4p710R5p8P0P4p4p7210R4p8P0p10025p4p710R0p8p1002Qp4p70R6P1p8P6P3p8P6P2p8P6p1003]p4p710p8p1004:p4p710R6P5p8P6P4p8P6P0p8g004Oj10Tg0054j15Tg005Rj11Tg0065j16Tg006Wj34Tg007gj22Tg008Cj23Tg008^j49Tg00:4j28Tg00:Nj37Tg00:h#0#0#0R0#0#0#0#5#1%50#1#6[R0g00;MR6f2R4f1R5f0R234f3R3?445g00;k/221224'3f4P3P2P4C9'3X46,86;72W3X16X26X00P4P5P2O3X16W2W0o"). Qed.

(* [comment removed for export] *)
Lemma ann_shadow_full (M : word -> option byte) b c : 0 <= c -> ann_shadow M b c c <-> shadow_blk M b c.
Proof.
ltac2:(KReplay.run1 (kr_t_HeapIfaceAEx ()) [] "h01jh11Hh21Mh31Ph42Z0h54__p1h64__x1h74__x2h81bh91ch:2H0h;2H1h<2H2h=2H3h>2H4h?2H5h@2H6hA2H7hB2H8hC2HchD2HjhE2_HhF7__arithhG4__ffhH6__sat1hI6__sat2hJ6__sat3hK8__varmaphL5__withM1qhN2q0hO1rhP2r0p;1p;2p;3p;4p;7p;6p;8g004Oj18Tg0054j1OTg005Rj1ITg0065j1UTg00<Ij1ATg00<gj20Tg00=Dj3;Tg00>Uj21Tg00?5j16Tg00@<j1>Tg00@aj22Tg007gj25Tg008CR0j23Tg00A>j4?Tg00AYj3XTg00BJj3Wj2VTg00C;j2LTg00C\j1HTg00D5j2GTg00DRj3<Tg00Dlj2FTg00ESj2=Tg00Eoj2ETg00FVj2JTg00G<j2KTg00Gbj1TTg00HBj1STg00Hbj2CTg00I@j1RTg00I^j4BTg00J<j1QTg00JZj1PTg00KEj2DTg00Khj4MTg00LSj7fTg00M7j1eTg00MYj6dTg00N=j8cTg00Naj2bTg00OCj2^Tg00O]j2]Tg00PIj3\Tg00Phj4[Tg008^j4ZTg006Wj3_Tg00QZj2YTg00R3j3`Tg00S@j7aTg00;kR1f0R2'5p=:g00;MR3?<21#Hp=9f3R4f2R5f1R6'2;`2p=41=62,35p=7A<321p=@P6g00SdR7g00TCR8P8g00TcR9P2g00UCFap=Ng00:hR:#8#8R;#8R<#8#8#8#O#I%O<#I#U[R=%:2%A<R<,069;45R>116<#9f4R?%64105<R@115<RAC4[RB%>:R:#>RC#ARD,25/0<RE/52?72Ef5RE%6?RFP6%>C#>#>#8#8#ARCC4[^03'3'3RGA;?4@R@%9APEPF104<RF114<RAC4[RH'3[13>BRB124D/0<R>/52?72>f6R>%6ERIP6PCC4[^03,3HRJ,3@[P0P@PJA;E?FRF%9AP>PI10?<RI11?<C4[RA'3P2A;>EIRI11E<#9f8RJf7RK#610><RL11><RMC4[RN12>D/0<RO/52?72Of9RO%6JRPP6PCC4[^03'3P0%9MPOPP10K<RP11K<RMC4[RQ12KD/0<RR/52?72RRRf:RS%6ORTP6PCC4[^03RUA;OJP%9MPSPT10J<11J<RTC4['3P2%9Tf;RT%6S10O<11O<RMC4[12SDRP/0<RV/52?72Vf=RVf<RW#6RXP6PCC4[^0310S<RY9;WT11S<#9PVPX10T<11T<C4[PEP6C?WEW3P6P2O2n2001000000120000000W1W4P6P2O2n2001000000121000000X1GP0P@PH12?D/0<RH/52?72HPK%6>P6PCC4[^03,3A,3FP2A;JKL13QUP6PQPUP2AXJ<K%:<RK%:M[AWO<J%:Y\K1VP<%:P12WDRW/0<RP#:\K[12TD/L<%@<RT#HRK1G<P11W<'29<3W[1FW<1=1<RW12VDRV/1<RP#:?7P<[1EV<1=<1RVf>/2DRP/1<RY,=<15Y1'3[1JP<f?/2DRP/0<#@\T1KP<f@/2DRP/1<=<3P\T10P<P3fA/2D/1<P3fBRD/L<fCRP10P<,G<11P<'25<3\K1FP<fDRK/1<RY#:?7Y<\W1EK<fERK/1<RW,=<15W1'3\V1JK<fFRK/0<#@\T1KK<fGRK/1<=<3K\T10K<P3fH/1<P3p-0R<g00UcRK#T%SKP3P31C35P5%R3CBP51C36CB%Q3%P3RKP7P8P8P9PKP7P8P8P9P31D3:R:g00VO1D3;R;CM,NKP3P;g00W6P:CM,NKFf%e8PKP7P8P8P9P?EdGc1bK9P2P5g00W]RKg00X=R9'^1]25=<K9dA\316C[bGbKbLX63X73W51526?762P4[^63^73^5<P2fLfK#6PPPCC4PPPOPDO4bFbPbNbBbAb@b?b>bObMb=b<b;b:b1bHbIbJXDRX03C?C?X3NX4IP6P2O2n2001000000121000000X1BC?P4P5P6P6CZA_456'YeWCX93X83X2=P5P6P2O3X93X83W2o"). Qed.

(* [comment removed for export] *)
Definition atexit_cells (segs : list Segment) (M : word -> option byte) (X f0 a0 f1 a1 atc : Z) (hs : list (Z * Z)) : Prop :=
  L5.u8_at segs M X 0 /\ L5.u32_at segs M (X + 4) 0 /\ L5.u32_at segs M (X + 8) (2 + 2 * Z.of_nat (length hs))
  /\ L5.u64_at segs M (X + 16) (X + 24) /\ L5.u64_at segs M (X + 24) 0
  /\ L5.u64_at segs M (X + 32) f0 /\ L5.u64_at segs M (X + 288) a0
  /\ L5.u64_at segs M (X + 40) f1 /\ L5.u64_at segs M (X + 296) a1
  /\ (forall (i : nat) f a, nth_error hs i = Some (f, a) ->
        L5.u64_at segs M (X + 48 + 16 * Z.of_nat i) f /\ L5.u64_at segs M (X + 56 + 16 * Z.of_nat i) atc
        /\ L5.u64_at segs M (X + 304 + 16 * Z.of_nat i) a /\ L5.u64_at segs M (X + 312 + 16 * Z.of_nat i) 0).

(* [comment removed for export] *)
Record ext_consts : Type := EXTC {
  ec_ann_pc : Z; ec_ann_scr : Z;          (* [comment removed for export] *)
  ec_cxa_pc : Z; ec_cxa_scr : Z;          (* [comment removed for export] *)
  ec_atexit : Z; ec_f0 : Z; ec_a0 : Z;              (* [comment removed for export] *)
  ec_f1 : Z; ec_a1 : Z;                               (* [comment removed for export] *)
  ec_atc : Z;                                        (* [comment removed for export] *)
  ec_nl : Z;                                         (* [comment removed for export] *)
  ec_sf_pc : Z; ec_sf_scr : Z             (* [comment removed for export] *)
}.

Section X.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable scfg : SpuriousCfg.
Variable HI : asan_iface.

Let cfg_at (fx : FPState) (R : bvmap 5 word) (pc : word) (M : word -> option byte) (model : Model) : config :=
  mkCfg (@mkst fx R pc M (seg_rom (hl_segs L))) model.

(* [comment removed for export] *)
Definition rt_wfR : Prop :=
  forall LB FF LK cr A M V, ri_inv HI LB FF LK cr A M V ->
    (forall b, In b LB -> ablock_range L ar (fst b) (snd b) /\ defined M (fst b) (snd b) /\ shadow_blkR M (fst b) (snd b)
                       /\ shadow_allowed A (fst b) (snd b)
                       /\ blocks_apart (fst b) (snd b) (lb_remove (fst b) LB) /\ fframes_apart (fst b) (snd b) (FF ++ LK)
                       /\ (fst b + snd b <= ar_fs ar \/ ar_fs ar + FS_BYTES <= fst b))
    /\ (forall f, In f FF -> ar_fs ar <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= ar_fs ar + FS_BYTES
                       /\ ff_addr f mod ff_bytes (ff_class f) = 0 /\ In (ff_class f) [0; 1; 2; 3; 4; 5]
                       /\ defined M (ff_addr f) (ff_bytes (ff_class f))
                       /\ fframes_apart (ff_addr f) (ff_bytes (ff_class f)) (ff_remove (ff_addr f) FF ++ LK))
    /\ app_mem (ar_fs ar) FS_BYTES /\ ar_fs ar + FS_BYTES <= ahl_ceil ar /\ (ar_fs ar + FS_BYTES <= hl_img_lo L \/ hl_img_hi L <= ar_fs ar)
    /\ shadow_allowed A (ar_fs ar) FS_BYTES
    /\ shadow_allowed A (ahl_ceil ar) (ar_sptop ar - ahl_ceil ar)
    /\ (ahl_ceil ar <= ar_stack_bottom ar + 4096 /\ ar_stack_bottom ar <= ahl_ceil ar + 4096)
    /\ (ar_stack_bottom ar mod 4096 = 0 /\ ar_stack_top ar = ar_stack_bottom ar + 8388608
        /\ 0x7fff80000000 <= ar_sptop ar <= 2 ^ 47 /\ ar_sptop ar mod 16 = 0)
    /\ ar_stack_top ar <= 2 ^ 47
    /\ NoDup (map fst LB) /\ NoDup (map ff_addr (FF ++ LK)) /\ 0 <= fst cr /\ 0 <= snd cr
    /\ defined M (ar_fs ar) FS_BYTES.

(* [comment removed for export] *)
Record asan_iface_okR : Prop := AIOKR {
  aior_malloc : amalloc_spec L ar scfg HI;
  aior_aligned : aaligned16_spec L ar scfg HI;
  aior_free : afree_spec L ar scfg HI;
  aior_stack_malloc : forall k, In k [0; 1; 2; 3; 5] -> astack_malloc_spec L ar scfg HI k;
  aior_release : rt_release_frame L ar HI;
  aior_leak : rt_leak_frames HI;
  aior_no_return : ahandle_no_return_spec L ar scfg HI;
  aior_memset : amemset_spec L ar scfg HI;
  aior_memcpy : amemcpy_spec L ar scfg HI;
  aior_memmove : amemmove_spec L ar scfg HI;
  aior_frame : rt_frame L ar HI;
  aior_wf : rt_wfR;
  aior_lazy : rt_lazy L ar HI;
  aior_perm : rt_perm HI;
  aior_statics : rt_statics L C HI;
  aior_flagptr : rt_flagptr L HI;
  aior_small_high : rt_small_high HI
}.

(* [comment removed for export] *)
Definition annotate_spec (pc scr : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model)
         (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (K : ShapeAlg.TSet) (b c u u' : Z),
    let sp := bv_unsigned (getr R 2%bv) in
    ri_inv HI LB FF LK cr A M (vml_of model) -> m_halted model = None -> MInv A model ->
    getr R 10%bv = Z_to_bv 64 b -> getr R 11%bv = Z_to_bv 64 (b + c) -> getr R 12%bv = Z_to_bv 64 (b + u) -> getr R 13%bv = Z_to_bv 64 (b + u') ->
    In (b, c) LB -> b mod 16 = 0 -> 0 <= u <= c -> 0 <= u' <= c ->
    ann_shadow M b u c ->
    getr R 4%bv = Z_to_bv 64 (hl_tp L) -> Hoare.ret_ok (getr R 1%bv) ->
    astack_ok L ar M scr sp ->
    K [] ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (A' : list (Z * Z)),
        regs_preserved R R' ->
        ann_shadow M' b u' c ->
        (forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF sp scr a -> ~ in_shadow_of b c a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
        (forall a, in_shadow_of b c a -> M (Z_to_bv 64 a) <> None -> M' (Z_to_bv 64 a) <> None) ->
        (forall a, sp - scr <= a < sp -> M' (Z_to_bv 64 a) <> None) ->
        model_rt model model' -> incl A A' -> MInv A' model' ->
        ri_inv HI LB FF LK cr A' M' (vml_of model') ->
        srealizes (hl_segs L) scfg (cfg_at fx' R' (getr R 1%bv) M' model') K) ->
    srealizes (hl_segs L) scfg (cfg_at fx R (Z_to_bv 64 pc) M model) K.

(* [comment removed for export] *)
Definition cxa_atexit_spec (pc scr X f0 a0 f1 a1 atc nl : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model)
         (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (K : ShapeAlg.TSet) (hs : list (Z * Z)) (f a d : Z),
    let sp := bv_unsigned (getr R 2%bv) in
    ri_inv HI LB FF LK cr A M (vml_of model) -> m_halted model = None -> MInv A model ->
    getr R 10%bv = Z_to_bv 64 f -> getr R 11%bv = Z_to_bv 64 a -> getr R 12%bv = Z_to_bv 64 d ->
    (length hs <= 2)%nat -> atexit_cells (hl_segs L) M X f0 a0 f1 a1 atc hs -> L5.u8_at (hl_segs L) M nl 0 ->
    getr R 4%bv = Z_to_bv 64 (hl_tp L) -> Hoare.ret_ok (getr R 1%bv) ->
    astack_ok L ar M scr sp ->
    K [] ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (A' : list (Z * Z)),
        regs_preserved R R' -> getr R' 10%bv = Z_to_bv 64 0 ->
        atexit_cells (hl_segs L) M' X f0 a0 f1 a1 atc (hs ++ [(f, a)]) ->
        (forall x, 0 <= x < 2 ^ 64 -> aclient L ar LB FF sp scr x -> ~ (X <= x < X + 544) -> M' (Z_to_bv 64 x) = M (Z_to_bv 64 x)) ->
        (forall x, X <= x < X + 544 -> M (Z_to_bv 64 x) <> None -> M' (Z_to_bv 64 x) <> None) ->
        (forall x, sp - scr <= x < sp -> M' (Z_to_bv 64 x) <> None) ->
        model_rt model model' -> incl A A' -> MInv A' model' ->
        ri_inv HI LB FF LK cr A' M' (vml_of model') ->
        srealizes (hl_segs L) scfg (cfg_at fx' R' (getr R 1%bv) M' model') K) ->
    srealizes (hl_segs L) scfg (cfg_at fx R (Z_to_bv 64 pc) M model) K.

(* [comment removed for export] *)
Definition astack_free_spec (pc scr k : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model)
         (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (K : ShapeAlg.TSet) (F rs : Z),
    let sp := bv_unsigned (getr R 2%bv) in
    ri_inv HI LB FF LK cr A M (vml_of model) -> m_halted model = None -> MInv A model ->
    In (F, k, rs) FF ->
    getr R 10%bv = Z_to_bv 64 F ->                   (* [comment removed for export] *)
    getr R 4%bv = Z_to_bv 64 (hl_tp L) -> Hoare.ret_ok (getr R 1%bv) ->
    astack_ok L ar M scr sp ->
    K [] ->
    (forall (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model),
        regs_preserved R R' ->
        (forall j, 0 <= j < ff_bytes k / 8 -> byte_at M' (S F + j) 245) ->
        (forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF sp scr a -> ~ in_shadow_of F (ff_bytes k) a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
        (forall a, sp - scr <= a < sp -> M' (Z_to_bv 64 a) <> None) ->
        model_rt model model' -> MInv A model' ->
        ri_inv HI LB (ff_remove F FF) LK cr A M' (vml_of model') ->
        srealizes (hl_segs L) scfg (cfg_at fx R' (getr R 1%bv) M' model') K) ->
    srealizes (hl_segs L) scfg (cfg_at fx R (Z_to_bv 64 pc) M model) K.

(* [comment removed for export] *)
Definition rt_frame_ctr : Prop :=
  forall LB FF LK cr A M M' V, ri_inv HI LB FF LK cr A M V ->
    (forall a, 0 <= a < 2 ^ 64 -> art_private L ar LB FF a -> ~ (hl_tp L + 16 <= a < hl_tp L + 20) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
    cell_is (hl_segs L) M' (hl_tp L + 16) 4 0 -> (forall a : word, M a <> None -> M' a <> None) -> ri_inv HI LB FF LK cr A M' V.

(* [comment removed for export] *)
Record asan_ext_ok (E : ext_consts) : Prop := AEXT {
  aex_annotate : annotate_spec (ec_ann_pc E) (ec_ann_scr E);
  aex_cxa_atexit : cxa_atexit_spec (ec_cxa_pc E) (ec_cxa_scr E) (ec_atexit E) (ec_f0 E) (ec_a0 E) (ec_f1 E) (ec_a1 E) (ec_atc E) (ec_nl E);
  aex_frame_ctr : rt_frame_ctr;
  aex_free_null : afree_null_spec L ar scfg HI;
  aex_stack_free : astack_free_spec (ec_sf_pc E) (ec_sf_scr E) 5          (* [comment removed for export] *)
}.
End X.

(* [comment removed for export] *)
Definition strict_of (HIR : asan_iface) : asan_iface :=
  AI (fun LB FF LK cr A M V => ri_inv HIR LB FF LK cr A M V /\ Forall (fun b => shadow_blk M (fst b) (snd b)) LB
                               /\ Forall (fun f => In (ff_class f) [1; 2; 3]) (FF ++ LK)).

End HAJ.
