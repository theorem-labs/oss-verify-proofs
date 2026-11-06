(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_HnIface () := "C46Stdlib9micromega5Tauto5eKindK46Stdlib9micromega5Tauto8GFormula04K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z2ltK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC56Stdlib6ZArith6BinInt1ZDmul_le_mono_nonneg_rC56Stdlib6ZArith6BinInt1Z5max_lc59OSSVerify5KrLib4Heap7HnIface4cszRC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I46Stdlib9micromega5Tauto8GFormula00C56Stdlib6ZArith6BinInt1Z8le_max_lC59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C35stdpp7tactics<f_equal_helpK47Corelib4Init9Datatypes4prod01K46Stdlib9micromega6VarMap1t03c59OSSVerify5KrLib4Heap7HnIface6debitRC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Heap7HnIface7refundRC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndI47Corelib4Init9Datatypes4prod00K46Stdlib9micromega=RingMicromega3Op201".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)

Definition NREQ : Z := 2 ^ 30 - 2 ^ 16.
(* [comment removed for export] *)
Definition cszR (n : Z) : Z := Z.max (2 ^ 20) ((n + 20 + 4095) / 4096 * 4096).

Definition credit_okR (cr : credit) (n : Z) : Prop := 1 <= fst cr /\ cszR n <= snd cr.
Definition debitR (cr : credit) (n : Z) : credit := (fst cr - 1, snd cr - cszR n).
Definition refundR (cr : credit) (n : Z) : credit := (fst cr + 1, snd cr + cszR n).

Lemma cszR_small n : 0 <= n <= 2 ^ 20 - 20 -> cszR n = 2 ^ 20.
Proof.
ltac2:(KReplay.run1 (kr_t_HnIface ()) [] "h07__arithh14__ffh28__varmaph35__with44__x1h52H0h62H1h72H2h82H3h92H4h:4__p1h;6__sat0h<1nh=1qh>1rh?1Hh@2Hnp;1p;2p;3p;4p;6p;7p;5p;8g0000R0p4p711g000OR1p4p73101p8g0013j1>Tg001Xj13Tg0026j18Tg002[j2WTg0038j2DTg003Uj2:Tg0041j2=Tg004Lj2;Tg004ij2ATg005Fj1fTg005fj1`Tg006Fj1XTg006dj1VTg007Bj1UTg007mj2FTg008Pj2STg0092j2RTg009Lj2QTg00:8j36Tg00:Rj3OTg00;1j4NTg00;cj22Tg00<?j2MTg00<]j6LTg00=Aj2KTg00=dj3JTg00>Gj7ITg00>kj1PTg00?Mj3CTg00@0j3HTg00@Sj5TTg00A?j2eTg00B0j2dTg00BQj1cTg00Bjj2<Tg00CJj2BTg00Cgj2_Tg00DNj2YTg00E5j2ZTg00E[j2[Tg00FAj5\Tg00Foj3]Tg00GNj1^Tg00HDj4GTP1j7aTg00Hoj8bTg00ISR1f0R2':p=5%>2#>p=0%82#8p=9f2R3f1R4'B/B2p=1g00J1R5/F2p=7P5P4g00JOP2CGp=@P4P0g00K6R6P6g00KVR7P2g00L6Fap=4P5P4g00LVP2CGp=?f3R8P0P6P6P7P3P4P2Gbp=E%52g00M=R9#>R:#3%8:#0#3R;'WR</D;,:2'=%0:#0#0R:#>R=#0#0R>#0#0#0#0#3R?%89#9#9#9#9#9#3R@914;RA%3>R>';RB/A>PAP>%8:#3R:g00MbRC#fRD%`CRC%X5RE%V5RF%U5RG1F51RH%7>RI'@'41SG7RJP2P3g00NNRKg00NnRL'R1Q23=6KLdAO514CNRLb1b2b3121>RKP2b0p-0RMPDPC1M54RNPFPGPGP0P6P6P7PGP0P6P6P7P8EL1K59R9%7?%7;R75J5'?,4GFI%P6R6AC597%7@5C5%7:R79H5I'@,4GCEPJPLb1b2b3X45W:1D?;,:2,=41A>:,2A[^45^:MP2%53P3P4O3b0DT12B:A13;@RB/;>%3=R=P>1eB>RM%5B%5>RBf4?1;@RA/;>R?#5[[R0A18;@/d>R8A65>1RO#c1A>?1<A>'B965A[R?1_A>RAf5?1;@RP/<>RQ#512Q>'=\KRK1YP>RP12>1f6?1;@RQ/<>RR,2>1:R1'=[RR1ZQ>RQf7?1;@RS/;>=651\OR11[S>RSf8?1;@RT/<>=65T\ORO1;T>RTP5f9RU?1;@/<>R>P5PDPCPEPF1?HI,4GPJPLb1b2b3PBP2b0b>b=b9b8b7b6b5b;PMP0P8P?PAPKPPPRPQP1PSPOPTP5P>P5PDPCPNPFPG1@97,4GP6%7=,?9,4GCEPJPLb1b2b3X45122:1:4=[^45P2P3PUO2b0b>b=b9b8b7b6b5b;D\b?3]%^4=65<eW@X<5P2O1X<5o"). Qed.

Lemma cszR_ge n : 2 ^ 20 <= cszR n.
Proof.
ltac2:(KReplay.run1 (kr_t_HnIface ()) [] "h01np;1p;2p10000p4p711p100ONp4p73101p8g0013j13Tg001Xj14Tg0026j12Tg002[j2;Tg00CJj25Tg004Lj2:Tg004ij29Tg00P2j27Tg00GNj16Tg003Uj28Tf0R0#3#3p=0%20#2p=1g00J1R1g00M=R2#3R3#4%23#0#4R4';R51504%22#1#1#1#1#1#4'5%33#0#0#0#0#0#4R3':/93'7%60,85eX01P0O1W0o"). Qed.

Lemma refund_debit cr n : refundR (debitR cr n) n = cr.
Proof.
ltac2:(KReplay.run1_chk (kr_t_HnIface ()) [] "p'0h04__x1h17__arithh24__ffh38__varmaph45__with54__x2h62crh71nh81bh91ki001pi011zp;1p;3p;2p;4p;8p;7g00PTR0p4p70g00QQR1p4p7210p8g0000R2p4p711g000OR3p4p73101p8g001Xj1TTg00GNj15Tg00:8j31Tg00Qnj3<j2Ej4PTg0092j2?Tg005Fj1CTg005fj1ATg00<?j2:Tg006dj1STg007Bj1RTg00=Aj2@Tg007mj2LTg00=dj3>Tg00?Mj38Tg00HDj4=Tg008Pj2KTg009Lj2JTg00:Rj3ITg00;1j4HTP1j8;Tg006Fj1FTg00RNj4GTg0013j1DTg0038j26Tg00CJj27Tg00Rlj2BTg00Sdj2MTg00T]j3NTg00U:j3OTP3j7QTg00J1R3f0R17N3p=3f2R4f1R5'6/71p=0AO331p=4P3P3P5P1CPp=2P5P2g00K6R2P2g00KVR2P1g00L6FQp=9g00UWP3P3%31g00M=R6#TR7;07%41%55R8;08'2=101P5P3P0A0577R89<33A<335f4#5R9=019P1P3P0\3R:1E33R;P;P8P5P:\3/?;g00MbR;#CR:%A;R;1:35%S3R8%R3R<P31@36R=1L37R>5>3=83>g00V7R>P=C='91K<2R2P1P4g00NNR?g00NnR@'?1J14=1?@dg00IS=I35CHR@b2b3b4X03A0177=131^03P1P4O1b1G;P:P;P31:34P5%F3CGP8P3%D6,@3R69>3==836P>P=C=,9<P2P@b2b3b4X03X53A0155=131^03^53P1f5#5P5O2b1G;1251R@#3?077%4@?099'2=10@eX83X93P5P1O2n2001100000121101101%35/67%45%51R@'6'2R9#3/77%49/7@'2=105e1B51/M1=105eX73X60P5P1O2X73X60o"). Qed.

(* [comment removed for export] *)

Section IfaceR.
Variable L : heap_layout.
Variable scfg : SpuriousCfg. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable HI : heap_iface.

Definition mallocR_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model)
         (LB : list (Z * Z)) (cr : credit) (n : Z) (K : ShapeAlg.TSet),
    hi_heap HI LB cr M (m_vmmaps model) ->
    m_halted model = None -> m_vm_lazy model = [] -> m_vm_materialized model = [] ->
    getr R 10%bv = Z_to_bv 64 n -> 0 < n <= NREQ ->
    credit_okR cr n ->
    getr R 4%bv = Z_to_bv 64 (hl_tp L) ->
    Hoare.ret_ok (getr R 1%bv) ->
    stack_ok L M (bv_unsigned (getr R 2%bv)) ->
    K [] ->
    (forall (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (A : Z),
        getr R' 10%bv = Z_to_bv 64 A ->
        regs_preserved R R' ->
        block_range L A n -> blocks_apart A n LB ->
        defined M' A n ->
        heap_pres_core L LB (bv_unsigned (getr R 2%bv)) M M' ->
        model_but_vm model model' ->
        hi_heap HI ((A, n) :: LB) (debitR cr n) M' (m_vmmaps model') ->
        srealizes (hl_segs L) scfg (mkCfg (@mkst fx R' (getr R 1%bv) M' (seg_rom (hl_segs L))) model') K) ->
    srealizes (hl_segs L) scfg (mkCfg (@mkst fx R (Z_to_bv 64 (hl_malloc L)) M (seg_rom (hl_segs L))) model) K.

Definition alignedR_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model)
         (LB : list (Z * Z)) (cr : credit) (n : Z) (K : ShapeAlg.TSet),
    hi_heap HI LB cr M (m_vmmaps model) ->
    m_halted model = None -> m_vm_lazy model = [] -> m_vm_materialized model = [] ->
    getr R 10%bv = Z_to_bv 64 16 -> getr R 11%bv = Z_to_bv 64 n -> 0 < n <= NREQ ->
    credit_okR cr n ->
    getr R 4%bv = Z_to_bv 64 (hl_tp L) ->
    Hoare.ret_ok (getr R 1%bv) ->
    stack_ok L M (bv_unsigned (getr R 2%bv)) ->
    K [] ->
    (forall (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (A : Z),
        getr R' 10%bv = Z_to_bv 64 A ->
        regs_preserved R R' ->
        block_range L A n -> blocks_apart A n LB ->
        defined M' A n ->
        heap_pres_core L LB (bv_unsigned (getr R 2%bv)) M M' ->
        model_but_vm model model' ->
        hi_heap HI ((A, n) :: LB) (debitR cr n) M' (m_vmmaps model') ->
        srealizes (hl_segs L) scfg (mkCfg (@mkst fx R' (getr R 1%bv) M' (seg_rom (hl_segs L))) model') K) ->
    srealizes (hl_segs L) scfg (mkCfg (@mkst fx R (Z_to_bv 64 (hl_aligned_alloc L)) M (seg_rom (hl_segs L))) model) K.

(* [comment removed for export] *)
Definition freeR_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model)
         (LB : list (Z * Z)) (cr : credit) (A n : Z) (K : ShapeAlg.TSet),
    hi_heap HI LB cr M (m_vmmaps model) ->
    m_halted model = None -> m_vm_lazy model = [] -> m_vm_materialized model = [] ->
    In (A, n) LB ->
    getr R 10%bv = Z_to_bv 64 A ->
    getr R 4%bv = Z_to_bv 64 (hl_tp L) ->
    Hoare.ret_ok (getr R 1%bv) ->
    stack_ok L M (bv_unsigned (getr R 2%bv)) ->
    K [] ->
    (forall (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model),
        regs_preserved R R' ->
        heap_pres L (lb_remove A LB) (bv_unsigned (getr R 2%bv)) M M' ->
        model_but_vm model model' ->
        hi_heap HI (lb_remove A LB) (refundR cr n) M' (m_vmmaps model') ->
        srealizes (hl_segs L) scfg (mkCfg (@mkst fx R' (getr R 1%bv) M' (seg_rom (hl_segs L))) model') K) ->
    srealizes (hl_segs L) scfg (mkCfg (@mkst fx R (Z_to_bv 64 (hl_free L)) M (seg_rom (hl_segs L))) model) K.

Record heap_ifaceR_ok : Prop := HIROK {
  hir_malloc : mallocR_spec;
  hir_aligned : alignedR_spec;
  hir_free : freeR_spec;
  hir_free_null : free_null_spec L scfg;
  hir_frame : heap_frame L HI;
  hir_wf : heap_blocks_wf L HI;
  hir_perm : heap_perm HI
}.
End IfaceR.

(* [comment removed for export] *)
