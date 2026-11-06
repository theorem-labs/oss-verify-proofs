(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core L5CoreKit
     PmLayout PmModel PmModelFacts PmStatics PmSpecs PmStep PeSpecsU PeCLayout PeCLayoutU PeCSink PeCStatics PeCModel PeCSpecs PeCSpecsU.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef UbjRefFacts.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_PeUCParseD () := "I47Corelib4Init5Logic2eq00I47Corelib4Init5Logic2or00K47Corelib4Init5Logic2eq01K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:PeUCParseD7PEUCLPD4lpG1C13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:PeUCParseD7PEUCLPD4lpG2C13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:PeUCParseD7PEUCLPD4lpG3C13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:PeUCParseD7PEUCLPD4lpG4C13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec6UbjRef5pmode00C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec6UbjRef5pmode01C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec6UbjRef5pmode02C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec6UbjRef5pmode07C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec6UbjRef5pmode09C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec6UbjRef5pmode0;C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec6UbjRef5pmode03C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec6UbjRef5pmode05C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec6UbjRef5pmode06C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec6UbjRef5pmode08C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec6UbjRef5pmode04C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec6UbjRef5pmode0:C13~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec;UbjRefFacts8bytes_okC13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:PeUCParseD7PEUCLPD4linvC13~~~K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3subC45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init9Datatypes3nat02C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec4getrC13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:PeUCParseD7PEUCLPD4lmemC13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec;UbjRefFacts4ginv00C13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec;UbjRefFacts9ginv_initC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec;UbjRefFacts8run_ginvC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec;UbjRefFacts;run_not_badC13~~~K47Corelib4Init5Logic3and01C47Corelib4Init5Logic8eq_ind_rC56Stdlib6ZArith6BinInt1Z6of_natC89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec6UbjRef3runC13~~~I47Corelib4Init5Logic2ex00C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec6UbjRef6haltedC13~~~I47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z3addC89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec6UbjRef5s_badC13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec6UbjRef2st00C13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec6UbjRef4initC13~~~I47Corelib4Init9Datatypes3nat00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02K47Corelib7Numbers7BinNums8positive03I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I47Corelib7Numbers7BinNums1Z00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9HeapIface6creditC13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7PmModel2PM3pst00C13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7PmModel2PM4vstr00C13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7PmModel2PM4strm00C13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PeCModel3PEC3enc00C13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7PeCSink4PESK4sink00C13~~~K47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums1Z01C56Stdlib5Arith8PeanoNat3Nat3addC89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec6UbjRef4stepC13~~~C47Corelib4Init3Nat3addC89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec;UbjRefFacts7run_addC13~~~C56Stdlib5Arith8PeanoNat3Nat7add_1_rC47Corelib4Init5Logic6eq_ind".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PEUCLPD.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Abbreviation AD := PeCLayoutU.CADDR_U.
Abbreviation EE := PeCLayoutU.EADDR_U.
Definition LPHEAD : Z := 0x39c90.
Definition LPRET : Z := 0x39fd0.

Section WithHeap.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable L : heap_layout.
Variable HI : heap_iface.
Variable P : PESK.sink_policy.

#[local] Notation T3 := PMSP.T3.
#[local] Notation T4 := PMSP.T4.
Abbreviation crun_pre := (PEC.crun_pre RSEGS AD EE L T3 T4 P).
Abbreviation owned := PEC.owned.
Abbreviation pot_all := (PEC.pot_all L P).

(* [comment removed for export] *)
Definition pkont (K : TSet) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (LBX : list (Z * Z)) (cr : credit) (sp r fb : Z)
           (p : list Z) (s : PM.pst) (str : PM.vstr) (sm : PM.strm) (en : PEC.enc) (k : PESK.sink) (e : bool) : Prop :=
  forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (n : nat)
         (s' : PM.pst) (sm' : PM.strm) (en' : PEC.enc) (k' : PESK.sink) (e' : bool) (cr' : credit),
    regs_preserved R R' ->
    halted (run n p UbjRef.init) = true ->
    PM.parser_at RSEGS AD T3 T4 M' (PMSP.o_p AD fb) (PMSP.o_is AD fb) s' /\ PM.iss_at RSEGS AD T3 M' (PMSP.o_is AD fb) str sm'
    /\ PEC.enc_at RSEGS EE L T3 T4 M' (PMSP.o_v AD fb) fb en' /\ PESK.sink_at RSEGS L T3 T4 P M' (PESK.o_sink EE fb) k'
    /\ PMST.base_ok RSEGS AD M' /\ PEST.err_ok RSEGS AD EE M' e' /\ L5.defined M' (PMSP.o_ec AD fb) 16
    /\ s_lo (run n p UbjRef.init) <= PESK.sk_z k' <= s_hi (run n p UbjRef.init) ->
    PMSP.src_step (PM.p_src s) (PM.p_src s') sm sm' -> (e = true -> e' = true) ->
    L5C.hpres L LBX sp (PMSP.pm_scr 10) (PEC.W_crun AD EE fb) M M' ->
    PMSP.credit_keep cr cr' (pot_all s en k) (PESK.sink_pot P (PESK.sk_c k')) ->
    model_but_vm model model' -> hi_heap HI (owned s' en' k' ++ LBX) cr' M' (m_vmmaps model') ->
    srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' r M' model') K.

(* [comment removed for export] *)
Definition pctx (K : TSet) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (LBX : list (Z * Z)) (cr : credit) (sp r fb cat : Z)
           (p : list Z) (s : PM.pst) (str : PM.vstr) (sm : PM.strm) (en : PEC.enc) (k : PESK.sink) (e : bool) : Prop :=
  hi_heap HI (owned s en k ++ LBX) cr M (m_vmmaps model) /\ PMSP.model_ok model /\ K [] /\ PMSP.entry AD L R M sp r 10 /\ PMSP.frame_ok AD L sp fb /\
  PECS.args3 AD tt R fb /\ crun_pre M fb p UbjRef.init s str sm en k e cat /\ incl (PM.vs_own str) LBX /\ PECS.payload_ok p /\
  (forall n, PESK.sp_hb P (s_hi (run n p UbjRef.init))) /\ PMSP.credit_le (pot_all s en k) cr /\
  pkont K R M model LBX cr sp r fb p s str sm en k e.

(* [comment removed for export] *)
Definition lslots (R : bvmap 5 word) (M1 : word -> option byte) (sp : Z) : Prop :=
  L5.u64_at RSEGS M1 (sp - 8) (bv_unsigned (getr R (PMK.reg 1))) /\
  L5.u64_at RSEGS M1 (sp - 16) (bv_unsigned (getr R (PMK.reg 8))) /\
  L5.u64_at RSEGS M1 (sp - 24) (bv_unsigned (getr R (PMK.reg 9))) /\
  L5.u64_at RSEGS M1 (sp - 32) (bv_unsigned (getr R (PMK.reg 18))) /\
  L5.u64_at RSEGS M1 (sp - 40) (bv_unsigned (getr R (PMK.reg 19))) /\
  L5.u64_at RSEGS M1 (sp - 48) (bv_unsigned (getr R (PMK.reg 20))) /\
  L5.u64_at RSEGS M1 (sp - 56) (bv_unsigned (getr R (PMK.reg 21))) /\
  L5.u64_at RSEGS M1 (sp - 64) (bv_unsigned (getr R (PMK.reg 22))) /\
  L5.u64_at RSEGS M1 (sp - 72) (bv_unsigned (getr R (PMK.reg 23))) /\
  L5.u64_at RSEGS M1 (sp - 80) (bv_unsigned (getr R (PMK.reg 24))) /\
  L5.u64_at RSEGS M1 (sp - 88) (bv_unsigned (getr R (PMK.reg 25))) /\
  L5.u64_at RSEGS M1 (sp - 96) (bv_unsigned (getr R (PMK.reg 26))) /\
  L5.u64_at RSEGS M1 (sp - 104) (bv_unsigned (getr R (PMK.reg 27))).

(* [comment removed for export] *)
Definition lrel (R : bvmap 5 word) (M : word -> option byte) (model : Model) (LBX : list (Z * Z)) (cr : credit) (sp fb : Z)
           (s : PM.pst) (sm : PM.strm) (en : PEC.enc) (k : PESK.sink) (e : bool)
           (M1 : word -> option byte) (model1 : Model) (s1 : PM.pst) (sm1 : PM.strm) (en1 : PEC.enc) (k1 : PESK.sink) (e1 : bool) (cr1 : credit) : Prop :=
  PMSP.src_step (PM.p_src s) (PM.p_src s1) sm sm1 /\ (e = true -> e1 = true) /\
  L5C.hpres L LBX sp 32768 (PEC.W_crun AD EE fb) M M1 /\ PMSP.credit_keep cr cr1 (pot_all s en k) (pot_all s1 en1 k1) /\
  model_but_vm model model1 /\ hi_heap HI (owned s1 en1 k1 ++ LBX) cr1 M1 (m_vmmaps model1) /\ lslots R M1 sp.

(* [comment removed for export] *)
Definition lmem (R : bvmap 5 word) (M : word -> option byte) (model : Model) (LBX : list (Z * Z)) (cr : credit) (sp fb cat : Z)
           (p : list Z) (s : PM.pst) (str : PM.vstr) (sm : PM.strm) (en : PEC.enc) (k : PESK.sink) (e : bool)
           (M1 : word -> option byte) (model1 : Model) (X1 : st) (s1 : PM.pst) (sm1 : PM.strm) (en1 : PEC.enc) (k1 : PESK.sink) (e1 : bool) (cr1 : credit) : Prop :=
  crun_pre M1 fb p X1 s1 str sm1 en1 k1 e1 cat /\
  lrel R M model LBX cr sp fb s sm en k e M1 model1 s1 sm1 en1 k1 e1 cr1.

(* [comment removed for export] *)
Definition linv (R : bvmap 5 word) (M : word -> option byte) (model : Model) (LBX : list (Z * Z)) (cr : credit) (sp fb cat : Z)
           (p : list Z) (s : PM.pst) (str : PM.vstr) (sm : PM.strm) (en : PEC.enc) (k : PESK.sink) (e : bool)
           (R1 : bvmap 5 word) (M1 : word -> option byte) (model1 : Model) (X1 : st) (s1 : PM.pst) (sm1 : PM.strm) (en1 : PEC.enc) (k1 : PESK.sink)
           (e1 : bool) (cr1 : credit) : Prop :=
  getr R1 (PMK.reg 2) = Z_to_bv 64 (sp - 128) /\ getr R1 (PMK.reg 8) = Z_to_bv 64 (fb + 40) /\ getr R1 (PMK.reg 9) = Z_to_bv 64 (fb + 8)
  /\ getr R1 (PMK.reg 18) = Z_to_bv 64 (fb + 432) /\ getr R1 (PMK.reg 19) = Z_to_bv 64 (fb + 64)
  /\ getr R1 (PMK.reg 20) = Z_to_bv 64 1 /\ getr R1 (PMK.reg 21) = Z_to_bv 64 32 /\ getr R1 (PMK.reg 22) = Z_to_bv 64 10 /\ getr R1 (PMK.reg 23) = Z_to_bv 64 2
  /\ getr R1 (PMK.reg 24) = Z_to_bv 64 125 /\ getr R1 (PMK.reg 25) = Z_to_bv 64 65024 /\ getr R1 (PMK.reg 26) = Z_to_bv 64 9 /\ getr R1 (PMK.reg 27) = Z_to_bv 64 79892
  /\ getr R1 (PMK.reg 10) = Z_to_bv 64 0
  /\ getr R1 (PMK.reg 3) = getr R (PMK.reg 3) /\ getr R1 (PMK.reg 4) = getr R (PMK.reg 4)
  /\ (exists i, X1 = run i p UbjRef.init) /\ halted X1 = false          (* [comment removed for export] *)
  /\ lmem R M model LBX cr sp fb cat p s str sm en k e M1 model1 X1 s1 sm1 en1 k1 e1 cr1.

(* [comment removed for export] *)
Definition top_mode (X : st) : pmode := ps_mode (hd (PS Mroot 0 0 0) (s_stk X)).
Definition lpG1 (m : pmode) : Prop := m = Mroot \/ m = Maccept \/ m = Mval \/ m = Mtval \/ m = Mival.
Definition lpG2 (m : pmode) : Prop := m = Marray \/ m = Mtarray.
Definition lpG3 (m : pmode) : Prop := m = Mkey \/ m = Mtkey.
Definition lpG4 (m : pmode) : Prop := m = Miarray \/ m = Mikey.
Lemma lp_split m : lpG1 m \/ lpG2 m \/ lpG3 m \/ lpG4 m.
Proof.
ltac2:(KReplay.run1 (kr_t_PeUCParseD ()) ["WithHeap"] "p'0h01mi001pp;3p;2p;1g0000j30Tg000Jj21Tg000dj26Tg001>j35Tg001Xj38Tg0022j1;Tg003Dj1:Tg004Vj1?Tg005hj1>Tf5R0f4R1f3R230f2R3f1R4f0R530'1p=2f6R6?001A0234/15'1p=3A0601A0234'1/15p=4A0123/14/15p=<A53459812p=9A83459812p=71145,13p==g007:R3P3P3P5g008HR4P3P5g009VR2P3P5g00:dR1P3P5g00<2R6P3P5g00=@R0E2F3P3P5g00>NR7P3P5g00?\R8P3P5g00@jR9P3P5g00B8R:P3P5g00CFR;P3P5g00DTR<E2F4F4D<P5A0344R=P3P4P2P3P4P1P3P4P6P3P4P0E2F3R>'1P3P4P7P3P4P8P3P4P9P3P4P:P3P4P;P3P4P<E2F4F4163495=>35A0324R>A0322R=P3P2P1P3P2P6A0320F3R?'1R@'1P3P2P7P3P2P8P3P2P9P3P2P:P3P2P;P3P2P<E2F4F4P>P@P=P?1632D935P3P7P4P3P7P2P3P7P1P3P7P6A0370F3F3A0377R?A0378R='1R@P3P7P9P3P7P:P3P7P;P3P7P<E2F4R>'1P@P>163795?=D9P3P;P4P3P;P2P3P;P1P3P;P6A03;0F3F3P3P;P7P3P;P8E2R=P3P;P9P3P;P:E2R?A03;;R>A03;<R@'1RA'1RB'1P=PBP?PAP>P@163;D9D7P3P8P4P3P8P2P3P8P1P3P8P6A0380F3F3A0387R@A0388R>'1RAP3P8P9P3P8P:P3P8P;P3P8P<E2F4R?'1PAP?163898@>D9P3P9P4P3P9P2P3P9P1P3P9P6A0390F3F3P3P9P7P3P9P8E2R>A0399R@A039:R?'1RAP3P9P;P3P9P<E2RB'1R='1P>P=163995@?95ABD7A0314RBA0312RAA0311R?P3P1P6P3P1P0E2R@'1R='1R>'1P3P1P7P3P1P8P3P1P9P3P1P:P3P1P;P3P1P<E2F4F4PBP>PAP=163195?@D735P3P:P4P3P:P2P3P:P1P3P:P6A03:0F3F3P3P:P7P3P:P8E2R@A03:9R?A03::R='1RAP3P:P;P3P:P<E2R>'1RB'1P@PB163:98?=95A>D7A0364R>A0362RAA0361R=A0366R?A0360RB'1R@'1RC'1RD'1P3P6P7P3P6P8P3P6P9P3P6P:P3P6P;P3P6P<E2F4F4P>PDPAPCP=P@P?PB1636D9D735P3P<P4P3P<P2P3P<P1P3P<P6A03<0F3F3P3P<P7P3P<P8E2RBP3P<P9P3P<P:E2R?A03<;R@A03<<R='1RC'1RA'1PBPAP?PCP@P=163<D7D7A0304R4A0302R2A0301R1A0306R6A0300R='1R@'1RC'1R?'1P3P0P7P3P0P8P3P0P9P3P0P:P3P0P;P3P0P<E2F4F4P4P?P2PCP1P@P6P=1630D7D735n01100000;0000000000000000000000%;5%:5%?5%>5'13=eX03P5O1X03P5O1W0o"). Qed.

(* [comment removed for export] *)
Definition iter_ok (G : pmode -> Prop) : Prop :=
  forall (K : TSet) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (LBX : list (Z * Z)) (cr : credit) (sp r fb cat : Z)
         (p : list Z) (s : PM.pst) (str : PM.vstr) (sm : PM.strm) (en : PEC.enc) (k : PESK.sink) (e : bool),
    PESK.sp_mode P -> PESK.sink_policy_ok P ->
    pctx K R M model LBX cr sp r fb cat p s str sm en k e ->
    forall (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (model1 : Model) (X1 : st)
           (s1 : PM.pst) (sm1 : PM.strm) (en1 : PEC.enc) (k1 : PESK.sink) (e1 : bool) (cr1 : credit),
      linv R M model LBX cr sp fb cat p s str sm en k e R1 M1 model1 X1 s1 sm1 en1 k1 e1 cr1 -> halted X1 = false -> G (top_mode X1) ->
      (forall (fx2 : FPState) (R2 : bvmap 5 word) (M2 : word -> option byte) (model2 : Model) (X2 : st)
              (s2 : PM.pst) (sm2 : PM.strm) (en2 : PEC.enc) (k2 : PESK.sink) (e2 : bool) (cr2 : credit),
          linv R M model LBX cr sp fb cat p s str sm en k e R2 M2 model2 X2 s2 sm2 en2 k2 e2 cr2 -> mu p X2 < mu p X1 ->
          srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx2 R2 LPHEAD M2 model2) K) ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 LPHEAD M1 model1) K.

(* [comment removed for export] *)
Lemma linv_ginv R M model LBX cr sp fb cat p s str sm en k e R1 M1 model1 X1 s1 sm1 en1 k1 e1 cr1 :
  bytes_ok p -> linv R M model LBX cr sp fb cat p s str sm en k e R1 M1 model1 X1 s1 sm1 en1 k1 e1 cr1 -> ginv p X1 /\ s_bad X1 = false.
Proof.
ltac2:(KReplay.run1 (kr_t_PeUCParseD ()) ["WithHeap"] "p'0h01ih11Hh22X1h33LBXh41Mh52M1h61Rh72R1h83cath92crh:3cr1h;1eh<2e1h=2enh>3en1h?2fbh@1khA2k1hB5modelhC6model1hD1phE1shF2s1hG2smhH3sm1hI2sphJ3strhK2BPhL2LIhM2_HhN3_H0hO3_H1hP4_H10hQ4_H11hR4_H12hS4_H13hT4_H14hU4_H15hV4_H16hW3_H2hX3_H3hY3_H4hZ3_H5h[3_H6h\3_H7h]3_H8h^3_H9i001xp%0p;1p;2p;Ip;Hp;5p;3p;4p;6g00Ebj1?Tg00FGj1:Tg00Flj1LTg00GJj1VTg00Gmj2^Tg00HYj1]Tg00I;j2\Tg00I[j1PTg00J;j1[Tg00KOlIZTg00Laj1HTg00M?j2UTg00M\j2ETg00NBj1;Tg00Naj22Tg00OilH1Tg00Q;j2STg00RMj1dTg00Sbj5cTg00U6j3bTg00VMj4aTg00Vhj6`Tg00WFj1_Tg0000j35Tg00Wfj3TTg00Y0S00j2JTg00YJj1KTg00ZWR0j28Tg00[2j2RTg00[Oj1QTf0R1#?#?p=<%;1#;p=Ff1R2%_1'Ep=9f3R3f2R4/22;51p=4%H1,E2p=Dg00\[R5g00]fS019T21754p=3f6R6f5R7f4R8'2;53g00_1R9/J4g00_PR:%K2g00`0R;35/81'8'8p==1234=582/81p=012781R42,E3556/81p=71S42%Q1=5:;'8p=61J94%K2=5:;/81'8p=B12831242557/81p=>12831R21,E4557p=C128395671J94%K2=5:;/81'8'8p=A12429583/81p=@A5678A5342/81'8p=Y%K2=5:;/81p=IA58341J92/81'8p=X12219534p=O1J91p=NQ019T21p=G%K1=5:;p=M%Q1=5:;p=Wg00`PR;#?R<#:R=#LR>%?<R?#?R@#<RA#?RB#LRC#VRD'^RE%L@#V#]\DRFg00a5RGg00akRH/\H#PS02g00bIRI%PHS03g00cTRJg00d_S04g00ekRKg00g7RLg00hDRMQ02Q03Q04Q02Q03Q04f@RN#[fIROfHRPfGRQfFRRfERSfDRTfCRUfBRVfARWPNf?RXf>RYf=RZf<R[f;R\f:S05f9R]f8S06f7S07P6P7P8P3P4P2MIZP0PDP\g00iR#FR^,9>R_%?B#HR`,US,ECC4PDP\%;^R^#;Ra#F#FRb,9>RcPCPT%?=R=#<#HRdPDP\%;bRb,9>RePCPT%H@R@PDP\%;bRb#F#F#F#FRf,9>RgPCPT%:;Rh#?#:#:#<#<#HRiPDP\%;fRf,9>RjPCPT%HBRBPDP\%;fRf,9>Rk1DC;R;PDP\%;fRf,9>Rl1DCARAPDP\%;fRf,9>Rm1DC=R=PDP\%;fRf,9>Rn1DC<R<PDP\%;fRf,9>Ro%:h#:#:Rh#?#:,DCRpPDP\%;fRf,9>Rq%:h#:#?#<#<#<#<,DCRhPDP\%;fRf,9>Rr%:?R?,DCRsPDP\%;f,9>Rf%:?#:#<#<#<#:#?#:#<,DCR?PDP\19>bRbg00j1,ECRtPDP\19>^R^fJRu/2^RvPDP\19>aRa12uaR>A3]1UX09Q06PuPOPPPQPRPSPTPUPVPWPNPXPYPZP[Q05P]Q06Q07P6P7P8P3P4MH1F=D0D0D0D0D0D0D0D0D0D0F7F7F7F7A6U]]P1PDPZP_1UQ`,ECC4PDPYPcPCPQPdPDPYPePCPQP@PDPYPgPCPQPiPDPYPjPCPQPBPDPYPkP;PDPYPlPAPDPYPmP=PDPYPnP<PDPYPoPpPDPYPqPhPDPYPrPsPDPYPfP?PDPYPbPtPDPYP^fMR`P^PDPYPaP`PaA3[1RX09P`fLR_fKRwPuPOPPPQPRPSPTPUPVPWPNPXPZP[P\Q05P]Q06Q07P6P7MH17B\E>E>D0D0D0D0D0D0D0D0D0F7F7F7F7P0PDPXPcPCPPPdECPDPXPePCPPP@PDPXPgPCPPPiPDPXPjPCPPPBPDPXPkP;PDPXPlPAPDPXPmP=PDPXPnP<PDPXPoPpPDPXPqPhPDPXPrPsPDPXPfP?PDPXPbPtPDPXP^fNRx/2^S08PDPXPa12xaRyA3Z1QX09P[PxP`P_PwPuPOPPPQPRPSPTPUPVPWPNPYPZP[P\Q05P]Q06Q07P6MH1F=D0D0D0D0D0D0D0D0D0D0F7F7F7A6QZZP1PDPWPcPCPuPdECPDPVPePCPwP@PDPVPgPCPwPiPDPVPjPCPwPBPDPVPkP;PDPVPlPAPDPVPmP=PDPVPnP<PDPVPoPpPDPVPqPhPDPVPrPsPDPVPfP?PDPVPbPtPDPVP^fQRdP^PDPVPaPdPaA3N1uX09PdfPRcfORzPxP`P_PwPuPOPPPQPRPSPTPUPWPNPXPYPZP[P\Q05P]MH17BXE>E>D0D0D0D0D0D0D0D0D0F7F7F7P0PDPUPePCP_P@ECPDPUPgPCP_PiPDPUPjPCP_PBPDPUPkP;PDPUPlPAPDPUPmP=PDPUPnP<PDPUPoPpPDPUPqPhPDPUPrPsPDPUPfP?PDPUPbPtPDPUP^fRR{/2^S09PDPUPa12{aR|A3W1wX09PNP{PdPcPzPxP`P_PwPuPOPPPQPRPSPTPVPWPNPXPYPZP[P\Q05MH1F=D0D0D0D0D0D0D0D0D0D0F7F7A6wWWP1PDPSPePCPxP@ECPDPRPgPCPzPiPDPRPjPCPzPBPDPRPkP;PDPRPlPAPDPRPmP=PDPRPnP<PDPRPoPpPDPRPqPhPDPRPrPsPDPRPfP?PDPRPbPtPDPRP^fUR@P^PDPRPaP@PaA3T1xX09P@fTRefSR}P{PdPcPzPxP`P_PwPuPOPPPQPSPTPUPVPWPNPXPYPZMH17BUE>E>D0D0D0D0D0D0D0D0D0F7F7P0PDPQPgPCPcPiECPDPQPjPCPcPBPDPQPkP;PDPQPlPAPDPQPmP=PDPQPnP<PDPQPoPpPDPQPqPhPDPQPrPsPDPQPfP?PDPQPbPtPDPQP^fVR~/2^S0:PDPQPa12~aS0;A3S1zX09PTP~P@PeP}P{PdPcPzPxP`P_PwPuPOPPPRPSPTPUPVPWPNPXPYMH1F=D0D0D0D0D0D0D0D0D0D0F7A6zSSP1PDPOPgPCP{PiECPDPuPjPCP}PBPDPuPkP;PDPuPlPAPDPuPmP=PDPuPnP<PDPuPoPpPDPuPqPhPDPuPrPsPDPuPfP?PDPuPbPtPDPvfYRvP^PDP>PvPaA3P1{X09PQPvfXR>fWRiP~P@PeP}P{PdPcPzPxP`P_PwPOPPPQPRPSPTPUPVPWMH1FAD@D0D0D0D0D0D0D0D0D0F7P0PDPwPjPCPePBECPDPwPkP;PDPwPlPAPDPwPmP=PDPwPnP<PDPwPoPpPDPwPqPhPDPwPrPsPDPwPfP?PDPwPbPtPDPwP^fZRg/2^S0<PDPwPa12gaS0=A3O1}X09PPPgPvP>PiP~P@PeP}P{PdPcPzPxP`P_PuPOPPPQPRPSPTPUPVMH1F=D0D0D0D0D0D0D0D0D0D0A6}OOP1PDP`PjPCP~PBECPDPxPkP;PDPxPlPAPDPxPmP=PDPxPnP<PDPxPoPpPDPxPqPhPDPxPrPsPDPxPfP?PDPxPbPtPDQ08f]RBP^PDPyPBPaA3_1~X09PwPBf\Ryf[RCPgPvP>PiP~P@PeP}P{PdPcPzP`P_PwPuPOPPPQPRPSMH1FAD@D0D0D0D0D0D0D0D0D0P0PDPzPkP;C4PDPzPlPAPDPzPmP=PDPzPnP<PDPzPoPpPDPzPqPhPDPzPrPsPDPzPfP?PDPzPbPtPDPzP^f^Rj/2^S08PDPzPa12jaS0>A3`1iX09P_PjPBPyPCPgPvP>PiP~P@PeP}P{PdPcPxP`P_PwPuPOPPPQPRMH1F=D0D0D0D0D0D0D0D0D0A6i``P1PDPdPkP;C4PDP{PlPAPDP{PmP=PDP{PnP<PDP{PoPpPDP{PqPhPDP{PrPsPDP{PfP?PDP{PbPtPDQ09faR;P^PDP|P;PaA3c1gX09PzP;f`R|f_RkPjPBPyPCPgPvP>PiP~P@PeP}PdPcPzPxP`P_PwPuPOMH1FAD@D0D0D0D0D0D0D0D0P0PDP}PlPAC4PDP}PmP=PDP}PnP<PDP}PoPpPDP}PqPhPDP}PrPsPDP}PfP?PDP}PbPtPDP}P^fbRO/2^S09PDP}Pa12OaS0?A3d1CX09PcPOP;P|PkPjPBPyPCPgPvP>PiP~P@PeP{PdPcPzPxP`P_PwPuMH1F=D0D0D0D0D0D0D0D0A6CddP1PDP@PlPAC4PDP~PmP=PDP~PnP<PDP~PoPpPDP~PqPhPDP~PrPsPDP~PfP?PDP~PbPtPDQ0:feRAP^PDQ0;PAPaA3e1jX09P}PAfdRlfcRuPOP;P|PkPjPBPyPCPgPvP>PiP@PeP}P{PdPcPzPxP`MH1FAD@D0D0D0D0D0D0D0P0PDPiPmP=C4PDPiPnP<PDPiPoPpPDPiPqPhPDPiPrPsPDPiPfP?PDPiPbPtPDPiP^ffR`/2^RwPDPiPa12`aR_A3@1kX09PeP`PAPlPuPOP;P|PkPjPBPyPCPgPvP>P~P@PeP}P{PdPcPzPxMH1F=D0D0D0D0D0D0D0A6k@@P1PDPvPmP=C4PDPgPnP<PDPgPoPpPDPgPqPhPDPgPrPsPDPgPfP?PDPgPbPtPDQ0<fiR=P^PDQ0=P=PaA3>1OX09PiP=fhRmfgRxP`PAPlPuPOP;P|PkPjPBPyPCPvP>PiP~P@PeP}P{PdMH1FAD@D0D0D0D0D0D0P0PDPCPnP<C4PDPCPoPpPDPCPqPhPDPCPrPsPDPCPfP?PDPCPbPtPDPCP^fjRd/2^RzPDPCPa12daRcA3v1uX09P>PdP=PmPxP`PAPlPuPOP;P|PkPjPBPyPgPvP>PiP~P@PeP}P{MH1F=D0D0D0D0D0D0A6uvvP1PDPBPnP<C4PDPjPoPpPDPjPqPhPDPjPrPsPDPjPfP?PDPjPbPtPDQ08fmR<P^PDQ0>P<PaA3y1`X09PCP<flRnfkR{PdP=PmPxP`PAPlPuPOP;P|PkPBPyPCPgPvP>PiP~P@MH1FAD@D0D0D0D0D0P0PDPkPoPpC4PDPkPqPhPDPkPrPsPDPkPfP?PDPkPbPtPDPkP^fnR@/2^R}PDPkPa12@aReA3B1xX09PyP@P<PnP{PdP=PmPxP`PAPlPuPOP;P|PjPBPyPCPgPvP>PiP~MH1F=D0D0D0D0D0A6xBBP1PDP;PoPpC4PDPOPqPhPDPOPrPsPDPOPfP?PDPOPbPtPDQ09fqRpP^PDQ0?PpPaA3|1dX09PkPpfpRofoR~P@P<PnP{PdP=PmPxP`PAPlPuP;P|PkPjPBPyPCPgPvMH1FAD@D0D0D0D0P0PDPuPqPhC4PDPuPrPsPDPuPfP?PDPuPbPtPDPuP^frRv/2^RiPDPuPa12vaR>A3;1{X09P|PvPpPoP~P@P<PnP{PdP=PmPxP`PAPlPOP;P|PkPjPBPyPCPgMH1F=D0D0D0D0A6{;;P1PDPAPqPhC4PDP`PrPsPDP`PfP?PDP`PbPtPDPwfuRw/2^RhPDP_12waA3l1@X09PwftR_fsRqPvPpPoP~P@P<PnP{PdP=PmPxPAPlPuPOP;P|PkPjPBMH17BuFYD0D0D0P0PDPxPrPsC4PDPxPfP?PDPxPbPtPDPxP^fvRBP^PDPxPa12BaRgA3A1~X09PlPBPwP_PqPvPpPoP~P@P<PnP{PdP=PmP`PAPlPuPOP;P|PkPjMH1F=E>D0D0A6~AAP1PDP=PrPsC4PDPdPfP?PDPdPbPtPDPzfyRzP^PDPc12zaRcA3m1vX09PzfxRsfwRrPBPwP_PqPvPpPoP~P@P<PnP{P=PmPxP`PAPlPuPOP;MH1,IxDXD@D0D0P0PDP{PfP?C4PDP{PbPtPDP{P^fzR;P^PDP{PaP;PaA3=1qX09P;PzPsPrPBPwP_PqPvPpPoP~P@P<PnPdP=PmPxP`PAPlPuPOMH17BmE>E>D0A6q==P1PDP<PfP?C4PDP@PbPtPDP}f}R}P^PDPeP}PaA3n1BX09P{P}f|Ref{R?P;PzPsPrPBPwP_PqPvPpPoP~P<PnP{PdP=PmPxP`PAMH1FAD@D0P0PDP~PbPtC4PDP~P^f~RAP^PDP~PaPAPaA3<1rX09PAP}PeP?P;PzPsPrPBPwP_PqPvPpPoP@P<PnP{PdP=PmPxP`MH17BnE>E>A6r<<P1PDPpPbPtC4PDPip+01BRiP^PDP>PiPaA3o1;X09P~Pip+01AR>p+01@RtPAP}PeP?P;PzPsPrPBPwP_PqPpPoP~P@P<PnP{PdP=MH1FAD@P0PDPqP^p+01CR=/2^C4PDPqPaP=PaA3p1?X09P=PiP>PtPAP}PeP?P;PzPsPrPBPwP_PvPpPoP~P@P<PnP{PdMH17BoE>A6?ppP1PDPhp+01ERhP^COPDPgp+01FRgPaA3_1AX09PqPgPhp+01DR^P=PiP>PtPAP}PeP?P;PzPsPrPwP_PqPvPpPoP~P@P<MH1FAP0PDPrPap+01GR</2aC4A3w1tX09P<PgPhP^P=PiP>PtPAP}PeP?P;PzPsPBPwP_PqPvPpPoP~P@MH17B_A6twwP1PDPcp+01IRcPaCOA3s1=X09p+01JRaPcp+01HRDP<PgPhP^P=PiP>PtPAP}PeP?PzPsPrPBPwP_PqPvPpMH17BrP0A3z1^X09#Np+01KRpPaPcPDP<PgPhP^P=PiP>PtPAP}PeP;PzPsPrPBPwP_PqPvMH1,IsA6^zzP1A3?1gX09#NQ00P9A3e1<X09p+01ORvp+01NRqp+01MR_p+01LRwPpPaPcPDP<PgPhP^P=PiP>PAP}PeP?P;PzPsPrPBMH1,IeA6D}}[P1A3A1cP51G2aRBp+01SRrp+01RRsp+01QR@p+01PR~PvPqP_PwPpPaPcPDP<PgPhP=PiP1PtPAP}PeP?P;MH1,I1A6w22[X25PsP@P~PvPqP_PwPpPaPcPDP<PgPhP^PiP>PBPAP}PeP?P;PzMH1,IBP01G4pR0#MPrPsP@P~PvPqP_PwPpPaPcPDP<PgPhP=PiP0PtPAP}PeP?P;MH11G3wR;=6w;P11G8_#Mp+01Vp+01Up+01TPrPsP@P~PvPqP_PwPpPaPcPDPgPh1G7qP=PiP>PtPAP}MH11G6vRA,Sv%WAPvP}P6Q01%dvDcAbv6}CaWVWUP2P1O2n2001000000120000000W1PtP1E`W1X09P2P1O2n2001000000120100000W1P2P1O2n2001000000121000000W1WTP2P1O2n2001000000121000000W1WSP2P1O2n2001000000121000000W1WRP2P1O2n2001000000121000000W1WQP2P1O2n2001000000121000000W1WPP2P1O2n2011000000121000000W1W^P2P1O2n2011000000121000000W1W]P2P1O2n2011000000121000000W1W\P2P1O2n2011000000121000000W1W[P2P1O2n2011000000121000000W1WZP2P1O2n2011000000121000000W1WYP2P1O2n2011000000121000000W1WXP2P1O2n2011000000121000000W1WWP2P1O2n2011000000121000000W1WOP2P1O2n2011000000121000000W1WNP2P1O2n2011000000121000000W1WMP2P1O2n2011000000121000000WLWKX:IX<:XAMX>LXHKXFJX25XCGX5FX7EX;:X@MX=LXGKWJXEJWDX8HX?HXIHX9IW3XBGX4FX6EPPPQPRPSPTPUPVPWPNPXPYPZP[P\Q05P]Q06Q07P6P7P8P3P4P2P1OIX:IX<:XAMX>LXHKXFJX25XCGX5FX7EX;:X@MX=LXGKWJXEJWDX8HX?HXIHX9IW3XBGX4FX6EPPPQPRPSPTPUPVPWPNPXPYPZP[P\Q05P]Q06Q07P6P7P8P3P4P2P1OIX:IX<:XAMX>LXHKXFJX25XCGX5FX7EX;:W@W=WGWJWEWDX8HX?HXIHW9W3WBW4W6o"). Qed.
Lemma step_run p i : UbjRef.step p (run i p UbjRef.init) = run (S i) p UbjRef.init.
Proof.
ltac2:(KReplay.run1 (kr_t_PeUCParseD ()) ["WithHeap"] "h01ih11ph21nh31sp;1p;2p;3p;4p;6g00I[j1;Tg00NBj12Tg00jOj24Tg00Wfj30Tg00joj2:Tg0000j31Tg000dj29Tg00l:j25Tg00lQj46Tg00Vhj67Tg00mdj13Tg00nHj68Tg00ak#;R0g00_1R1P1f0R2g00iR#2R3'4g00\[R4f2R5f1R6g00]fR7705':R8A025731X21P4A02679036R5A1482X3419451523?067P2P3P6P7C6E7%22%32E8X01X10P6P2O2X01X10P6P2O2W0W1o"). Qed.
End WithHeap.
End PEUCLPD.
