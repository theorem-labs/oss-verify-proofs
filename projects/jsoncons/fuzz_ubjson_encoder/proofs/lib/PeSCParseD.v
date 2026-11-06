(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core L5CoreKit
     PmLayout PmModel PmModelFacts PmStatics PmSpecs PmStep PeSpecsS PeCLayout PeCLayoutS PeCSink PeCStatics PeCModel PeCSpecs PeCSpecsS.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef UbjRefFacts.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_PeSCParseD () := "I47Corelib4Init5Logic2eq00I47Corelib4Init5Logic2or00K47Corelib4Init5Logic2eq01K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:PeSCParseD7PESCLPD4lpG1C13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:PeSCParseD7PESCLPD4lpG2C13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:PeSCParseD7PESCLPD4lpG3C13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:PeSCParseD7PESCLPD4lpG4C13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec6UbjRef5pmode00C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec6UbjRef5pmode01C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec6UbjRef5pmode02C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec6UbjRef5pmode07C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec6UbjRef5pmode09C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec6UbjRef5pmode0;C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec6UbjRef5pmode03C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec6UbjRef5pmode05C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec6UbjRef5pmode06C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec6UbjRef5pmode08C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec6UbjRef5pmode04C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec6UbjRef5pmode0:C13~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec;UbjRefFacts8bytes_okC13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:PeSCParseD7PESCLPD4linvC13~~~K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3subC45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init9Datatypes3nat02C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec4getrC13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:PeSCParseD7PESCLPD4lmemC13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec;UbjRefFacts4ginv00C13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec;UbjRefFacts9ginv_initC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec;UbjRefFacts8run_ginvC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec;UbjRefFacts;run_not_badC13~~~K47Corelib4Init5Logic3and01C47Corelib4Init5Logic8eq_ind_rC56Stdlib6ZArith6BinInt1Z6of_natC89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec6UbjRef3runC13~~~I47Corelib4Init5Logic2ex00C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec6UbjRef6haltedC13~~~I47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z3addC89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec6UbjRef5s_badC13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec6UbjRef2st00C13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec6UbjRef4initC13~~~I47Corelib4Init9Datatypes3nat00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02K47Corelib7Numbers7BinNums8positive03I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I47Corelib7Numbers7BinNums1Z00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9HeapIface6creditC13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7PmModel2PM3pst00C13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7PmModel2PM4vstr00C13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7PmModel2PM4strm00C13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PeCModel3PEC3enc00C13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7PeCSink4PESK4sink00C13~~~K47Corelib4Init9Datatypes3nat01C56Stdlib5Arith8PeanoNat3Nat3addC89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec6UbjRef4stepC13~~~C47Corelib4Init3Nat3addC89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec;UbjRefFacts7run_addC13~~~C56Stdlib5Arith8PeanoNat3Nat7add_1_rC47Corelib4Init5Logic6eq_ind".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PESCLPD.
Abbreviation RSEGS := Plain.M.loaded_segments.
Abbreviation AD := PeCLayoutS.CADDR_S.
Abbreviation EE := PeCLayoutS.EADDR_S.
Definition LPHEAD : Z := 0x385b4.
Definition LPRET : Z := 0x3882c.

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
  getr R1 (PMK.reg 2) = Z_to_bv 64 (sp - 128) /\ getr R1 (PMK.reg 8) = Z_to_bv 64 (fb + 48) /\ getr R1 (PMK.reg 9) = Z_to_bv 64 (fb + 16)
  /\ getr R1 (PMK.reg 18) = Z_to_bv 64 (fb + 440) /\ getr R1 (PMK.reg 19) = Z_to_bv 64 (fb + 72)
  /\ getr R1 (PMK.reg 20) = Z_to_bv 64 10 /\ getr R1 (PMK.reg 21) = Z_to_bv 64 79832 /\ getr R1 (PMK.reg 22) = Z_to_bv 64 9 /\ getr R1 (PMK.reg 23) = Z_to_bv 64 256
  /\ getr R1 (PMK.reg 24) = Z_to_bv 64 93 /\ getr R1 (PMK.reg 25) = Z_to_bv 64 7 /\ getr R1 (PMK.reg 26) = Z_to_bv 64 5 /\ getr R1 (PMK.reg 27) = Z_to_bv 64 125
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
ltac2:(KReplay.run1 (kr_t_PeSCParseD ()) ["WithHeap"] "p'0h01mi001pp;3p;2p;1g0000j30Tg000Jj21Tg000dj26Tg001>j35Tg001Xj38Tg0022j1;Tg003Dj1:Tg004Vj1?Tg005hj1>Tf5R0f4R1f3R230f2R3f1R4f0R530'1p=2f6R6?001A0234/15'1p=3A0601A0234'1/15p=4A0123/14/15p=<A53459812p=9A83459812p=71145,13p==g007:R3P3P3P5g008HR4P3P5g009VR2P3P5g00:dR1P3P5g00<2R6P3P5g00=@R0E2F3P3P5g00>NR7P3P5g00?\R8P3P5g00@jR9P3P5g00B8R:P3P5g00CFR;P3P5g00DTR<E2F4F4D<P5A0344R=P3P4P2P3P4P1P3P4P6P3P4P0E2F3R>'1P3P4P7P3P4P8P3P4P9P3P4P:P3P4P;P3P4P<E2F4F4163495=>35A0324R>A0322R=P3P2P1P3P2P6A0320F3R?'1R@'1P3P2P7P3P2P8P3P2P9P3P2P:P3P2P;P3P2P<E2F4F4P>P@P=P?1632D935P3P7P4P3P7P2P3P7P1P3P7P6A0370F3F3A0377R?A0378R='1R@P3P7P9P3P7P:P3P7P;P3P7P<E2F4R>'1P@P>163795?=D9P3P;P4P3P;P2P3P;P1P3P;P6A03;0F3F3P3P;P7P3P;P8E2R=P3P;P9P3P;P:E2R?A03;;R>A03;<R@'1RA'1RB'1P=PBP?PAP>P@163;D9D7P3P8P4P3P8P2P3P8P1P3P8P6A0380F3F3A0387R@A0388R>'1RAP3P8P9P3P8P:P3P8P;P3P8P<E2F4R?'1PAP?163898@>D9P3P9P4P3P9P2P3P9P1P3P9P6A0390F3F3P3P9P7P3P9P8E2R>A0399R@A039:R?'1RAP3P9P;P3P9P<E2RB'1R='1P>P=163995@?95ABD7A0314RBA0312RAA0311R?P3P1P6P3P1P0E2R@'1R='1R>'1P3P1P7P3P1P8P3P1P9P3P1P:P3P1P;P3P1P<E2F4F4PBP>PAP=163195?@D735P3P:P4P3P:P2P3P:P1P3P:P6A03:0F3F3P3P:P7P3P:P8E2R@A03:9R?A03::R='1RAP3P:P;P3P:P<E2R>'1RB'1P@PB163:98?=95A>D7A0364R>A0362RAA0361R=A0366R?A0360RB'1R@'1RC'1RD'1P3P6P7P3P6P8P3P6P9P3P6P:P3P6P;P3P6P<E2F4F4P>PDPAPCP=P@P?PB1636D9D735P3P<P4P3P<P2P3P<P1P3P<P6A03<0F3F3P3P<P7P3P<P8E2RBP3P<P9P3P<P:E2R?A03<;R@A03<<R='1RC'1RA'1PBPAP?PCP@P=163<D7D7A0304R4A0302R2A0301R1A0306R6A0300R='1R@'1RC'1R?'1P3P0P7P3P0P8P3P0P9P3P0P:P3P0P;P3P0P<E2F4F4P4P?P2PCP1P@P6P=1630D7D735n01100000;0000000000000000000000%;5%:5%?5%>5'13=eX03P5O1X03P5O1W0o"). Qed.

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
ltac2:(KReplay.run1 (kr_t_PeSCParseD ()) ["WithHeap"] "p'0h01ih11Hh22X1h33LBXh41Mh52M1h61Rh72R1h83cath92crh:3cr1h;1eh<2e1h=2enh>3en1h?2fbh@1khA2k1hB5modelhC6model1hD1phE1shF2s1hG2smhH3sm1hI2sphJ3strhK2BPhL2LIhM2_HhN3_H0hO3_H1hP4_H10hQ4_H11hR4_H12hS4_H13hT4_H14hU4_H15hV3_H2hW3_H3hX3_H4hY3_H5hZ3_H6h[3_H7h\3_H8h]3_H9i001xp%0p;1p;2p;Ip;Hp;5p;3p;4p;6g00Ebj19Tg00FGj1>Tg00Flj1MTg00GJj1WTg00Gmj2^Tg00HYj1]Tg00I;j2\Tg00I[j1QTg00J;j1[Tg00KOlIZTg00Laj1HTg00M?j2VTg00M\j2ETg00NBj1;Tg00Naj22Tg00OilH1Tg00Q;j2STg00RMj1dTg00Sbj5cTg00U6j3bTg00VMj4aTg00Vhj6`Tg00WFj1_Tg0000j34Tg00Wfj3TTg00Y0S00j2LTg00YJj1KTg00ZWR0j28Tg00[2j2RTg00[Oj1UTf0R1#9#9p=J%;1#;p=Df1R2%_1'Ep=:f3R3f2R4/22;41p=5%>1#>p=F%H1,E2p=Cg00\[R5g00]fS019T21744p=3f6R6f5R7f4R8'2;43g00_1R9/L4g00_PR:%K2g00`0R;34/81'8'8p==1234=482/81p=012781R42,E3546/81p=61S42%U1=4:;'8p=71L94%K2=4:;/81'8p=A12831242547/81p=<12831R21,E4547p=B128394671L94%K2=4:;/81'8'8p=?12429483/81p=@A4678A4342/81'8p=Y%K2=4:;/81p=IA48341L92/81'8p=X12219434p=P1L91p=OQ019T21p=G%K1=4:;p=N%U1=4:;p=eg00`PR;#9R<#>R=#MR>%9<R<#9R?#9R@#JRA#MRB#WRC'^RD%M?#W#]\CR?g00a5REg00akRF/\F#QS02g00bIRG%QFS03g00cTRHg00d_S04g00ekRIg00g7RJg00hDRKQ02Q03Q04Q02Q03Q04f@RL#[fIRMfHRNfGROfFRPfERQfDRRfCRSfBRTfARUPLf?RVf>RWf=RXf<RYf;RZf:R[f9R\f8R]f7S05P6P7P8P3P4P2MIZP0PCPZg00iR#DR^,:>R_%9ARA#HR`,VQ,EBC5PCPZ%;^R^#;Ra#D#DRb,:>RcPBPR%>;R;#9Rd#9#J#HRePCPZ%;bRb,:>RfPBPR%H@R@PCPZ%;b#D#D#D#DRb,:>RgPBPR%>d#F#9#J#HRdPCPZ%;bRb,:>RhPBPR%><R<#9#J#HRiPCPZ%;bRb,:>Rj%9=,CBRkPCPZ%;bRb,:>Rl%><#9#>#F#F#9#F#9#J,CBRmPCPZ%;bRb,:>Rn1CB<R<PCPZ%;bRb,:>Ro%9A,CBRAPCPZ%;bRb,:>Rp%F=#9#>,CBRqPCPZ%;bRb,:>Rr%>;R;,CBRsPCPZ%;bRb,:>Rt1CB=R=PCPZ%;b,:>Rb%F;#9#>,CBR;PCPZ1:>^R^fJRu/2^RvPCPZ1:>aRa12uaR>A3\1SX09P]PuPMPNPOPPPQPRPSPTPUPLPVPWPXPYP[P\P]Q05P6P7P8P3P4MH1F=D0D0D0D0D0D0D0D0D0F6F6F6F6A7S\\P1PCPXP_1VO`,EBC5PCPWPcPBPOPePCPWPfPBPOP@PCPWPgPBPOPdPCPWPhPBPOPiPCPWPjPkPCPWPlPmPCPWPnP<PCPWPoPAPCPWPpPqPCPWPrPsPCPWPtP=PCPWPbP;PCPWP^fMR`P^PCPWPaP`PaA3Y1PX09P`fLR_fKRwPuPMPNPOPPPQPRPSPTPUPLPVPXPYPZP[P\P]Q05P6P7MH17AZE<E<D0D0D0D0D0D0D0D0F6F6F6F6P0PCPVPcPBPNPeEBPCPVPfPBPNP@PCPVPgPBPNPdPCPVPhPBPNPiPCPVPjPkPCPVPlPmPCPVPnP<PCPVPoPAPCPVPpPqPCPVPrPsPCPVPtP=PCPVPbP;PCPVP^fNRx/2^S06PCPVPa12xaRyA3X1OX09PYPxP`P_PwPuPMPNPOPPPQPRPSPTPUPLPWPXPYPZP[P\P]Q05P6MH1F=D0D0D0D0D0D0D0D0D0F6F6F6A7OXXP1PCPUPcPBPuPeEBPCPTPfPBPwP@PCPTPgPBPwPdPCPTPhPBPwPiPCPTPjPkPCPTPlPmPCPTPnP<PCPTPoPAPCPTPpPqPCPTPrPsPCPTPtP=PCPTPbP;PCPTP^fQReP^PCPTPaPePaA3L1uX09PefPRcfORzPxP`P_PwPuPMPNPOPPPQPRPSPUPLPVPWPXPYPZP[P\MH17AVE<E<D0D0D0D0D0D0D0D0F6F6F6P0PCPSPfPBP_P@EBPCPSPgPBP_PdPCPSPhPBP_PiPCPSPjPkPCPSPlPmPCPSPnP<PCPSPoPAPCPSPpPqPCPSPrPsPCPSPtP=PCPSPbP;PCPSP^fRR{/2^S07PCPSPa12{aR|A3U1wX09PLP{PePcPzPxP`P_PwPuPMPNPOPPPQPRPTPUPLPVPWPXPYPZP[MH1F=D0D0D0D0D0D0D0D0D0F6F6A7wUUP1PCPQPfPBPxP@EBPCPPPgPBPzPdPCPPPhPBPzPiPCPPPjPkPCPPPlPmPCPPPnP<PCPPPoPAPCPPPpPqPCPPPrPsPCPPPtP=PCPPPbP;PCPPP^fUR@P^PCPPPaP@PaA3R1xX09P@fTRffSR}P{PePcPzPxP`P_PwPuPMPNPOPQPRPSPTPUPLPVPWPXMH17ASE<E<D0D0D0D0D0D0D0D0F6F6P0PCPOPgPBPcPdEBPCPOPhPBPcPiPCPOPjPkPCPOPlPmPCPOPnP<PCPOPoPAPCPOPpPqPCPOPrPsPCPOPtP=PCPOPbP;PCPOP^fVR~/2^S08PCPOPa12~aS09A3Q1zX09PRP~P@PfP}P{PePcPzPxP`P_PwPuPMPNPPPQPRPSPTPUPLPVPWMH1F=D0D0D0D0D0D0D0D0D0F6A7zQQP1PCPMPgPBP{PdEBPCPuPhPBP}PiPCPuPjPkPCPuPlPmPCPuPnP<PCPuPoPAPCPuPpPqPCPuPrPsPCPuPtP=PCPuPbP;PCPvfYRvP^PCP>PvPaA3N1{X09POPvfXR>fWRdP~P@PfP}P{PePcPzPxP`P_PwPMPNPOPPPQPRPSPTPUMH1F?D@D0D0D0D0D0D0D0D0F6P0PCPwPhPBPfPiEBPCPwPjPkPCPwPlPmPCPwPnP<PCPwPoPAPCPwPpPqPCPwPrPsPCPwPtP=PCPwPbP;PCPwP^fZRg/2^S0:PCPwPa12gaS0;A3M1}X09PNPgPvP>PdP~P@PfP}P{PePcPzPxP`P_PuPMPNPOPPPQPRPSPTMH1F=D0D0D0D0D0D0D0D0D0A7}MMP1PCP`PhPBP~PiEBPCPxPjPkPCPxPlPmPCPxPnP<PCPxPoPAPCPxPpPqPCPxPrPsPCPxPtP=PCPxPbP;PCQ06f]RiP^PCPyPiPaA3_1~X09PwPif\Ryf[RBPgPvP>PdP~P@PfP}P{PePcPzP`P_PwPuPMPNPOPPPQMH1F?D@D0D0D0D0D0D0D0D0P0PCPzPjPkC5PCPzPlPmPCPzPnP<PCPzPoPAPCPzPpPqPCPzPrPsPCPzPtP=PCPzPbP;PCPzP^f^Rh/2^S06PCPzPa12haS0<A3`1dX09P_PhPiPyPBPgPvP>PdP~P@PfP}P{PePcPxP`P_PwPuPMPNPOPPMH1F=D0D0D0D0D0D0D0D0A7d``P1PCPePjPkC5PCP{PlPmPCP{PnP<PCP{PoPAPCP{PpPqPCP{PrPsPCP{PtP=PCP{PbP;PCQ07faRkP^PCP|PkPaA3c1gX09PzPkf`R|f_RjPhPiPyPBPgPvP>PdP~P@PfP}PePcPzPxP`P_PwPuPMMH1F?D@D0D0D0D0D0D0D0P0PCP}PlPmC5PCP}PnP<PCP}PoPAPCP}PpPqPCP}PrPsPCP}PtP=PCP}PbP;PCP}P^fbRM/2^S07PCP}Pa12MaS0=A3e1BX09PcPMPkP|PjPhPiPyPBPgPvP>PdP~P@PfP{PePcPzPxP`P_PwPuMH1F=D0D0D0D0D0D0D0A7BeeP1PCP@PlPmC5PCP~PnP<PCP~PoPAPCP~PpPqPCP~PrPsPCP~PtP=PCP~PbP;PCQ08feRmP^PCQ09PmPaA3f1hX09P}PmfdRlfcRuPMPkP|PjPhPiPyPBPgPvP>PdP@PfP}P{PePcPzPxP`MH1F?D@D0D0D0D0D0D0P0PCPdPnP<C5PCPdPoPAPCPdPpPqPCPdPrPsPCPdPtP=PCPdPbP;PCPdP^ffR`/2^RwPCPdPa12`aR_A3@1jX09PfP`PmPlPuPMPkP|PjPhPiPyPBPgPvP>P~P@PfP}P{PePcPzPxMH1F=D0D0D0D0D0D0A7j@@P1PCPvPnP<C5PCPgPoPAPCPgPpPqPCPgPrPsPCPgPtP=PCPgPbP;PCQ0:fiR<P^PCQ0;P<PaA3>1MX09PdP<fhRnfgRxP`PmPlPuPMPkP|PjPhPiPyPBPvP>PdP~P@PfP}P{PeMH1F?D@D0D0D0D0D0P0PCPBPoPAC5PCPBPpPqPCPBPrPsPCPBPtP=PCPBPbP;PCPBP^fjRe/2^RzPCPBPa12eaRcA3v1uX09P>PeP<PnPxP`PmPlPuPMPkP|PjPhPiPyPgPvP>PdP~P@PfP}P{MH1F=D0D0D0D0D0A7uvvP1PCPiPoPAC5PCPhPpPqPCPhPrPsPCPhPtP=PCPhPbP;PCQ06fmRAP^PCQ0<PAPaA3y1`X09PBPAflRofkR{PeP<PnPxP`PmPlPuPMPkP|PjPiPyPBPgPvP>PdP~P@MH1F?D@D0D0D0D0P0PCPjPpPqC5PCPjPrPsPCPjPtP=PCPjPbP;PCPjP^fnR@/2^R}PCPjPa12@aRfA3i1xX09PyP@PAPoP{PeP<PnPxP`PmPlPuPMPkP|PhPiPyPBPgPvP>PdP~MH1F=D0D0D0D0A7xiiP1PCPkPpPqC5PCPMPrPsPCPMPtP=PCPMPbP;PCQ07fqRq/2^RpPCQ0=12qaA3|1eX09PqfpR~foRdP@PAPoP{PeP<PnPxP`PmPlPuPkP|PjPhPiPyPBPgPvMH17AjFYD0D0D0P0PCPuPrPsC5PCPuPtP=PCPuPbP;PCPuP^frRvP^PCPuPa12vaR>A3k1{X09P|PvPqP~PdP@PAPoP{PeP<PnPxP`PmPlPMPkP|PjPhPiPyPBPgMH1F=E<D0D0A7{kkP1PCPmPrPsC5PCP`PtP=PCP`PbP;PCPwfuRwP^PCP_12waR_A3l1@X09PwftRsfsRrPvPqP~PdP@PAPoP{PeP<PnPxPmPlPuPMPkP|PjPhPiMH1,IuDXD@D0D0P0PCPxPtP=C5PCPxPbP;PCPxP^fvRiP^PCPxPaPiPaA3m1dX09PiPwPsPrPvPqP~PdP@PAPoP{PeP<PnP`PmPlPuPMPkP|PjPhMH17AlE<E<D0A7dmmP1PCP<PtP=C5PCPePbP;PCPzfyRzP^PCPcPzPaA3n1vX09PxPzfxRcfwR=PiPwPsPrPvPqP~PdP@PAPoP{P<PnPxP`PmPlPuPMPkMH1F?D@D0P0PCP{PbP;C5PCP{P^fzRkP^PCP{PaPkPaA3<1rX09PkPzPcP=PiPwPsPrPvPqP~PdP@PAPoPeP<PnPxP`PmPlPuPMMH17AnE<E<A7r<<P1PCPAPbP;C5PCP}f}R}P^PCPfP}PaA3o1iX09P{P}f|Rff{R;PkPzPcP=PiPwPsPrPvPqP~PdPAPoP{PeP<PnPxP`PmMH1F?D@P0PCPdP^f~Rm/2^C5PCPdPaPmPaA3A1=X09PmP}PfP;PkPzPcP=PiPwPsPrPvPqP~P@PAPoP{PeP<PnPxP`MH17AoE<A7=AAP1PCPpp+01ARpP^CPPCP>p+01BR>PaA3~1kX09PdP>Ppp+01@R^PmP}PfP;PkPzPcP=PiPwPsPrPqP~PdP@PAPoP{PeP<MH1F?P0PCPrPap+01CR</2aC5A3q1;X09P<P>PpP^PmP}PfP;PkPzPcP=PiPwPsPvPqP~PdP@PAPoP{PeMH17A~A7;qqP1PCP_p+01ER_PaCPA3s1mX09p+01FRaP_p+01DRCP<P>PpP^PmP}PfP;PkPzPcP=PwPsPrPvPqP~PdP@PAMH17ArP0A3w1^X09#Op+01GRAPaP_PCP<P>PpP^PmP}PfP;PkPzPcPiPwPsPrPvPqP~PdP@MH1,IsA7^wwP1A3=1>X09#OQ00P9A3c1<X09p+01KR@p+01JRdp+01IR~p+01HRqPAPaP_PCP<P>PpP^PmP}PfPkPzPcP=PiPwPsPrPvMH1,IcA7Czz[P1A3k1_P51G2aRvp+01ORrp+01NRsp+01MRep+01LR{P@PdP~PqPAPaP_PCP<P>PpPmP}P1P;PkPzPcP=PiMH1,I1A7q22[X25PsPeP{P@PdP~PqPAPaP_PCP<P>PpP^P}PfPvPkPzPcP=PiPwMH1,IvP01G4AR0#NPrPsPeP{P@PdP~PqPAPaP_PCP<P>PpPmP}P0P;PkPzPcP=PiMH11G3qRi=7qiP11G8~#Np+01Rp+01Qp+01PPrPsPeP{P@PdP~PqPAPaP_PCP>Pp1G7dPmP}PfP;PkPzMH11G6@Rk,S@%ekP@PzP6Q01%d@DcAb@6zCaWUWTP2P1O2n2001000000120000000W1P;P1E`W1X09P2P1O2n2001000000120100000W1P2P1O2n2001000000121000000W1WSP2P1O2n2001000000121000000W1WRP2P1O2n2001000000121000000W1WQP2P1O2n2001000000121000000W1WPP2P1O2n2011000000121000000W1W]P2P1O2n2011000000121000000W1W\P2P1O2n2011000000121000000W1W[P2P1O2n2011000000121000000W1WZP2P1O2n2011000000121000000W1WYP2P1O2n2011000000121000000W1WXP2P1O2n2011000000121000000W1WWP2P1O2n2011000000121000000W1WVP2P1O2n2011000000121000000W1WOP2P1O2n2011000000121000000W1WNP2P1O2n2011000000121000000W1WMP2P1O2n2011000000121000000WLWKX:GX<:XAKX>JXHIXFHX25XCEX5?X7DX;:X@KX=JXGIWJXEHWDX8FX?FXIFX9GW3XBEX4?X6DPNPOPPPQPRPSPTPUPLPVPWPXPYPZP[P\P]Q05P6P7P8P3P4P2P1OIX:GX<:XAKX>JXHIXFHX25XCEX5?X7DX;:X@KX=JXGIWJXEHWDX8FX?FXIFX9GW3XBEX4?X6DPNPOPPPQPRPSPTPUPLPVPWPXPYPZP[P\P]Q05P6P7P8P3P4P2P1OIX:GX<:XAKX>JXHIXFHX25XCEX5?X7DX;:W@W=WGWJWEWDX8FX?FXIFW9W3WBW4W6o"). Qed.
Lemma step_run p i : UbjRef.step p (run i p UbjRef.init) = run (S i) p UbjRef.init.
Proof.
ltac2:(KReplay.run1 (kr_t_PeSCParseD ()) ["WithHeap"] "h01ih11ph21nh31sp;1p;2p;3p;4p;6g00I[j1;Tg00NBj12Tg00j1j24Tg00Wfj30Tg00jQj2:Tg0000j31Tg000dj29Tg00k\j25Tg00l3j46Tg00Vhj67Tg00mFj13Tg00mjj68Tg00ak#;R0g00_1R1P1f0R2g00iR#2R3'4g00\[R4f2R5f1R6g00]fR7705':R8A025731X21P4A02679036R5A1482X3419451523?067P2P3P6P7C6E7%22%32E8X01X10P6P2O2X01X10P6P2O2W0W1o"). Qed.
End WithHeap.
End PESCLPD.
