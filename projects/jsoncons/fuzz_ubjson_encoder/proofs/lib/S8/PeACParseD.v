(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceAEx IcptIfaceA LibIface AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsA L5CoreAS8 L5CoreSpecsAS8 L5StepARS8 L5CoreBRS8 L5ADetailHRS8.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout PmLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PmModel PmModelFacts PmStatics PmStaticsA PmSpecs PmSpecsA PmSpecsAX PeSpecsAa PnStatics PmCertKitG PmModelFactsA PmStep PeStepA PmParStep PmParKit PeASrcKit PeAParKit LibIfaceAB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayout PeCLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PeCSink PeCModel PeCSpecs PeCFrame PeCSinkA PeCModelA PeCStaticsA PeCSpecsA PeCSpecsAa PeCFrameA PmAUarK.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.Spec Require Import UbjRefFactsS8.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PEACLPD.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := Asan.M.loaded_segments.
Abbreviation AD := PeCLayoutA.CADDR_A.
Abbreviation AAD := PeCLayoutA.CAADDR_A.
Abbreviation EE := PeCLayoutA.EADDR_A.
Definition LPHEAD : Z := 0xb2720.
Definition LPEXIT : Z := 0xb2620.
Definition LPRET : Z := 0xb2e48.
Definition LPJOIN : Z := 0xb2cc8.
Definition JT : Z := 143440.
Definition SB : Z := 2147450880.

Definition own (E : Z) (R : bvmap 5 word) (M : word -> option byte) : Prop :=
  L5.u64_at RSEGS M (E - 8) (bv_unsigned (getr R (reg 1))) /\ L5.u64_at RSEGS M (E - 16) (bv_unsigned (getr R (reg 8)))
  /\ L5.u64_at RSEGS M (E - 24) (bv_unsigned (getr R (reg 9))) /\ L5.u64_at RSEGS M (E - 32) (bv_unsigned (getr R (reg 18)))
  /\ L5.u64_at RSEGS M (E - 40) (bv_unsigned (getr R (reg 19))) /\ L5.u64_at RSEGS M (E - 48) (bv_unsigned (getr R (reg 20)))
  /\ L5.u64_at RSEGS M (E - 56) (bv_unsigned (getr R (reg 21))) /\ L5.u64_at RSEGS M (E - 64) (bv_unsigned (getr R (reg 22)))
  /\ L5.u64_at RSEGS M (E - 72) (bv_unsigned (getr R (reg 23))) /\ L5.u64_at RSEGS M (E - 80) (bv_unsigned (getr R (reg 24)))
  /\ L5.u64_at RSEGS M (E - 88) (bv_unsigned (getr R (reg 25))) /\ L5.u64_at RSEGS M (E - 96) (bv_unsigned (getr R (reg 26)))
  /\ L5.u64_at RSEGS M (E - 104) (bv_unsigned (getr R (reg 27))).
Definition ocell (E : Z) (a : Z) : Prop := E - 104 <= a < E.
Lemma own_agree E R M1 M1' : 0 <= E - 104 -> E <= 2 ^ 64 ->
  own E R M1 -> (forall a, ocell E a -> M1' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> own E R M1'.
Proof.
  intros H0 H1 (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13) AG. unfold own, ocell in *.
  repeat split; (eapply L5C.u64_at_agree; [ | | | eassumption]; [intros j Hj; apply AG; lia | lia | lia]).
Qed.

Definition lspill (M : word -> option byte) (E F op ov oec : Z) : Prop :=
  L5.u64_at RSEGS M (E - 248) (F + 32) /\ L5.u64_at RSEGS M (E - 240) 3 /\ L5.u64_at RSEGS M (E - 232) 1 /\ L5.u64_at RSEGS M (E - 224) 0
  /\ L5.u64_at RSEGS M (E - 216) ((op + 328) / 8 + 2147450880) /\ L5.u64_at RSEGS M (E - 208) (op + 328)
  /\ L5.u64_at RSEGS M (E - 200) (ov / 8 + 2147450880) /\ L5.u64_at RSEGS M (E - 192) ((op + 360) / 8 + 2147450880)
  /\ L5.u64_at RSEGS M (E - 184) (op + 360) /\ L5.u64_at RSEGS M (E - 176) F /\ L5.u64_at RSEGS M (E - 168) (op + 24)
  /\ L5.u64_at RSEGS M (E - 160) F /\ L5.u64_at RSEGS M (E - 152) (oec / 8 + 2147450880) /\ L5.u64_at RSEGS M (E - 144) ov
  /\ L5.u64_at RSEGS M (E - 136) ((op + 8) / 8 + 2147450880) /\ L5.u64_at RSEGS M (E - 112) F.
Lemma lspill_agree M M' E F op ov oec : 0 <= E - 256 -> E <= 2 ^ 64 ->
  lspill M E F op ov oec -> (forall a, E - 256 <= a < E - 104 -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> lspill M' E F op ov oec.
Proof.
  intros H0 H1 (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & C14 & C15 & C16) AG. unfold lspill in *.
  repeat split; (eapply L5C.u64_at_agree; [ | | | eassumption]; [intros j Hj; apply AG; lia | lia | lia]).
Qed.

Definition lregs (R R1 : bvmap 5 word) (E op oec F : Z) : Prop :=
  getr R1 (reg 2) = Z_to_bv 64 (E - 256) /\ getr R1 (reg 8) = Z_to_bv 64 E /\ getr R1 (reg 9) = Z_to_bv 64 (E - 256)
  /\ getr R1 (reg 18) = Z_to_bv 64 ((op + 368) / 8 + 2147450880) /\ getr R1 (reg 19) = Z_to_bv 64 oec /\ getr R1 (reg 20) = Z_to_bv 64 JT
  /\ getr R1 (reg 21) = Z_to_bv 64 op /\ getr R1 (reg 22) = Z_to_bv 64 2147450880 /\ getr R1 (reg 23) = Z_to_bv 64 (op + 8)
  /\ getr R1 (reg 24) = Z_to_bv 64 (op + 9) /\ getr R1 (reg 25) = Z_to_bv 64 (op + 368) /\ getr R1 (reg 26) = Z_to_bv 64 ((op + 9) / 8 + 2147450880)
  /\ getr R1 (reg 27) = Z_to_bv 64 (F / 8 + 2147450880)
  /\ getr R1 (reg 3) = getr R (reg 3) /\ getr R1 (reg 4) = getr R (reg 4).

Definition top_mode (X : st) : pmode := ps_mode (hd (PS Mroot 0 0 0) (s_stk X)).
Definition lpG1 (m : pmode) : Prop := m = Mroot \/ m = Maccept \/ m = Mval \/ m = Mtval \/ m = Mival.
Definition lpG2 (m : pmode) : Prop := m = Marray \/ m = Mtarray.
Definition lpG3 (m : pmode) : Prop := m = Mkey \/ m = Mtkey.
Definition lpG4 (m : pmode) : Prop := m = Miarray \/ m = Mikey.
Lemma lp_split m : lpG1 m \/ lpG2 m \/ lpG3 m \/ lpG4 m.
Proof. unfold lpG1, lpG2, lpG3, lpG4. destruct m; tauto. Qed.

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (HI : asan_iface) (P : PESKA.sink_policyA).

Abbreviation crun_preA := (PECA.crun_preA RSEGS AD AAD EE L ar P).
Abbreviation pot_allA := (PECA.pot_allA L ar P).

Definition apkont (K : TSet) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z))
           (cr : credit) (sp r fb : Z) (p : list Z) (s : PM.pst) (str : PM.vstr) (sm : PM.strm) (en : PEC.enc) (k : PESK.sink) (e : bool) : Prop :=
  forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (n : nat)
         (s' : PM.pst) (sm' : PM.strm) (en' : PEC.enc) (k' : PESK.sink) (e' : bool) (cr' : credit),
    regs_preserved R R' ->
    halted (run n p UbjRef.init) = true ->
    PM.parser_at RSEGS AD PMSPA.accA PMSPA.annA M' (PMSPA.o_p AD fb) (PMSPA.o_is AD fb) s' /\ PM.iss_at RSEGS AD PMSPA.accA M' (PMSPA.o_is AD fb) str sm'
    /\ PECA.enc_atA RSEGS EE L ar M' (PMSPA.o_v AD fb) fb en' /\ PESKA.sink_atA RSEGS L ar P M' (PESK.o_sink EE fb) k'
    /\ PMSTA.base_okA RSEGS AD M' /\ PESTA.err_okA RSEGS AD AAD EE M' e' /\ L5.defined M' (PMSPA.o_ec AD fb) 16
    /\ s_lo (run n p UbjRef.init) <= PESK.sk_z k' <= s_hi (run n p UbjRef.init) ->
    PMSPA.src_step (PM.p_src s) (PM.p_src s') sm sm' -> (e = true -> e' = true) ->
    L5CA.ahpres L ar LBX FF sp (PMSPA.pm_scr 10) (PEC.W_crun AD EE fb) M M' ->
    PMSP.credit_keep cr cr' (pot_allA s en k) (PESKA.spa_pot P (PESK.sk_c k')) ->
    model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' -> ri_inv HI (PEC.owned s' en' k' ++ LBX) FF LK' cr' Aw' M' (vml_of model') ->
    srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx' R' r M' model') K.

Definition apctx (K : TSet) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z))
           (cr : credit) (sp r fb cat : Z) (p : list Z) (s : PM.pst) (str : PM.vstr) (sm : PM.strm) (en : PEC.enc) (k : PESK.sink) (e : bool) : Prop :=
  ri_inv HI (PEC.owned s en k ++ LBX) FF LK cr Aw M (vml_of model) /\ L5CA.amodel_ok Aw model /\ K [] /\ PMSPA.entryA AD L ar R M sp r 10
  /\ PMSPA.ffroomA 10 FF LK /\ PMSPA.ffrsA FF sp /\ PECA.frame_ok5 FF fb /\ sp mod 32 = 0 /\ PECSPA.args3 AD tt R fb
  /\ crun_preA M fb p UbjRef.init s str sm en k e cat /\ incl (PM.vs_own str) LBX /\ PECSPA.payload_ok p
  /\ (forall n, PESKA.spa_hb P (s_hi (run n p UbjRef.init))) /\ PMSP.credit_le (pot_allA s en k) cr
  /\ apkont K R M model LBX FF LK Aw cr sp r fb p s str sm en k e.

Definition aframe (R : bvmap 5 word) (M : word -> option byte) (model : Model) (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z))
           (cr : credit) (sp : Z) (s : PM.pst) (en : PEC.enc) (k : PESK.sink) (F fl : Z) (LK2 : list fframe) (M2 : word -> option byte) (model2 : Model) : Prop :=
  PMAUK.gctx L ar HI LBX FF LK Aw sp (PMSPA.pm_scr 10) (sp - 256) (sp - 104) sp (ocell sp) (own sp R) F fl 1 LK2 M2 model2 cr (PEC.owned s en k).

Definition lmem (R : bvmap 5 word) (M : word -> option byte) (model : Model) (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z))
           (cr : credit) (sp fb cat : Z) (p : list Z) (s : PM.pst) (str : PM.vstr) (sm : PM.strm) (en : PEC.enc) (k : PESK.sink) (e : bool) (F : Z)
           (M1 : word -> option byte) (model1 : Model) (LK1 : list fframe) (Aw1 : list (Z * Z)) (X1 : st)
           (s1 : PM.pst) (sm1 : PM.strm) (en1 : PEC.enc) (k1 : PESK.sink) (e1 : bool) (cr1 : credit) : Prop :=
  PMAUK.binv L ar HI M model LBX FF LK Aw sp (PMSPA.pm_scr 10) (sp - 256) (own sp R) F 1 (PEC.W_crun AD EE fb) (PEC.owned s1 en1 k1) M1 model1 LK1 cr1 Aw1
  /\ crun_preA M1 fb p X1 s1 str sm1 en1 k1 e1 cat
  /\ lspill M1 sp F (PMSPA.o_p AD fb) (PMSPA.o_v AD fb) (PMSPA.o_ec AD fb)
  /\ PMSPA.src_step (PM.p_src s) (PM.p_src s1) sm sm1 /\ (e = true -> e1 = true)
  /\ PMSP.credit_keep cr cr1 (pot_allA s en k) (pot_allA s1 en1 k1).

Definition alinv (R : bvmap 5 word) (M : word -> option byte) (model : Model) (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z))
           (cr : credit) (sp fb cat : Z) (p : list Z) (s : PM.pst) (str : PM.vstr) (sm : PM.strm) (en : PEC.enc) (k : PESK.sink) (e : bool) (F : Z)
           (R1 : bvmap 5 word) (M1 : word -> option byte) (model1 : Model) (LK1 : list fframe) (Aw1 : list (Z * Z)) (X1 : st)
           (s1 : PM.pst) (sm1 : PM.strm) (en1 : PEC.enc) (k1 : PESK.sink) (e1 : bool) (cr1 : credit) : Prop :=
  lregs R R1 sp (PMSPA.o_p AD fb) (PMSPA.o_ec AD fb) F
  /\ (exists i, X1 = run i p UbjRef.init) /\ halted X1 = false
  /\ lmem R M model LBX FF LK Aw cr sp fb cat p s str sm en k e F M1 model1 LK1 Aw1 X1 s1 sm1 en1 k1 e1 cr1.

Definition aiter_ok (G : pmode -> Prop) : Prop :=
  forall (K : TSet) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z))
         (cr : credit) (sp r fb cat : Z) (p : list Z) (s : PM.pst) (str : PM.vstr) (sm : PM.strm) (en : PEC.enc) (k : PESK.sink) (e : bool)
         (F fl : Z) (LK2 : list fframe) (M2 : word -> option byte) (model2 : Model),
    PESKA.spa_mode P -> PESKA.sink_policyA_ok L P ->
    apctx K R M model LBX FF LK Aw cr sp r fb cat p s str sm en k e ->
    aframe R M model LBX FF LK Aw cr sp s en k F fl LK2 M2 model2 ->
    forall (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (model1 : Model) (LK1 : list fframe) (Aw1 : list (Z * Z)) (X1 : st)
           (s1 : PM.pst) (sm1 : PM.strm) (en1 : PEC.enc) (k1 : PESK.sink) (e1 : bool) (cr1 : credit),
      alinv R M model LBX FF LK Aw cr sp fb cat p s str sm en k e F R1 M1 model1 LK1 Aw1 X1 s1 sm1 en1 k1 e1 cr1 -> halted X1 = false -> G (top_mode X1) ->
      (forall (fx2 : FPState) (R2 : bvmap 5 word) (M2' : word -> option byte) (model2' : Model) (LK2' : list fframe) (Aw2 : list (Z * Z)) (X2 : st)
              (s2 : PM.pst) (sm2 : PM.strm) (en2 : PEC.enc) (k2 : PESK.sink) (e2 : bool) (cr2 : credit),
          alinv R M model LBX FF LK Aw cr sp fb cat p s str sm en k e F R2 M2' model2' LK2' Aw2 X2 s2 sm2 en2 k2 e2 cr2 -> mu p X2 < mu p X1 ->
          srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx2 R2 LPHEAD M2' model2') K) ->
      srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx1 R1 LPHEAD M1 model1) K.

Lemma alinv_ginv R M model LBX FF LK Aw cr sp fb cat p s str sm en k e F R1 M1 model1 LK1 Aw1 X1 s1 sm1 en1 k1 e1 cr1 :
  bytes_ok p -> alinv R M model LBX FF LK Aw cr sp fb cat p s str sm en k e F R1 M1 model1 LK1 Aw1 X1 s1 sm1 en1 k1 e1 cr1 -> ginv p X1 /\ s_bad X1 = false.
Proof.
  intros BP LI. destruct LI as (_ & (i & ->) & _ & _).
  split; [apply run_ginv; [exact BP| apply ginv_init] | apply run_not_bad; exact BP].
Qed.
Lemma step_run p i : UbjRef.step p (run i p UbjRef.init) = run (Datatypes.S i) p UbjRef.init.
Proof. rewrite <- (Nat.add_1_r i), run_add. reflexivity. Qed.
End WithHeap.
End PEACLPD.
