(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec StoreOk AsanAcct HeapIface HeapIfaceA HeapIfaceAEx L5Defs L5Core L5KnA L5LazyA L5DefsA L5CoreAS9.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout PmLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PmModel PmStatics PmStaticsA PmSpecs PmSpecsA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayout.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PeCSink PeCStatics PeCModel PeCSinkA PeCStaticsA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9.Spec Require Import UbjRefFactsS9.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require LibIfaceAB.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PECA.
Section WithImage.
Context {SCFG_P : ScfgP}.
Variable segs : list Segment.
Variable A : pm_addrs.
Variable AA : pm_asan_addrs.
Variable E : pe_addrs.
Variable L : asan_layout.
Variable ar : asan_run.

Abbreviation accA := PMSPA.accA.
Abbreviation annA := PMSPA.annA.
Abbreviation HV := (PMSPA.HV L ar).
Abbreviation scA := (PMSPA.scA L).
Abbreviation parser_at := (PM.parser_at segs A accA annA).
Abbreviation iss_at := (PM.iss_at segs A accA).
Abbreviation sink_atA := (PESKA.sink_atA segs L ar).

Definition frame_ok5 (FF : list fframe) (fb : Z) : Prop := (exists rs, In (fb, 5, rs) FF) /\ fb mod 2048 = 0.

Definition enc_atA (M : word -> option byte) (ov fb : Z) (en : PEC.enc) : Prop :=
  L5.u64_at segs M ov (pe_vt E) /\ L5.u64_at segs M (ov + 8) (PESK.o_sink E fb) /\ L5.u32_at segs M (ov + 16) UbjRef.MAX_DEPTH
  /\ L5.u64_at segs M (ov + 24) (PEC.en_b en)
  /\ L5.u64_at segs M (ov + 32) (PEC.en_b en + PEC.ESZ * Z.of_nat (length (PEC.en_stk en)))
  /\ L5.u64_at segs M (ov + 40) (PEC.en_b en + PEC.ESZ * PEC.ecap (PEC.en_k en))
  /\ L5.u32_at segs M (ov + 48) (PEC.en_depth en)
  /\ L5.defined M ov 56 /\ accA M ov 56
  /\ 0 <= PEC.en_k en <= 12 /\ Z.of_nat (length (PEC.en_stk en)) <= PEC.ecap (PEC.en_k en) /\ 0 <= PEC.en_depth en <= UbjRef.MAX_DEPTH + 1
  /\ (PEC.en_k en = 0 -> PEC.en_b en = 0)
  /\ (0 < PEC.en_k en ->
        PEC.en_b en mod 8 = 0 /\ L5.defined M (PEC.en_b en) (PEC.ESZ * PEC.ecap (PEC.en_k en)) /\ ablock_range L ar (PEC.en_b en) (PEC.ESZ * PEC.ecap (PEC.en_k en))
        /\ accA M (PEC.en_b en) (PEC.ESZ * Z.of_nat (length (PEC.en_stk en)))
        /\ annA M (PEC.en_b en) (PEC.ESZ * Z.of_nat (length (PEC.en_stk en))) (PEC.ESZ * PEC.ecap (PEC.en_k en)))
  /\ (forall i, (i < length (PEC.en_stk en))%nat -> PEC.eitem_at segs M (PEC.en_b en + PEC.ESZ * Z.of_nat i) (nth i (PEC.en_stk en) (EI 0 0 0))).

Definition ec_stateA (M : word -> option byte) (fb : Z) (e : bool) (cat : Z) : Prop :=
  if e then exists v, 1 <= v <= 64 /\ PMSPA.ec_at segs M (PMSPA.o_ec A fb) v (pa_errcat_obj A)
  else PMSPA.ec_at segs M (PMSPA.o_ec A fb) 0 cat.

Definition RDR_BYTES : Z := 392.

Definition crun_preA (P : PESKA.sink_policyA) (M : word -> option byte) (fb : Z) (p : list Z) (X : UbjRef.st)
           (s : PM.pst) (str : PM.vstr) (sm : PM.strm) (en : PEC.enc) (k : PESK.sink) (e : bool) (cat : Z) : Prop :=
  parser_at M (PMSPA.o_p A fb) (PMSPA.o_is A fb) s /\ iss_at M (PMSPA.o_is A fb) str sm
  /\ enc_atA M (PMSPA.o_v A fb) fb en /\ L5.u64_at segs M (PMSPA.o_p A fb + 384) (PMSPA.o_v A fb)
  /\ sink_atA P M (PESK.o_sink E fb) k
  /\ PMSTA.base_okA segs A M /\ PESTA.err_okA segs A AA E M e /\ PM.tb_ok (PM.p_tb s) (PM.p_tg s)
  /\ PEC.content_ok segs A M fb p (PM.p_src s) str sm
  /\ PEC.clink p X s sm en k
  /\ ec_stateA M fb (s_ec X) cat
  /\ (s_ec X = true -> e = true)
  /\ accA M (PMSPA.o_p A fb) RDR_BYTES.

Definition pot_allA (P : PESKA.sink_policyA) (s : PM.pst) (en : PEC.enc) (k : PESK.sink) : credit :=
  PEC.credit_add (scA (PM.pot_parser HV s)) (PEC.credit_add (scA (PEC.pot_estack HV (PEC.en_k en))) (PESKA.spa_pot P (PESK.sk_c k))).
Definition pot_encA (P : PESKA.sink_policyA) (en : PEC.enc) (k : PESK.sink) : credit :=
  PEC.credit_add (scA (PEC.pot_estack HV (PEC.en_k en))) (PESKA.spa_pot P (PESK.sk_c k)).

Lemma crun_preA_clink P M fb p X s str sm en k e cat : crun_preA P M fb p X s str sm en k e cat -> PEC.clink p X s sm en k.
Proof. intros H. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H)))))))))). Qed.
Lemma crun_preA_content P M fb p X s str sm en k e cat : crun_preA P M fb p X s str sm en k e cat -> PEC.content_ok segs A M fb p (PM.p_src s) str sm.
Proof. intros H. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H))))))))). Qed.
Lemma crun_preA_rdr P M fb p X s str sm en k e cat : crun_preA P M fb p X s str sm en k e cat -> accA M (PMSPA.o_p A fb) RDR_BYTES.
Proof. intros H. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H)))))))))))). Qed.
End WithImage.
End PECA.
