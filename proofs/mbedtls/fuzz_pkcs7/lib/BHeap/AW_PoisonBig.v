(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux CellsX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_stringA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Unwind AW_MmapFixed AW_MmapDie AW_MmapFixedNR AW_Poison.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Open Scope Z_scope.
Unset Lia Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_AW_PoisonBig () : Init.string Init.list := ["Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.Lib.Step.ro_cells"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "ARUN_1.A_GOT_CANARY"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "stdpp.bitvector.definitions.Z_to_bv"; "ARUN_1.A_CANARY"; "Corelib.Init.Datatypes.nil"; "ARUN_1.A_LIBC_PAGESZ"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_GOT_CFLAGS"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_CFLAGS"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_MMAP_LIMIT"; "ARUN_1.A_CF_DONTDUMP"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_GOT_SEALED2"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind.A_GOT_PAGESZ"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind.A_PAGESZ_CELL"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_GOT_DYING"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_DYING"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixedNR.A_MADV_FLAG"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "ARUN_1.rsmr_statics"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.disjoint_from"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Corelib.Lists.ListDef.firstn"; "Stdlib.ZArith.BinInt.Z.sub"; "Corelib.Lists.ListDef.skipn"; "Corelib.Init.Datatypes.app"].

Section ARUN_1. Context {hAR : arun}.
Definition A_GETGRAN : Z := 0x7c918.         (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_RSMR : Z := 0x082f68.           (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_RSMR_B : Z := 0x082fd4.         (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_GOT_CANARY : Z := 0x0f6ae0.     (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_CANARY : Z := 0x65cad0.         (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_LIBC_PAGESZ : Z := 0x65cd50.    (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_CF_DONTDUMP : Z := 0x19b603.    (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_DONTDUMP : Z := 0x0846fc.       (* [comment removed for export] *) (* [comment removed for export] *)

Definition rsmr_statics (m : mem) (can : word) (dd madv : byte) : Prop := ltac2:(CDefT.buildp (gd_tbl_AW_PoisonBig ()) "(0.(1.$2.O4.$3.(4.$5.(6.(7.&40.$8.))(9.$5.)))(0.(1.$2.O4.$8.(4.$5.(6.O3.)(9.$5.)))(0.(1.$2.O4.$:.(4.$5.(6.(7.&40.+1000.))(9.$5.)))(0.(1.$2.O4.$;.(4.$5.(6.(7.&40.$<.))(9.$5.)))(0.(1.$2.O4.$=.(4.$5.(6.(7.&40.=))(9.$5.)))(0.(1.$2.O4.$>.(4.$5.(?.O2.)(9.$5.)))(0.(1.$2.O4.$10.(4.$5.(6.(7.&40.+1.))(9.$5.)))(0.(1.$2.O4.$11.(4.$5.(6.(7.&40.$12.))(9.$5.)))(0.(1.$2.O4.$12.(4.$5.(6.(7.&40.+1000.))(9.$5.)))(0.(1.$2.O4.$13.(4.$5.(6.(7.&40.$14.))(9.$5.)))(0.(1.$2.O4.$14.(4.$5.(15.(7.&40.=))(9.$5.)))(1.$2.O4.$16.(4.$5.(?.O1.)(9.$5.))))))))))))))")
(* [comment removed for export] *).

#[using="Type"] Lemma rsmr_statics_transport : ltac2:(CDefT.buildp (gd_tbl_AW_PoisonBig ()) "PW,(17.$18.)Pm,P,(19.&40.)(1:.(19.&8.))Pm',P,(19.&40.)(1:.(19.&8.))Pcan,(19.&40.)Pdd,(19.&8.)Pmadv,(19.&8.)P,(1;.R5.R3.R2.R1.)P,(1<.R7.R6.R5.)P,PA,$1=.Pn,$1=.P,(0.(1>.+10000.R2.)(1>.(1?.R2.R1.)+65?000.))(20.R;.R3.R2.)(1;.R7.R6.R5.R4.)")
(* [comment removed for export] *).
Proof.
  intros W m m' can dd madv S MU DJ. unfold rsmr_statics in *.
  unfold A_GOT_CANARY, A_CANARY, A_LIBC_PAGESZ, A_GOT_CFLAGS, A_CFLAGS, A_MMAP_LIMIT, A_CF_DONTDUMP, A_GOT_SEALED2, A_GOT_PAGESZ, A_PAGESZ_CELL,
    A_GOT_DYING, A_DYING, A_MADV_FLAG in *.
  decompose [and] S. repeat split; (eapply ro_cells_transport; [eassumption| exact MU| apply DJ; cbn; lia]).
Qed.



(* [comment removed for export] *)
#[using="Type"] Lemma cb_split : ltac2:(CDefT.buildp (gd_tbl_AW_PoisonBig ()) "Pm,P,(19.&40.)(1:.(19.&8.))PA,$1=.Pk,$1=.Pa,$1=.Pbs,(17.(19.&8.))P,(21.$2.R5.R4.(4.$5.(22.(23.R3.)R1.)(9.$5.)))P,(0.(1>.=R3.)(1>.R3.R4.))(0.(21.$2.R7.R6.(4.$5.(22.(23.R4.)(24.(19.&8.)(23.R4.)R3.))(9.$5.)))(21.$2.R7.(1?.R6.R4.)(4.$5.(22.(23.(25.R5.R4.))(26.(19.&8.)(23.R4.)R3.))(9.$5.))))")
(* [comment removed for export] *).
Proof.
  intros m A k a bs H Ha. pose proof H as [[WF _] _]. cbn in WF. destruct WF as [LEN _].
  assert (R : rw_cells asegs m A ([CB (Z.to_nat a) (firstn (Z.to_nat a) bs)] ++ [CB (Z.to_nat (k - a)) (skipn (Z.to_nat a) bs)])).
  { eapply rw_cells_reshape; [exact H| |].
    - cbn. rewrite firstn_length, skipn_length. repeat split; lia.
    - cbn. rewrite !app_nil_r. apply firstn_skipn. }
  apply rw_cells_app in R. destruct R as [R1 R2]. cbn [cells_size csize Nat.add] in R2. rewrite Nat.add_0_r, Z2Nat.id in R2 by lia.
  split; [exact R1| exact R2].
Qed.

#[using="Type"] Lemma cb_join : ltac2:(CDefT.buildp (gd_tbl_AW_PoisonBig ()) "Pm,P,(19.&40.)(1:.(19.&8.))PA,$1=.Pa,$1=.Pb,$1=.Pbs1,(17.(19.&8.))Pbs2,(17.(19.&8.))P,(21.$2.R6.R5.(4.$5.(22.(23.R4.)R2.)(9.$5.)))P,(21.$2.R7.(1?.R6.R5.)(4.$5.(22.(23.R4.)R2.)(9.$5.)))P,(1>.=R6.)P,(1>.=R6.)(21.$2.R:.R9.(4.$5.(22.(23.(1?.R8.R7.))(27.(19.&8.)R6.R5.))(9.$5.)))")
(* [comment removed for export] *).
Proof.
  intros m A a b bs1 bs2 H1 H2 Ha Hb. pose proof H1 as [[W1 _] _]. pose proof H2 as [[W2 _] _]. cbn in W1, W2.
  assert (R : rw_cells asegs m A ([CB (Z.to_nat a) bs1] ++ [CB (Z.to_nat b) bs2])).
  { apply (proj2 (rw_cells_app asegs m A _ _)). split; [exact H1|]. cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by lia. exact H2. }
  eapply rw_cells_reshape; [exact R| |].
  - cbn. rewrite app_length. split; [lia| exact I].
  - cbn. rewrite !app_nil_r. reflexivity.
Qed.


#[using="Type"] Lemma repeat_app' : forall (A : Type) (x : A) a b, repeat x (a + b) = repeat x a ++ repeat x b.
Proof. intros A x a b. induction a; cbn; [reflexivity|]. rewrite IHa. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma land_negpage : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709547520 = x / 4096 * 4096.
Proof.
  intros x Hx.
  assert (E : 18446744073709547520 = Z.shiftl (Z.ones 52) 12) by reflexivity. rewrite E.
  apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec, Z.shiftl_spec, Z.testbit_ones by lia.
  destruct (Z.ltb_spec i 12).
  - replace (0 <=? i - 12) with false by (symmetry; apply Z.leb_gt; lia). cbn [andb].
    rewrite Bool.andb_false_r. replace (x / 4096 * 4096) with (Z.shiftl (x / 4096) 12) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
    rewrite Z.shiftl_spec_low by lia. reflexivity.
  - replace (0 <=? i - 12) with true by (symmetry; apply Z.leb_le; lia).
    destruct (Z.ltb_spec (i - 12) 52); cbn [andb].
    + rewrite Bool.andb_true_r. replace (x / 4096 * 4096) with (Z.shiftl (Z.shiftr x 12) 12) by (rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia; reflexivity).
      rewrite Z.shiftl_spec_high, Z.shiftr_spec by lia. f_equal. lia.
    + rewrite Bool.andb_false_r. symmetry.
      assert (B : 0 <= x / 4096 * 4096 < 2^64) by (pose proof (Z.div_mod x 4096 ltac:(lia)); pose proof (Z.mod_pos_bound x 4096 ltac:(lia)); lia).
      destruct (Z.eq_dec (x / 4096 * 4096) 0) as [->|NZ]; [apply Z.bits_0|].
      apply Z.bits_above_log2; [lia|].
      assert (Z.log2 (x / 4096 * 4096) < 64) by (apply Z.log2_lt_pow2; lia). lia.
Qed.

(* [comment removed for export] *)

End ARUN_1.
