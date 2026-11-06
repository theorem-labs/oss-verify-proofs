(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType State.
From LinuxProcessSemantics.Riscv Require Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From Stdlib Require Bool Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics Run.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Inv PrimCreditLaws.
From LinuxProcessSemantics.Riscv Require Prelude Sem.

(* [comment removed for export] *)
Module CertFreeNull.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nat"; "nil"; "pair"; "prod"; "app"; "None"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "sprop"; "SLit"; "SPUle"; "FcsrFrm0"; "mkSS"; "SPAlign"; "SPUlt"; "SVar"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "carved"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "vT"; "TP_A"; "vCTX"; "O_T0"; "O_T40"; "O_cfa"; "O_ctx8"; "O_ctx98"; "O_mcs"; "O_pga"; "O_pgb"; "O_rt1a"; "O_rt1b"; "O_self_tsd"; "O_tsd0"; "O_tsda"; "O_tsdb"; "O_tsdc"; "vBOT"; "vTOP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "pre_fregs"; "setregs"; "cut_regs"; "pre_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull"; "E_fn"; "F_geom_fn"; "NW2"; "P0_fn"; "RT_fn"; "O_T3168"; "O_ia"; "O_iamap"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "AE_A"; "A_globals"; "Wcan"; "free_depth"; "mkA"; "pre_facts"; "stack_win"; "unwind_factsS"; "unwind_objs"; "V_FREE_A1"; "ae_free"; "ae_ret_free"; "@Stdlib.ZArith.BinInt.Z"; "sub"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA CFGA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Open Scope Z_scope.

Definition NW2 : positive := 220%positive.

Definition O_ia (inited : Z) : sobj := ltac2:(tb__ "0|5|
S18SbZ0A1M0Z17db48M1Z17db4aS0S4S4S12S1A2M2S9A2M3S3G2S9S3S12S1G1U1M4A4SbVinited;A1A4S0G3S3G2S9S3S12S1Z17db49G4A4G0A4S2G3A1A3A3A4").
Definition O_iamap : sobj := ltac2:(tb__ "0|4|
S18SbZ0A1M0Zef2c8M1Zef2d0S0S4S4S12S1A2M2S9A2M3S3G2S9S3S12S1G1U8A4G0A4S2G3A1A3A4").

Definition O_T3168 : sobj := ltac2:(tb__ "0|3|
S18S1bZc60M0Zc61S0S4S4S12S1A2M1S9A2M2S3G1S9S3S12S1G0U1A4SbZ0A1A4S2G2A1A3A4").

Definition RT_fn : list sobj := ltac2:(tb__ "0|0|
S0S8S39Z1A1S0S8S3aS0S8S26S0S8S27S0S8S2aS0S8S2bS0S8S2cS0S8S28S0S8S29S0S8S21S0S8S22S0S8S1eS0S8S1fS0S8S38S0S8S20S0S8S24S0S8S25S0S8S23S2S8A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Definition F_geom_fn : list sprop := ltac2:(tb__ "0|3|
S0SaS10S2dS2eA2S0SaScSbZ1000M0A1M1S1bA2S0SaScS1bSbS47Z7fffff800000G0A2A1M2A2S0SaSfP97ZcA2S0SaScG1S1dA2S0SaScS1dG2A2S2SaA1A3A3A3A3A3A3").

Section FN.
Variable W : list ulink.
Variable st : ustop.

Definition P0_fn : axst := ltac2:(tb__ "0|1|
S3fSeS45S3bA1S30S32S0S4S1S9A2M0S3S1S9U4SbS1cA1A4S0G0S3S1S9UaSbZ0A1A4S0G0S3S1S9UbS11S44A1A4S2G0A1A3A3A3A2S2fSdS6S9A1S5S8S0S8S41S5S8S43VW;A1S3cA3A3S37A3S5SaS5SaS42VW;Vst;A2S40S3eA1A3S34A3S35S7A9S2S4S9S9A2A1A2").

Definition E_fn : axst := ltac2:(tb__ "0|1|
S3fSeS46S3bA1S30S31S19A1S0S4S1S9A2M0S3S1S9U4SbS1cA1A4S2G0A1A3A2S2fSdS6S9A1S5S8S0S8S41S5S8S43VW;A1S3cA3A3S37A3S5SaS5SaS42VW;Vst;A2S40S3eA1A3S34A3S35S7A9S2S4S9S9A2A1A2").
End FN.

Definition fn_cert (n : nat) (st : ustop) : bool := ltac2:(tb__ "0|2|
S15S1aUbb8S2S12A1S19S0S17S36S3dVn;A1M0Vst;A2S2S17A1M1A3S0S17S33G0Vst;A2G1A3A6").
Definition fn_ecert (n : nat) (st : ustop) : bool := ltac2:(tb__ "0|4|
S16S1aUbb8S2S12A1S19S0S13S14S36S3dVn;A1M0Vst;A2Z1SbZ0M1A1M2A3S2S13A1M3A3S0S13S14S33G0Vst;A2G1G2A3G3A3A6").

Lemma fn_cert_0 : fn_cert 0 UStopLe = true. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma fn_cert_1 : fn_cert 1 UStopLe = true. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
End CertFreeNull.

(* [comment removed for export] *)
Module SecRoom.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "length"; "list"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_sec"; "sec_chunk"; "budget_ok_alloc"; "large_live"; "sec_room"; "@Stdlib.ZArith.BinInt.Z"; "add"; "of_nat"; "lt"; "pow"; "le"; "@stdpp.bitvector.definitions"; "bv"; "@Corelib.Numbers.BinNums"; "Z"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Inv.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section WithSegs.
Variable segs : list Segment.

Lemma AInvA_sec_bound : ltac2:(tb__ "0|0|
S5S3S1S10Q40A1A1S2S4Vsegs;R4R3R2R1A5SfScS0S7S6R5A1A2A1SbS9R5A1Z1051A2A2F_;Fmd;Ftp;Frho;FA;").
Proof.
  intros A rho tp md (_ & _ & _ & HRest & _ & HI3 & _).
  destruct HRest as (_ & _ & _ & _ & HQ & _). pose proof (qlarge_bound _ _ HQ) as QB.
  destruct HI3 as (_ & _ & _ & _ & _ & _ & H7 & _). lia.
Qed.

Lemma AInvA_sec_ok : ltac2:(tb__ "0|0|
S5S3S1S10Q40A1A1S2S4Vsegs;R4R3R2R1A5SaR5A1SdSbScS0S7S6R6A1A2A1Z1A2SeZ2Z14A2A2F_;F_;Fmd;Ftp;Frho;FA;").
Proof. intros A rho tp md HA HR. pose proof (AInvA_sec_bound A rho tp md HA). unfold sec_room, SEC_SLACK in HR. lia. Qed.

Lemma sec_ok_of_budget : ltac2:(tb__ "0|0|
S5S3S1S10Q40A1A1S2S11S4Vsegs;R5R4R3R2A5S8R6R2A2SdSbScS0S7S6R7A1A2A1Z1A2SeZ2Z14A2A2F_;F_;Fn;Fmd;Ftp;Frho;FA;").
Proof. intros A rho tp md n HA HB. exact (AInvA_sec_ok A rho tp md HA (budget_ok_alloc_room A n HB)). Qed.
End WithSegs.
End SecRoom.

(* [comment removed for export] *)
Module PrimRoom.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Stdlib.ZArith.BinInt.Z"; "le"; "of_nat"; "mul"; "add"; "@Corelib.Init.Datatypes"; "length"; "list"; "prod"; "snd"; "bool"; "nil"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "qbatch"; "AA"; "class_state"; "aa_cls"; "aa_geom"; "ageom"; "cs_cache"; "cs_empty"; "cs_free_array"; "cs_mapped_user"; "small_live"; "@Corelib.Init.Logic"; "and"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "bview"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs"; "qall"; "qitems"; "q_ids"; "@Stdlib.Lists.List"; "In"; "filter"; "@Corelib.Lists.ListDef"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "kQuarantineBatchCount"; "kQuarantineBatchSize"; "kUserMapSize"; "kUserSpaceSize"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "batch_repr"; "isum"; "quarantine_repr"; "AInvA"; "live_ids"; "nthZ"; "qsize"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCredit"; "NBQ"; "MUCAP"; "QCAP"; "qmax"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "@stdpp.bitvector.definitions"; "bv"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells SegQ_defs PrimCredit PrimCreditLaws Inv.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma filter_length_imp : forall {T} (p q : T -> bool) (l : list T),
  (forall x, In x l -> p x = true -> q x = true) -> (length (List.filter p l) <= length (List.filter q l))%nat.
Proof.
  intros T p q. induction l as [|x l IH]; intros H; [cbn; lia|]. cbn [List.filter].
  specialize (IH (fun y Hy => H y (or_intror Hy))). pose proof (H x (or_introl eq_refl)) as Hx.
  destruct (p x) eqn:Ep; [rewrite (Hx eq_refl); cbn [length]; lia | destruct (q x); cbn [length]; lia].
Qed.
Lemma filter_length_le : forall {T} (p : T -> bool) (l : list T), (length (List.filter p l) <= length l)%nat.
Proof. intros T p. induction l as [|x l IH]; [cbn; lia|]. cbn [List.filter]. destruct (p x); cbn [length]; lia. Qed.

Lemma isum_filter_ge : ltac2:(tb__ "0|1|
S7S0S0A2M0S9F_;S0S6G0A1G0S1dG0R1R2A3S1Z0S8S0S0R2A3A2F_;Fit;G0S1dG0R1R3A3S18S9R6R2A1SbA3S1R6S8S0S0R3A3A2F_;F_;Fit;S1S3R4S2S5G0S1eG0R5R3A3A2A1A2S25R3A1A2F_;F_;Fl;Fw;Fp;").
Proof.
  intros p w. induction l as [|x l IH]; intros H0 Hw; [cbn; lia|].
  specialize (IH (fun it Hit => H0 it (or_intror Hit)) (fun it Hit => Hw it (or_intror Hit))).
  pose proof (H0 x (or_introl eq_refl)) as X0. pose proof (Hw x (or_introl eq_refl)) as Xw.
  cbn [List.filter]. unfold isum in *. cbn [fold_right]. destruct (p x) eqn:Ep.
  - specialize (Xw eq_refl). cbn [length]. rewrite Nat2Z.inj_succ. set (k := Z.of_nat _) in *. clearbody k. clear -IH Xw. nia.
  - clear -IH X0. lia.
Qed.
Lemma qitems_length : ltac2:(tb__ "0|0|
S19SdS6ScA1S1fScS24R3R2A2R1A3S1S2S5S7S0S0A2S1bR2A1A2A1S3S20S2S5ScR2A2A1A2A2F_;Fl;FA;Fm;").
Proof.
  intros m A. induction l as [|b l IH]; intros HF; [cbn; lia|]. inversion HF as [|? ? Hb HF']; subst. specialize (IH HF').
  destruct Hb as (_ & _ & _ & Hcnt & _). unfold qitems in *. cbn [flat_map]. rewrite length_app. cbn [length].
  rewrite Nat2Z.inj_add, Nat2Z.inj_succ. unfold kQuarantineBatchCount in *. lia.
Qed.
Lemma qsize_batches : ltac2:(tb__ "0|0|
S19SdS6ScA1S1fScS24R3R2A2R1A3S1S3S21S2S5ScR2A2A1A2S2aR2A1A2F_;Fl;FA;Fm;").
Proof.
  intros m A. induction l as [|b l IH]; intros HF; [cbn; lia|]. inversion HF as [|? ? Hb HF']; subst. specialize (IH HF').
  assert (HF1 : Forall (batch_repr m A) [b]) by (constructor; [exact Hb | constructor]).
  destruct (isum_qitems_le m A [b] HF1) as [I1 _].
  destruct Hb as (_ & _ & _ & _ & Hsz & _).
  assert (0 <= fold_right (fun it acc => snd it + acc) 0 (qb_items b)).
  { assert (G : forall l0, (forall it, In it l0 -> 1 <= snd it) -> 0 <= fold_right (fun (it : Z * Z) acc => snd it + acc) 0 l0).
    { induction l0 as [|x l0 IH0]; intros Hx; [cbn; lia|]. cbn [fold_right]. pose proof (Hx x (or_introl eq_refl)). specialize (IH0 (fun it Hit => Hx it (or_intror Hit))). lia. }
    apply G. intros it Hit. apply I1. unfold qitems. cbn [flat_map]. rewrite app_nil_r. exact Hit. }
  unfold qsize in *. cbn [fold_right length]. rewrite Nat2Z.inj_succ. unfold kQuarantineBatchSize in *. lia.
Qed.

Section WithSegs.
Variable segs : list Segment.

Lemma quarantine_counts : ltac2:(tb__ "0|3|
S19SdS26R2R1A2S17S1S2S5ScS1aR2A1M0A2A1S2bA2S17S1S2S5S7S0S0A2M1S1bG0A1M2A2A1S3S20S2bA2A2S17S1S25G2A1S2dA2G1S1dG1R1S1bS1aR3A1A1A3S1Z1S8S0S0R2A3A2F_;Fit;A2A2A2F_;FA;Fm;").
Proof.
  intros m A (HF & _ & _ & _ & _ & _ & _ & HT & HG & _).
  assert (HFt : Forall (batch_repr m A) (aa_q_thread A)) by (apply Forall_app in HF; tauto).
  assert (HFg : Forall (batch_repr m A) (aa_q_global A)) by (apply Forall_app in HF; tauto).
  pose proof (qsize_batches m A _ HFt) as Bt. pose proof (qsize_batches m A _ HFg) as Bg.
  assert (NB : Z.of_nat (length (qall A)) <= NBQ).
  { unfold qall. rewrite length_app, Nat2Z.inj_add. unfold NBQ, QCAP, kQuarantineBatchSize, kQuarantineMax, kQuarantineCacheMax in *. change ((2 ^ 28 + 2 ^ 20) / 8192) with 32896. lia. }
  split; [exact NB|]. destruct (isum_qitems_le m A _ HF) as [I1 I2]. fold (qall A) in I1, I2.
  split.
  { pose proof (qitems_length m A _ HF) as QL. fold (qall A) in QL. unfold kQuarantineBatchCount in *. lia. }
  split; [|exact I1].
  assert (QS : forall l1 l2, qsize (l1 ++ l2) = qsize l1 + qsize l2).
  { induction l1 as [|x t IHt]; intros l2; [reflexivity|]. cbn [app]. unfold qsize in *. cbn [fold_right]. rewrite IHt. lia. }
  unfold qall in I2. rewrite QS in I2. unfold QCAP. set (i := isum _) in *. set (qt := qsize (aa_q_thread A)) in *. set (qg := qsize (aa_q_global A)) in *.
  clearbody i qt qg. clear -I2 HT HG. lia.
Qed.

Lemma q_ids_bound : ltac2:(tb__ "0|0|
S19SdS0S26R3R2A2S17S1Z1R2A2S1R2Z1eA2A2S1S2S5S0S1cS10R4A1S1aR4A1R3A3A2A1S2eR3A1A2F_;F_;Fc;FA;Fm;").
Proof.
  intros m A c HQ Hc. destruct (quarantine_counts m A HQ) as (NB & NI & IS & I1).
  unfold q_ids, qmax. rewrite length_app, !length_map, Nat2Z.inj_add.
  set (p := fun it : Z * Z => is_primary (snd it) && (it_cls it =? c)).
  assert (ITEMS : Z.of_nat (length (List.filter p (qitems (qall A)))) <= (if nmin c =? 0 then 0 else Z.min (kQuarantineBatchCount * NBQ) (QCAP / nmin c))).
  { assert (PN : forall it, In it (qitems (qall A)) -> p it = true -> 1 <= nmin c <= snd it).
    { intros it Hit Hp. unfold p in Hp. apply andb_prop in Hp as [Hp1 Hp2]. apply Z.eqb_eq in Hp2. unfold it_cls in Hp2.
      pose proof (I1 it Hit) as H1.
      assert (H2 : snd it <= 64512).
      { destruct (Z_le_dec (snd it) 64512) as [L|G]; [exact L|]. rewrite (not_primary_large (snd it)) in Hp1 by lia. discriminate Hp1. }
      pose proof (nmin_ok (snd it) (conj H1 H2)) as NM. rewrite Hp2 in NM. exact NM. }
    destruct (Z.eqb_spec (nmin c) 0) as [E0|NE].
    -
      destruct (List.filter p (qitems (qall A))) as [|it l] eqn:EF; [cbn; lia|]. exfalso.
      assert (Hin : In it (List.filter p (qitems (qall A)))) by (rewrite EF; left; reflexivity). apply filter_In in Hin as [Hi Hp].
      pose proof (PN it Hi Hp). lia.
    - apply Z.min_glb.
      + pose proof (filter_length_le p (qitems (qall A))) as FL. apply Nat2Z.inj_le in FL. lia.
      + assert (NP : 1 <= nmin c).
        { destruct (List.filter p (qitems (qall A))) as [|it l] eqn:EF.
          -   unfold nmin in *. clear -NE Hc.
            assert (C : forall k, In k nmin_tab -> 0 <= k) by (intros k Hk; unfold nmin_tab in Hk; repeat (destruct Hk as [<-|Hk]; [lia|]); destruct Hk).
            assert (0 <= nth (Z.to_nat (c - 1)) nmin_tab 0) by (apply C; apply nth_In; unfold nmin_tab; cbn [length]; lia). lia.
          - assert (Hin : In it (List.filter p (qitems (qall A)))) by (rewrite EF; left; reflexivity). apply filter_In in Hin as [Hi Hp]. exact (proj1 (PN it Hi Hp)). }
        apply Z.div_le_lower_bound; [lia|].
        pose proof (isum_filter_ge p (nmin c) (qitems (qall A)) (fun it Hit => ltac:(pose proof (I1 it Hit); lia)) (fun it Hit Hp => proj2 (PN it Hit Hp))) as W. lia. }
  destruct (c =? 24); [rewrite length_map | cbn [length]]; fold p; lia.
Qed.

Lemma live_ids_bound : ltac2:(tb__ "0|0|
S11SdS0S1S2S5S0S28R3R2R1A3A2A1S16R2A1A2Fc;FA;FG;").
Proof.
  intros G A c. unfold live_ids, small_live. rewrite length_map.
  set (p := fun bn : Z * Z => is_primary (snd bn) && (ClassID (needed (snd bn)) =? c)).
  assert (E : forall l : list (Z * Z), filter p l = List.filter p l).
  { induction l as [|x l IH]; [reflexivity|]. cbn [List.filter]. destruct (p x) eqn:Ep.
    - rewrite list_basics.list.filter_cons_True by (rewrite Ep; exact I). rewrite IH. reflexivity.
    - rewrite list_basics.list.filter_cons_False by (rewrite Ep; intros []). exact IH. }
  fold p. rewrite E. apply Nat2Z.inj_le. apply filter_length_imp. intros [b n] _ Hp. unfold p in Hp. cbn [snd] in Hp |- *. apply andb_prop in Hp as [Hp _].
  unfold is_large. cbn [snd]. destruct (Z.leb_spec 64513 n) as [L|L]; [rewrite (not_primary_large n L) in Hp; discriminate Hp | reflexivity].
Qed.

Theorem populate_room : ltac2:(tb__ "0|1|
SdS30S6S31Q40A1A1S2fS0S27Vsegs;R5R4R3R2A5S17S1Z1R2A2S1R2Z1eA2A2S29SeSfR7A1R3S13A4SeS18S6S0A1S12R1A1SaS0A1A3S1S2S5S0S14R2A1A2A1Z7A2S17S1S4S15R3A1S22A2S2cR6A1M0A2S1G0S23A2A2F_;F_;Tcs;F_;F_;Fc;Fmd;Ftp;Frho;FA;").
Proof.
  intros A rho tp md c HA Hc cs Hcache Hfa.
  destruct HA as (_ & _ & _ & HRest & _ & HI3 & _).
  destruct HRest as (_ & _ & HPR & _ & HQ & _). destruct HPR as (_ & _ & _ & PC). pose proof (PC c Hc) as P4. fold cs in P4.
  unfold class_repr in P4.
  destruct P4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & N2 & _ & N4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TI & CV & _ & _).
  destruct HI3 as (_ & _ & _ & _ & _ & _ & _ & SL & _).
  pose proof (q_ids_bound _ A c HQ Hc) as QB. pose proof (live_ids_bound (aa_geom A) A c) as LB.
  destruct (cap_facts c Hc) as (HS & _ & MCU & _).
  split; [|exact MCU].
  rewrite Hcache in CV. cbn [length] in CV. unfold slots in CV.
  assert (Eau : cs_allocated_user cs = Size c * (cs_allocated_user cs / Size c)) by (apply Z.div_exact; [clear -HS; lia | exact N4]).
  rewrite !Nat2Z.inj_add in CV. cbn [Z.of_nat] in CV.
  unfold MUCAP. set (S := Size c) in *. set (sl := cs_allocated_user cs / S) in *. set (mu := cs_mapped_user cs) in *. set (au := cs_allocated_user cs) in *.
  set (nf := Z.of_nat (length (cs_free_array cs))) in *. set (nl := Z.of_nat (length (live_ids (aa_geom A) A c))) in *. set (nq := Z.of_nat (length (q_ids (aa_geom A) (qall A) c))) in *.
  set (q := qmax c) in *. set (sv := small_live A) in *. unfold PRIM_LIVE_MAX in *. unfold kUserMapSize.
  clearbody S sl mu au nf nl nq q sv. clear -HS TI CV Eau Hfa QB LB SL. nia.
Qed.
End WithSegs.
End PrimRoom.

(* [comment removed for export] *)
Module SegQlib.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@Corelib.Init.Datatypes"; "list"; "bool"; "true"; "prod"; "false"; "andb"; "option"; "pair"; "nil"; "Some"; "fst"; "snd"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sv"; "sprop"; "agree_below"; "ss_next"; "holds"; "ss_facts"; "sobj"; "sprop_below"; "sprop_eqb"; "ss_pc"; "SLit"; "SPBranch"; "SVar"; "rl"; "rm"; "rw"; "sv_below"; "swf"; "SPNot"; "ss_lenient"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "stableA"; "LQA"; "ok_frameA"; "smatchA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "leafA"; "ax_S"; "la_state"; "ax_setS"; "axwf"; "entailsA"; "sym_runA"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "NPRE"; "leaf"; "runA"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Stdlib.Lists.List"; "In"; "forallb"; "existsb"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "diffs_ok"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib"; "entsI"; "sdiff"; "one_at"; "two_at"; "JQ"; "pairs_eqb"; "diffs_below"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "call_checkA"; "entails_frA"; "import_postA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_sub"; "rho_absorb"; "wsub"; "wsub_id_below"; "@Stdlib.ZArith.BinInt.Z"; "eqb"; "le"; "lt"; "pow"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_GEU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "call_link"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@Stdlib.PArith.BinPos.Pos"; "eqb"; "le"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Open Scope Z_scope.

Lemma Forall_holds_agree : ltac2:(tb__ "0|1|
S3eS11S11S1S13A1S14R4R3R2A3SdS2S40S13S19R5A1R2A3S3A3S42S13S16R5A1M0R3A3S42S13G0R4A3F_;F_;F_;FF;Frho';Frho;Fn;").
Proof.
  intros n rho rho' F Hag Hb HF. apply Forall_forall. intros p Hp.
  apply (proj1 (holds_agree n rho rho' p Hag (proj1 (forallb_forall _ _) Hb p Hp))). exact (proj1 (Forall_forall _ _) HF p Hp).
Qed.

Definition diffs_below (n : positive) (d : list (sv * sv)) : bool := ltac2:(tb__ "0|1|
S40S4S12S12A2M0G0S6S22Vn;SbS12S12R1A3A2S22Vn;ScS12S12R1A3A2A2Lp;Vd;A3").
Lemma diffs_ok_agree : ltac2:(tb__ "0|0|
S3eS11S11S1S4S12S12A2A1SdS2S4eR4R1A2S3A3S14R5R4R3A3S46R5R3A2S46R5R4A2F_;F_;F_;Fd;Frho';Frho;Fn;").
Proof.
  intros n rho rho' d Hb Hag Hd. unfold diffs_ok in *. apply Forall_forall. intros p Hp.
  pose proof (proj1 (forallb_forall _ _) Hb p Hp) as B. cbn beta in B. apply andb_prop in B as [B1 B2].
  rewrite <- (eval_agree n rho rho' _ Hag B1), <- (eval_agree n rho rho' _ Hag B2). exact (proj1 (Forall_forall _ _) Hd p Hp).
Qed.

Definition one_at (l : list leafA) (pc : Z) : bool := ltac2:(tb__ "0|1|
S1S2dA1M0S2Ll;Vl;S5S2dG0G0S2Ll0;R1S5cS1bS2eS2fR2A1A1A1Vpc;A2S2dG0S5Ll2;Ll1;X1x2Ll0;LL;X1x2").
Definition two_at (l : list leafA) (pc : Z) : bool := ltac2:(tb__ "0|1|
S1S2dA1M0S2Ll;Vl;S5S2dG0G0S2Ll0;R1S5S2dG0G0S2Ll1;R1S6S5cS1bS2eS2fR4A1A1A1Vpc;A2S5cS1bS2eS2fR2A1A1A1Vpc;A2A2S2dG0S5Ll3;Ll2;X1x2Ll1;LL2;X1x2Ll0;LL1;X1x2").

Lemma one_at_In : ltac2:(tb__ "0|1|
S1S2dA1M0S3dS2dSdS2S4aR3R2A2S3A3S3fS2dR2R4A3SeSdS2cS2fR3A1S3bU0R5A2A3SfSdG0R5S9S2dA1A3A1A2F_;F_;FL0;Fpc;Fl;").
Proof.
  intros l pc L0 H Hin. unfold one_at in H. destruct l as [|L [|L' l']]; try discriminate H.
  destruct Hin as [<-|[]]. split; [reflexivity | discriminate].
Qed.
Lemma two_at_In : ltac2:(tb__ "0|2|
S1S2dA1M0S3dS2dSdS2S4bR3R2A2S3A3S3fS2dR2R4A3SeS10SdS2cS2fR3A1M1S3bU0R5A2A3SdS2cG1S3bU1R5A2A3A2SfSdG0R5S9S2dA1A3A1A2F_;F_;FL0;Fpc;Fl;").
Proof.
  intros l pc L0 H Hin. unfold two_at in H. destruct l as [|L1 [|L2 [|L3 l']]]; try discriminate H.
  destruct Hin as [<-|[<-|[]]]; (split; [|discriminate]); [left | right]; reflexivity.
Qed.
Lemma one_at_ne : ltac2:(tb__ "0|1|
S1S2dA1M0S3dSdS2S4aR2R1A2S3A3SfSdG0R3S9S2dA1A3A1F_;Fpc;Fl;"). Proof. intros [|L l'] pc H; [discriminate H | discriminate]. Qed.
Lemma two_at_ne : ltac2:(tb__ "0|1|
S1S2dA1M0S3dSdS2S4bR2R1A2S3A3SfSdG0R3S9S2dA1A3A1F_;Fpc;Fl;"). Proof. intros [|L l'] pc H; [discriminate H | discriminate]. Qed.

Section Runs.
Variables (fuel : nat) (cuts : list Z) (Pre : axst) (l : list leafA) (n : positive) (EA EB : axst).
Hypothesis HLEN : ltac2:(tb__ "0|0|
SdS2S25S2eVPre;A1A1S5A3").
Hypothesis HNX : ltac2:(tb__ "0|0|
SdS3eS15S2eVPre;A1A1Vn;A3").
Hypothesis RUNL : ltac2:(tb__ "0|0|
SdS1S2dA1S3cVfuel;Vcuts;VPre;A3Vl;A3").

Hypothesis HEA : leaf 0 l = EA.
Hypothesis HEB : leaf 1 l = EB.

Lemma run_some : ltac2:(tb__ "0|1|
SfSdS1S2dA1M0Vl;S9S2dA1A3A1SdS7G0A1S33S0Vfuel;Vcuts;VPre;S3A5SaG0Vl;A2A3F_;").
Proof using RUNL. intros Hne. pose proof RUNL as R. unfold runA in R. destruct (sym_runA segsA fuel cuts Pre true) as [l'|]; [congruence|]. exfalso. apply Hne. symmetry. exact R. Qed.

Theorem run_cont1 : ltac2:(tb__ "0|0|
S3dS27S38OF_;S11S1S34Q40A1A1S39SdS2S4aVl;R6A2S3A3S2aS0R5R6A3S28S0Vn;R7A3S11S14Vn;R7R1A3S37S0R9S26S0RaVEA;R2R7A5R6A4F_;FrhoE;S37S0R8S26S0R9VPre;R7R6A5R5A4F_;F_;F_;F_;FQ;Ftp;Frho;Fok;FJ;Fpc;").
Proof using HLEN HNX RUNL HEA.
  intros pc J ok rho tp Q H1 HOK HST HC. eapply triple_seq.
  - apply triple1_triple. exact (sym_run_soundA segsA fuel cuts Pre l ok J rho tp (run_some (one_at_ne l pc H1)) HOK HLEN ltac:(rewrite HNX; exact HST)).
  - rewrite HNX. apply triple_LQA_of_leaves. intros L0 rhoE Hin Hag. rewrite (proj1 (one_at_In l pc L0 H1 Hin)), HEA. exact (HC rhoE Hag).
Qed.
Theorem run_econt1 : ltac2:(tb__ "0|0|
S3dS27S11S1S34Q40A1A1S38OF_;SdS2S4aVl;R5A2S3A3S28S0Vn;R5A3S11S14Vn;R6R1A3S36S0S26S0R8VEA;R2R6A5R5A3F_;FrhoE;S36S0S26S0R7VPre;R6R5A5R4A3F_;F_;F_;FQ;Ftp;Frho;FJ;Fpc;").
Proof using HLEN HNX RUNL HEA.
  intros pc J rho tp Q H1 HST HC. eapply etriple_seq.
  - exact (sym_run_etripleA segsA fuel cuts Pre l J rho tp HLEN ltac:(rewrite HNX; exact HST) (run_some (one_at_ne l pc H1))).
  - rewrite HNX. apply etriple_LQA_of_leaves. intros L0 rhoE Hin Hag. rewrite (proj1 (one_at_In l pc L0 H1 Hin)), HEA. exact (HC rhoE Hag).
Qed.
Theorem run_cont2 : ltac2:(tb__ "0|0|
S3dS27S38OF_;S11S1S34Q40A1A1S39SdS2S4bVl;R6A2S3A3S2aS0R5R6A3S28S0Vn;R7A3S11S14Vn;R7R1A3S37S0R9S26S0RaVEA;R2R7A5R6A4F_;FrhoE;S11S14Vn;R8R1A3S37S0RaS26S0RbVEB;R2R8A5R7A4F_;FrhoE;S37S0R9S26S0RaVPre;R8R7A5R6A4F_;F_;F_;F_;F_;FQ;Ftp;Frho;Fok;FJ;Fpc;").
Proof using HLEN HNX RUNL HEA HEB.
  intros pc J ok rho tp Q H2 HOK HST HC0 HC1. eapply triple_seq.
  - apply triple1_triple. exact (sym_run_soundA segsA fuel cuts Pre l ok J rho tp (run_some (two_at_ne l pc H2)) HOK HLEN ltac:(rewrite HNX; exact HST)).
  - rewrite HNX. apply triple_LQA_of_leaves. intros L0 rhoE Hin Hag.
    destruct (proj1 (two_at_In l pc L0 H2 Hin)) as [-> | ->]; [rewrite HEA; exact (HC0 rhoE Hag) | rewrite HEB; exact (HC1 rhoE Hag)].
Qed.
Theorem run_econt2 : ltac2:(tb__ "0|0|
S3dS27S11S1S34Q40A1A1S38OF_;SdS2S4bVl;R5A2S3A3S28S0Vn;R5A3S11S14Vn;R6R1A3S36S0S26S0R8VEA;R2R6A5R5A3F_;FrhoE;S11S14Vn;R7R1A3S36S0S26S0R9VEB;R2R7A5R6A3F_;FrhoE;S36S0S26S0R8VPre;R7R6A5R5A3F_;F_;F_;F_;FQ;Ftp;Frho;FJ;Fpc;").
Proof using HLEN HNX RUNL HEA HEB.
  intros pc J rho tp Q H2 HST HC0 HC1. eapply etriple_seq.
  - exact (sym_run_etripleA segsA fuel cuts Pre l J rho tp HLEN ltac:(rewrite HNX; exact HST) (run_some (two_at_ne l pc H2))).
  - rewrite HNX. apply etriple_LQA_of_leaves. intros L0 rhoE Hin Hag.
    destruct (proj1 (two_at_In l pc L0 H2 Hin)) as [-> | ->]; [rewrite HEA; exact (HC0 rhoE Hag) | rewrite HEB; exact (HC1 rhoE Hag)].
Qed.
End Runs.

Fixpoint pairs_eqb (a b : list (sv * sv)) : bool :=
  match a, b with
  | [], [] => true
  | p :: a', q :: b' => sv_eqb (fst p) (fst q) && sv_eqb (snd p) (snd q) && pairs_eqb a' b'
  | _, _ => false
  end.
Lemma pairs_eqb_sound : ltac2:(tb__ "0|1|
S1S4S12S12A2A1M0G0SdS2S4dR2R1A2S3A3SdG0R3R2A3F_;Fb;Fa;").
Proof.
  induction a as [|p a IH]; intros [|q b] H; cbn in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply sv_eqb_sound in H1. apply sv_eqb_sound in H2.
  destruct p, q; cbn in *; subst. f_equal. apply IH. exact H3.
Qed.
Definition sdiff (E C : axst) (d : list (sv * sv)) : bool := ltac2:(tb__ "0|5|
S6S6S7S4S1S4S12S12A2A1M0S1S13A1M1A2M2A1S2Lx;S47S2eVE;A1M3S2eVC;A1M4A2G2G2S2Lp;R1G0G1G1S2Ll;R1S4dR2Vd;A2S13G1S5Ll0;Ls;X1x2Ll;Ld';X4x1Lp;S5X7x2S23G4A1A2S64S15G4A1S15G3A1A2A2").

Lemma restate_SPA : ltac2:(tb__ "0|0|
S27S2cS2cS1S4S12S12A2A1S11S1S34Q40A1A1S38SdS2S49R6R5R4A3S3A3S46R4R5A2S26S0R9R8R5R4R3A6S26S0RaS30R9S2eR8A1A2R6R5R4A6F_;F_;F_;Fw;Ftp;Frho;Fd;FC;FE;FJ;").
Proof.
  intros J E C d rho tp w H Hd HS. unfold sdiff in H. apply andb_prop in H as [H HN]. apply andb_prop in H as [H HW].
  destruct (state_diff (ax_S E) (ax_S C)) as [[d' [|f nf]]|] eqn:SD; try discriminate H.
  apply pairs_eqb_sound in H. subst d'. apply Pos.eqb_eq in HN.
  exact (SPA_restate segsA J rho E (ax_S C) tp w d [] HW SD HN Hd ltac:(constructor) HS).
Qed.

Lemma restate_cont : ltac2:(tb__ "0|0|
S27S38OF_;S2cS2cS1S4S12S12A2A1S11S1S34Q40A1A1S39SdS2S49R6R5R4A3S3A3S46R4R5A2SdS2cS30R8S2eR7A1A2R7A3S37S0RaS26S0RbR8R6R5A5R4A4S37S0RbS26S0RcRaR7R6A5R5A4F_;F_;F_;F_;FQ;Ftp;Frho;Fd;FC;FE;Fok;FJ;").
Proof.
  intros J ok E C d rho tp Q H Hd HEQ HT. eapply triple_conseq; [| intros w Hw; exact Hw | exact HT].
  intros w Hw. rewrite <- HEQ. exact (restate_SPA J E C d rho tp w H Hd Hw).
Qed.
Lemma restate_econt : ltac2:(tb__ "0|0|
S27S2cS2cS1S4S12S12A2A1S11S1S34Q40A1A1S38OF_;SdS2S49R6R5R4A3S3A3S46R4R5A2SdS2cS30R8S2eR7A1A2R7A3S36S0S26S0RaR8R6R5A5R4A3S36S0S26S0RbRaR7R6A5R5A3F_;F_;F_;F_;FQ;Ftp;Frho;Fd;FC;FE;FJ;").
Proof.
  intros J E C d rho tp Q H Hd HEQ HT. eapply etriple_conseq; [| intros w Hw; exact Hw | exact HT].
  intros w Hw. rewrite <- HEQ. exact (restate_SPA J E C d rho tp w H Hd Hw).
Qed.

Lemma restate_contF : ltac2:(tb__ "0|1|
S27S38OF_;S2cS2cS1S4S12S12A2A1S11S1S34Q40A1A1S39SdS2S49R6R5R4A3S3A3S42S13S16R4A1S17S2eR7A1M0A1A3S46R5R6A2F_;SdS2cS30R8G0A2R7A3S37S0RaS26S0RbR8R6R5A5R4A4S37S0RbS26S0RcRaR7R6A5R5A4F_;F_;F_;F_;FQ;Ftp;Frho;Fd;FC;FE;Fok;FJ;").
Proof.
  intros J ok E C d rho tp Q H Hd HEQ HT. eapply triple_conseq; [| intros w Hw; exact Hw | exact HT].
  intros w Hw. rewrite <- HEQ. exact (restate_SPA J E C d rho tp w H (Hd (SPA_facts_hold segsA J rho E tp w Hw)) Hw).
Qed.
Lemma restate_econtF : ltac2:(tb__ "0|1|
S27S2cS2cS1S4S12S12A2A1S11S1S34Q40A1A1S38OF_;SdS2S49R6R5R4A3S3A3S42S13S16R4A1S17S2eR7A1M0A1A3S46R5R6A2F_;SdS2cS30R8G0A2R7A3S36S0S26S0RaR8R6R5A5R4A3S36S0S26S0RbRaR7R6A5R5A3F_;F_;F_;F_;FQ;Ftp;Frho;Fd;FC;FE;FJ;").
Proof.
  intros J E C d rho tp Q H Hd HEQ HT. eapply etriple_conseq; [| intros w Hw; exact Hw | exact HT].
  intros w Hw. rewrite <- HEQ. exact (restate_SPA J E C d rho tp w H (Hd (SPA_facts_hold segsA J rho E tp w Hw)) Hw).
Qed.

Lemma fact_in_holds : ltac2:(tb__ "0|0|
S11S13S1S13A1SdS2S41S13S1aR2A1R1A3S3A3S42S13S16R4A1R2A3S16R5R4A2F_;F_;FF;Fp;Frho;").
Proof.
  intros rho p F Hb HF. apply existsb_exists in Hb as (q & Hin & Heq). apply sprop_eqb_sound in Heq. subst q. exact (proj1 (Forall_forall _ _) HF p Hin).
Qed.
Lemma fact_geu_lit : ltac2:(tb__ "0|0|
S11S3eS3dS1S13A1SeS5dZ0R2A2S5eR2S5fZ2Z40A2A2A2SdS2S41S13S1aS1dS60S1eR4A1S1cR3A1A3A1R2A3S3A3S42S13S16R6A1R3A3S5dR5S35Q40S21R7R6A2A2A2F_;F_;F_;FF;Fk;Fi;Frho;").
Proof.
  intros rho i k F Hk Hb HF. pose proof (fact_in_holds rho _ F Hb HF) as H. cbn [holds branch_taken eval] in H.
  unfold bv_ltu in H. rewrite Z_to_bv_unsigned, bv_wrap_small in H by (change (bv_modulus 64) with (2 ^ 64); lia).
  apply Bool.negb_true_iff in H. apply Z.ltb_ge in H. exact H.
Qed.
Lemma fact_ltu_lit : ltac2:(tb__ "0|0|
S11S3eS3dS1S13A1SeS5dZ0R2A2S5eR2S5fZ2Z40A2A2A2SdS2S41S13S1aS24S1dS60S1eR4A1S1cR3A1A3A1A1R2A3S3A3S42S13S16R6A1R3A3S5eS35Q40S21R7R6A2A2R5A2F_;F_;F_;FF;Fk;Fi;Frho;").
Proof.
  intros rho i k F Hk Hb HF. pose proof (fact_in_holds rho _ F Hb HF) as H. cbn [holds branch_taken eval] in H.
  unfold bv_ltu in H. rewrite Z_to_bv_unsigned, bv_wrap_small in H by (change (bv_modulus 64) with (2 ^ 64); lia).
  destruct (Z.ltb_spec (bv_unsigned (rw rho i)) k) as [L|L]; [exact L|]. exfalso. apply H. reflexivity.
Qed.

Definition entsI (L T : axst) : bool := ltac2:(tb__ "0|2|
S6S6S6S32VL;VT;S61S3aS2eVL;A1S2eVT;A1M0A3M1A3S5bG1S3aA2A2S31VT;A1A2S23G0A1A2").
Lemma ent_SPA : ltac2:(tb__ "0|0|
S27S2cS2cS11S1S34Q40A1A1S38SdS2S48R5R4A2S3A3S28S0S3aR7A3S26S0R8R7R5R4R3A6S58R6S61S3aS2eR8A1S2eR7A1A3A2S11SeS26S0RaR8R1R6R5A6S14S3aR7R1A3A2Trho';F_;F_;F_;Fw;Ftp;Frho;FT;FL;FJ;").
Proof.
  intros J L T rho tp w H HST HS rho'. unfold entsI in H. apply andb_prop in H as [H _]. apply andb_prop in H as [H _]. apply andb_prop in H as [HE HI].
  split; [exact (SPA_entails segsA J NPRE L T _ rho tp w HE HI HST HS) | apply rho_sub_agree; exact HI].
Qed.
Lemma ent_cont : ltac2:(tb__ "0|0|
S27S38OF_;S2cS2cS11S1S34Q40A1A1S39SdS2S48R5R4A2S3A3S28S0S3aR8A3S11S14S3aR6R1A3S37S0RaS26S0RbR8R2R6A5R5A4F_;Frho';S37S0R9S26S0RaR8R6R5A5R4A4F_;F_;F_;FQ;Ftp;Frho;FT;FL;Fok;FJ;").
Proof.
  intros J ok L T rho tp Q H HST HC. eapply triple_conseq; [| intros w Hw; exact Hw | apply (HC (rho_sub rho (infer_sub NPRE (ax_S L) (ax_S T))))].
  - intros w Hw. exact (proj1 (ent_SPA J L T rho tp w H HST Hw)).
  - apply rho_sub_agree. unfold entsI in H. apply andb_prop in H as [H _]. apply andb_prop in H as [H _]. apply andb_prop in H as [_ HI]. exact HI.
Qed.
Lemma ent_econt : ltac2:(tb__ "0|0|
S27S2cS2cS11S1S34Q40A1A1S38OF_;SdS2S48R5R4A2S3A3S28S0S3aR7A3S11S14S3aR6R1A3S36S0S26S0RaR8R2R6A5R5A3F_;Frho';S36S0S26S0R9R8R6R5A5R4A3F_;F_;F_;FQ;Ftp;Frho;FT;FL;FJ;").
Proof.
  intros J L T rho tp Q H HST HC. eapply etriple_conseq; [| intros w Hw; exact Hw | apply (HC (rho_sub rho (infer_sub NPRE (ax_S L) (ax_S T))))].
  - intros w Hw. exact (proj1 (ent_SPA J L T rho tp w H HST Hw)).
  - apply rho_sub_agree. unfold entsI in H. apply andb_prop in H as [H _]. apply andb_prop in H as [H _]. apply andb_prop in H as [_ HI]. exact HI.
Qed.

Definition JQ (J : jpredA) : jpostA := ltac2:(tb__ "0|3|
S11S1S34Q40A1M0A1M1S11G1S1S45A1S44SeVJ;R4R3R2R1A4SeSdG1R3R5A3SeG0SdS7S34Q8A1M2A1S20R5R1A2S20R7R1A2A3Fa;S3eSdS1G2A1S1fR5R1A2S1fR7R1A2A3Fl;A2A2A2Lmd;Ltr;Ltp';Lrho';Ltp0;Lrho0;").
Lemma leaf_post : ltac2:(tb__ "0|1|
S27S38OF_;S2cS2cS11S11S1S34Q40A1A1S1S4S2cS52A2M0A1SdS2S48R6R5A2S3A3S28S0S3aR9A3S3fG0S8S2cS52R7S4cRaA1A4R3A3S14S3aR7R6A3S37S0RbS26S0RcRaR7R6A5S56S0S3aR8R6R5A5A4F_;F_;F_;F_;FPosts;Ftp;FrhoL;Frho0;FPost;FL;Fok;FJ;").
Proof.
  intros J ok L Post rho0 rhoL tp Posts H HST HIN Hag. eapply triple_conseq; [| intros w Hw; exact Hw | apply triple_refl].
  intros w Hw. destruct (ent_SPA J L Post rhoL tp w H HST Hw) as [HP Hag'].
  pose proof (agree_below_trans _ _ _ _ Hag Hag') as (Hrw & Hrl & Hrm).
  apply (LQPA_intro segsA NPRE rho0 tp Posts Post (JQ J) _ tp w J HIN HP).
  - split; [exact Hrw | exact Hrl].
  - intros HJ. split; [exact HJ|]. split; [reflexivity|]. split; [intros a; symmetry; apply Hrm | intros l0; symmetry; apply Hrl].
Qed.
Lemma leaf_epost : ltac2:(tb__ "0|1|
S27S2cS2cS11S11S1S34Q40A1A1S1S4S2cS52A2M0A1SdS2S48R6R5A2S3A3S28S0S3aR8A3S3fG0S8S2cS52R7S4cR9A1A4R3A3S14S3aR7R6A3S36S0S26S0RbRaR7R6A5S56S0S3aR8R6R5A5A3F_;F_;F_;F_;FPosts;Ftp;FrhoL;Frho0;FPost;FL;FJ;").
Proof.
  intros J L Post rho0 rhoL tp Posts H HST HIN Hag. eapply etriple_conseq; [| intros w Hw; exact Hw | apply etriple_refl].
  intros w Hw. destruct (ent_SPA J L Post rhoL tp w H HST Hw) as [HP Hag'].
  pose proof (agree_below_trans _ _ _ _ Hag Hag') as (Hrw & Hrl & Hrm).
  apply (LQPA_intro segsA NPRE rho0 tp Posts Post (JQ J) _ tp w J HIN HP).
  - split; [exact Hrw | exact Hrl].
  - intros HJ. split; [exact HJ|]. split; [reflexivity|]. split; [intros a; symmetry; apply Hrm | intros l0; symmetry; apply Hrl].
Qed.

Lemma call_soundA_tp : ltac2:(tb__ "0|3|
S38OF_;S27S27S27S27S2cS2cS5aS1S18A1M0S1S2dA1S39S11S1S34Q40A1A1M1SdS7G0A1S54R8R7R6A3SaG0R5A2A3SdS2S53R9R8R7R6S43S2dS2cS2fR5A4A5S3A3S11G1S37S0R11S26S0RfRbR2R1A5S29S0ReS15S2eRbA1A1R2R1R8A6A4Ftp1;Frho1;S1S45A1M2S4fS44S2bS0R8R7ReS8G2S50R3S51R2R1A2A4A5R13R9R8R4R2A4R13S58S59RaRdS57R3R9R4A3A3ReA2R9R5R3A4F_;F_;Fmd;Fms;Ftr;S2dS11S11G2S4fS44G2S44S3fS2dR8R10A3S2bS0RfReR15S8G2S50R6S51R5R4A2A4A5R1aR10RfR7R5A4S62R11S57R6R10R7A3R14R15S2eR16A1S2eR17A1S2eS2fRbA1A1RaR9A9R1aRaR11R6R5A4R1aRcR12R7R6A4F_;F_;F_;F_;F_;Fmd';Ftr';Fmd;Fms;Ftr;FrhoL;Frho';FL;S2dS11S3fS2dR2RbA3S14S15S2eR10A1A1RaR2A3S37S0R16S26S0R12S55RfR10S2fR4A1R11ReA5R3RaA5RcA4F_;F_;Frho';FL;S37S0R13S26S0R12ReR8R7A5R9A4F_;F_;F_;F_;F_;F_;Ftp;Frho;FQ;FPosts;FR;Fs;FPre;FC;FJc;FJp';FJp;FJ;Fok;").
Proof.
  intros ok J Jp Jp' Jc C Pre s R Posts Q rho tp He Hchk Hsum Hin Hout Hcont.
  intros n HgQ w [Hsm Hk]. destruct w as [tr [ms md]].
  destruct (entails_frA_sound segsA C Pre s R rho tp tr ms md He Hsm) as (HsmPre & _).
  apply (Hsum (rho_sub (rho_absorb rho R (vms md tp ms)) s) tp n); [|split; [exact HsmPre|exact (Hin tr ms md Hsm Hk)]].
  intros w' (L & rhoL & HinL & HagL & HsmL & Hk'). destruct w' as [tr' [ms' md']].
  cbn [w_tr w_cfg fst snd cfg_model] in Hk'.
  destruct (import_post_linkA segsA C Pre s R (map la_state Posts) rho tp tr ms md tr' ms' md' (la_state L) rhoL tp He Hchk Hsm
              ltac:(apply in_map_iff; exists L; auto) HagL HsmL) as (rho' & HLK & HSP).
  pose proof (proj1 HLK) as HAG.
  apply (Hcont L rho' HinL HAG n HgQ). split; [exact HSP|].
  exact (Hout L rho' rhoL tr ms md tr' md' HinL Hsm Hk HLK Hk').
Qed.
Lemma call_completeA_tp : ltac2:(tb__ "0|3|
S27S27S27S27S2cS2cS5aS1S18A1M0S1S2dA1S38OF_;S11S1S34Q40A1A1M1SdS7G0A1S54R8R7R6A3SaG0R5A2A3SdS2S53R9R8R7R6S43S2dS2cS2fR5A4A5S3A3S11G1S36S0S26S0RfRbR2R1A5S29S0ReS15S2eRbA1A1R2R1R8A6A3Ftp1;Frho1;S1S45A1M2S4fS44S2bS0R8R7ReS8G2S50R3S51R2R1A2A4A5R13R9R8R4R2A4R13S58S59RaRdS57R3R9R4A3A3ReA2R9R5R3A4F_;F_;Fmd;Fms;Ftr;S2dS11S11G2S4fS44G2S44S3fS2dR8R10A3S2bS0RfReR15S8G2S50R6S51R5R4A2A4A5R1aR10RfR7R5A4S62R11S57R6R10R7A3R14R15S2eR16A1S2eR17A1S2eS2fRbA1A1RaR9A9R1aRaR11R6R5A4R1aRcR12R7R6A4F_;F_;F_;F_;F_;Fmd';Ftr';Fmd;Fms;Ftr;FrhoL;Frho';FL;S2dS11S3fS2dR2RbA3S14S15S2eR10A1A1RaR2A3S36S0S26S0R12S55RfR10S2fR4A1R11ReA5R3RaA5RcA3F_;F_;Frho';FL;S36S0S26S0R12ReR8R7A5R9A3F_;F_;F_;F_;F_;F_;Ftp;Frho;FQ;FPosts;FR;Fs;FPre;FC;FJc;FJp';FJp;FJ;").
Proof.
  intros J Jp Jp' Jc C Pre s R Posts Q rho tp He Hchk Hsum Hin Hout Hcont.
  intros w [Hsm Hk]. destruct w as [tr [ms md]].
  destruct (entails_frA_sound segsA C Pre s R rho tp tr ms md He Hsm) as (HsmPre & _).
  destruct (Hsum (rho_sub (rho_absorb rho R (vms md tp ms)) s) tp _ (conj HsmPre (Hin tr ms md Hsm Hk))) as (w' & Hsteps & HLQ).
  destruct HLQ as (L & rhoL & HinL & HagL & HsmL & Hk'). destruct w' as [tr' [ms' md']].
  cbn [w_tr w_cfg fst snd cfg_model] in Hk'.
  destruct (import_post_linkA segsA C Pre s R (map la_state Posts) rho tp tr ms md tr' ms' md' (la_state L) rhoL tp He Hchk Hsm
              ltac:(apply in_map_iff; exists L; auto) HagL HsmL) as (rho' & HLK & HSP).
  pose proof (proj1 HLK) as HAG.
  destruct (Hcont L rho' HinL HAG _ (conj HSP (Hout L rho' rhoL tr ms md tr' md' HinL Hsm Hk HLK Hk'))) as (w'' & Hsteps' & HQ).
  exists w''. split; [eapply wsteps_trans; eauto | exact HQ].
Qed.

Section OpaqueCall.
Variables (Cst : axst) (Pre : axst) (Posts : list leafA) (s : wsub) (R : list sobj) (T : axst) (g : positive).
Hypothesis Hsum : ltac2:(tb__ "0|1|
S38OF_;S27S11S1S34Q40A1A1S2aS0R4R3A3S28S0S15S2eVPre;A1A1M0R4A3S37S0R6S26S0R5VPre;R4R3A5S29S0R5G0R4R3VPosts;A6A4F_;F_;Ftp;Frho;FJx;Fok;").
Hypothesis Hesum : ltac2:(tb__ "0|1|
S27S11S1S34Q40A1A1S28S0S15S2eVPre;A1A1M0R3A3S36S0S26S0R4VPre;R3R2A5S29S0R4G0R3R2VPosts;A6A3F_;Ftp;Frho;FJx;").
Hypothesis He : ltac2:(tb__ "0|1|
SdS7S1S18A1M0A1S54VCst;VPre;Vs;A3SaG0VR;A2A3").
Hypothesis Hchk : ltac2:(tb__ "0|0|
SdS2S53VCst;VPre;Vs;VR;S43S2dS2cS2fVPosts;A4A5S3A3").
Hypothesis HT : ltac2:(tb__ "0|0|
S2dS3fS2dR1VPosts;A3SdS2cS55Vs;VPre;S2fR2A1VCst;VR;A5VT;A3F_;FP;").
Hypothesis FBC : ltac2:(tb__ "0|1|
SdS2S40S13S19S15S2eVCst;A1M0A1A1S17G0A1A3S3A3").
Hypothesis FBT : ltac2:(tb__ "0|0|
SdS2S40S13S19S15S2eVT;A1A1A1S17S2eVCst;A1A1A3S3A3").
Hypothesis NXC : ltac2:(tb__ "0|0|
S65Vg;S15S2eVCst;A1A1A2").

Theorem call_cont : ltac2:(tb__ "0|1|
S27S38OF_;S11S1S34Q40A1A1S39S2aS0R4R5A3S28S0Vg;R6A3S11S14S15S2eVCst;A1M0A1R6R1A3S37S0R8S26S0R9S63VT;S17G0A1A2R2R6A5R5A4F_;Frho';S37S0R7S26S0R8VCst;R6R5A5R4A4F_;F_;F_;FQ;Ftp;FrhoE;Fok;FJ;").
Proof.
  intros J ok rhoE tp Q HOK HST HC.
  set (Jf := (fun (_ : valuation) t tr md => J rhoE t tr md) : jpredA).
  assert (Jf_okf : ok_frameA segsA ok Jf) by (intros r t tr ms md msv' HJ; exact (HOK rhoE t tr ms md msv' HJ)).
  assert (Jf_st : stableA segsA (ss_next (ax_S Pre)) Jf).
  { intros r r' t tr md md' Hag Hme HJ. unfold Jf in *. eapply HST; [apply agree_below_refl | exact Hme | exact HJ]. }
  apply (triple_pre_pure segsA ok _ _ (Forall (holds rhoE) (ss_facts (ax_S Cst)))).
  { intros w Hw. exact (SPA_facts_hold segsA _ rhoE Cst tp w Hw). }
  intros HFC.
  apply (call_soundA_tp ok J Jf Jf J Cst Pre s R Posts Q rhoE tp He Hchk).
  - intros rho1 tp1. exact (Hsum ok Jf rho1 tp1 Jf_okf Jf_st).
  - intros tr ms md Hsm HJ. exact HJ.
  - intros L rho' rhoL tr ms md tr' md' HinL Hsm HJ HLK HJ'. unfold Jf in HJ'.
    eapply HST; [| apply mat_equiv_refl | exact HJ']. eapply agree_below_le; [exact NXC | exact (proj1 HLK)].
  - intros L rho' HinL Hag. rewrite (HT L HinL).
    eapply triple_conseq; [intros w Hw | intros w Hw; exact Hw | apply (HC rho' Hag)].
    apply SPA_refacts; [exact Hw | exact FBT | intros _; exact (Forall_holds_agree _ rhoE rho' _ Hag FBC HFC)].
Qed.
Theorem call_econt : ltac2:(tb__ "0|1|
S27S11S1S34Q40A1A1S38OF_;S28S0Vg;R4A3S11S14S15S2eVCst;A1M0A1R5R1A3S36S0S26S0R7S63VT;S17G0A1A2R2R5A5R4A3F_;Frho';S36S0S26S0R6VCst;R5R4A5R3A3F_;F_;FQ;Ftp;FrhoE;FJ;").
Proof.
  intros J rhoE tp Q HST HC.
  set (Jf := (fun (_ : valuation) t tr md => J rhoE t tr md) : jpredA).
  assert (Jf_st : stableA segsA (ss_next (ax_S Pre)) Jf).
  { intros r r' t tr md md' Hag Hme HJ. unfold Jf in *. eapply HST; [apply agree_below_refl | exact Hme | exact HJ]. }
  intros w Hw. pose proof (SPA_facts_hold segsA _ rhoE Cst tp w Hw) as HFC. revert w Hw.
  apply (call_completeA_tp J Jf Jf J Cst Pre s R Posts Q rhoE tp He Hchk).
  - intros rho1 tp1. exact (Hesum Jf rho1 tp1 Jf_st).
  - intros tr ms md Hsm HJ. exact HJ.
  - intros L rho' rhoL tr ms md tr' md' HinL Hsm HJ HLK HJ'. unfold Jf in HJ'.
    eapply HST; [| apply mat_equiv_refl | exact HJ']. eapply agree_below_le; [exact NXC | exact (proj1 HLK)].
  - intros L rho' HinL Hag. rewrite (HT L HinL).
    eapply etriple_conseq; [intros w Hw | intros w Hw; exact Hw | apply (HC rho' Hag)].
    apply SPA_refacts; [exact Hw | exact FBT | intros _; exact (Forall_holds_agree _ rhoE rho' _ Hag FBC HFC)].
Qed.
End OpaqueCall.
End SegQlib.

(* [comment removed for export] *)
Module SegQ1.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "NPRE"; "PostQ1A"; "PostQ1Be"; "PostQ1Bf"; "PreQ1A"; "PreQ1Be"; "PreQ1Bf"; "chk1p"; "runA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "leafA"; "ax_S"; "la_state"; "entailsA"; "sym_runA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@Corelib.Init.Datatypes"; "list"; "cons"; "nil"; "pair"; "prod"; "true"; "bool"; "option"; "Some"; "false"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rl"; "rm"; "ss_lenient"; "ss_next"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "jpredA"; "stableA"; "SPA"; "ok_frameA"; "LQA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQ1"; "JQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@Corelib.Numbers.BinNums"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Open Scope Z_scope.

Definition JQ (J : jpredA) : jpostA := ltac2:(tb__ "0|3|
S1fS12S24Q40A1M0A1M1S1fG1S12S32A1S31S1dVJ;R4R3R2R1A4S1dS1cG1R3R5A3S1dG0S1cS19S24Q8A1M2A1S21R5R1A2S21R7R1A2A3Fa;S2fS1cS12G2A1S20R5R1A2S20R7R1A2A3Fl;A2A2A2Lmd;Ltr;Ltp';Lrho';Ltp0;Lrho0;").

Section Straight.
Variables (fuel : nat) (cuts : list Z) (retpc : Z) (Pre Post : axst) (l : list leafA).
Hypothesis HNX : ltac2:(tb__ "0|0|
S1cS2fS23ScVPre;A1A1S1A3").
Hypothesis HLEN : ltac2:(tb__ "0|0|
S1cS18S22ScVPre;A1A1S1bA3").
Hypothesis RUNL : ltac2:(tb__ "0|0|
S1cS12SbA1S9Vfuel;Vcuts;VPre;A3Vl;A3").
Hypothesis CHK : ltac2:(tb__ "0|0|
S1cS18S8Vretpc;Vl;VPost;A3S17A3").

Lemma chk1_run : ltac2:(tb__ "0|3|
S1eSbSbS1dS1cS19S12SbA1M0A1SfS0Vfuel;Vcuts;VPre;S17A5S1aG0S13SbR1S14SbA1A3A2A3S1dS1cS18SeSdR1A1M1VPost;S2eS1ScG1A1ScVPost;A1A3M2A3S17A3S1cS18S30G2S1A2S17A3A2A2LL;A2").
Proof.
  pose proof CHK as C. rewrite <- RUNL in C. unfold chk1p, single_ret, runA in C.
  destruct (sym_runA segsA fuel cuts Pre true) as [[|L [|L' l']]|] eqn:E; try discriminate C.
  apply andb_prop in C as [C W]. apply andb_prop in C as [C I]. apply andb_prop in C as [_ EN].
  exists L. split; [reflexivity|]. unfold ents, leaf in EN, I. cbn [nth] in EN, I. split; [exact EN | exact I].
Qed.

Lemma straight_post : ltac2:(tb__ "0|5|
S25S1fS12S24Q40A1A1S2bSbS26S0S1R5A3S1cS19S12SbA1M0A1SfS0Vfuel;Vcuts;VPre;S17A5S1aG0S13SbR2S14SbA1M1A3A2A3S1cS18SeSdR3A1M2VPost;S2eS1ScG2A1ScVPost;A1M3A3A3S17A3S1cS18S30S2eS1ScSdR4A1A1G3A3S1A2S17A3S29S0R9S1R8R7S13SbR5G1A3R6A7S11S0S1R9R8S13S16SaS10A2M4S15SaS10VPost;S2aRaA1A4S14G4A1A3R7A6F_;F_;F_;F_;F_;FL;Fw;Ftp;Frho;FJ;").
Proof.
  intros J rho tp w L HST RUN EN ID (L' & rho' & Hin & Hag & Hsm & Hk).
  destruct Hin as [<-|[]].
  set (s := infer_sub NPRE (ax_S (la_state L)) (ax_S Post)) in *.
  pose proof (SPA_entails segsA J NPRE (la_state L) Post s rho' tp w EN ID HST (conj Hsm Hk)) as HP.
  pose proof Hag as (Hrw & Hrl & Hrm).
  apply (LQPA_intro segsA NPRE rho tp _ Post (JQ J) (rho_sub rho' s) tp w J); [left; reflexivity | exact HP | |].
  - split; [| intros l0; cbn; apply Hrl]. intros i Hi. cbn. rewrite (wsub_get_id s NPRE i ID Hi). cbn. apply Hrw. exact Hi.
  - intros HJ. split; [exact HJ|]. split; [reflexivity|]. split; [intros a; cbn; symmetry; apply Hrm | intros l0; cbn; symmetry; apply Hrl].
Qed.

Theorem straight_sound : ltac2:(tb__ "0|1|
S25S2bOF_;S1fS12S24Q40A1A1S28S0R3R4A3S26S0S1R5A3S2dS0R5S27S0R6VPre;R4R3A5S11S0S1R4R3S13S16SaS10A2M0S15SaS10VPost;S2aR6A1A4S14G0A1A3A5A4F_;F_;Ftp;Frho;Fok;FJ;").
Proof.
  intros J ok rho tp HOK HST. destruct chk1_run as (L & RUN & EN & ID).
  eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (straight_post J rho tp w L HST RUN EN ID Hw) |].
  apply triple1_triple. rewrite <- HNX. apply (sym_run_soundA segsA fuel cuts Pre [L] ok J rho tp RUN HOK HLEN). rewrite HNX. exact HST.
Qed.

Theorem straight_complete : ltac2:(tb__ "0|1|
S25S1fS12S24Q40A1A1S26S0S1R3A3S2cS0S27S0R4VPre;R3R2A5S11S0S1R3R2S13S16SaS10A2M0S15SaS10VPost;S2aR4A1A4S14G0A1A3A5A3F_;Ftp;Frho;FJ;").
Proof.
  intros J rho tp HST. destruct chk1_run as (L & RUN & EN & ID).
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (straight_post J rho tp w L HST RUN EN ID Hw) |].
  rewrite <- HNX. apply (sym_run_etripleA segsA fuel cuts Pre [L] J rho tp HLEN). rewrite HNX. exact HST. exact RUN.
Qed.
End Straight.

Section Arms.
Let NX := pre_nx.
Theorem seg_Q1A_sound : ltac2:(tb__ "0|1|
S25S2bOF_;S1fS12S24Q40A1A1S28S0R3R4A3S26S0S1R5A3S2dS0R5S27S0R6S5R4R3A5S11S0S1R4R3S13S16SaS10A2M0S15SaS10S2S2aR6A1A4S14G0A1A3A5A4F_;F_;Ftp;Frho;Fok;FJ;").
Proof. intros J ok rho tp HOK HST. exact (straight_sound 400%nat [CREF] RETQ PreQ1A PostQ1A run_A (proj1 NX) (proj1 (proj2 (proj2 (proj2 NX)))) run_A_eq chk_A J ok rho tp HOK HST). Qed.
Theorem seg_Q1A_complete : ltac2:(tb__ "0|1|
S25S1fS12S24Q40A1A1S26S0S1R3A3S2cS0S27S0R4S5R3R2A5S11S0S1R3R2S13S16SaS10A2M0S15SaS10S2S2aR4A1A4S14G0A1A3A5A3F_;Ftp;Frho;FJ;").
Proof. intros J rho tp HST. exact (straight_complete 400%nat [CREF] RETQ PreQ1A PostQ1A run_A (proj1 NX) (proj1 (proj2 (proj2 (proj2 NX)))) run_A_eq chk_A J rho tp HST). Qed.

Theorem seg_Q1Be_sound : ltac2:(tb__ "0|1|
S25S2bOF_;S1fS12S24Q40A1A1S28S0R3R4A3S26S0S1R5A3S2dS0R5S27S0R6S6R4R3A5S11S0S1R4R3S13S16SaS10A2M0S15SaS10S3S2aR6A1A4S14G0A1A3A5A4F_;F_;Ftp;Frho;Fok;FJ;").
Proof. intros J ok rho tp HOK HST. exact (straight_sound 400%nat [CREF] RETQ PreQ1Be PostQ1Be run_Be (proj1 (proj2 NX)) (proj1 (proj2 (proj2 (proj2 (proj2 NX))))) run_Be_eq chk_Be J ok rho tp HOK HST). Qed.
Theorem seg_Q1Be_complete : ltac2:(tb__ "0|1|
S25S1fS12S24Q40A1A1S26S0S1R3A3S2cS0S27S0R4S6R3R2A5S11S0S1R3R2S13S16SaS10A2M0S15SaS10S3S2aR4A1A4S14G0A1A3A5A3F_;Ftp;Frho;FJ;").
Proof. intros J rho tp HST. exact (straight_complete 400%nat [CREF] RETQ PreQ1Be PostQ1Be run_Be (proj1 (proj2 NX)) (proj1 (proj2 (proj2 (proj2 (proj2 NX))))) run_Be_eq chk_Be J rho tp HST). Qed.

Theorem seg_Q1Bf_sound : ltac2:(tb__ "0|1|
S25S2bOF_;S1fS12S24Q40A1A1S28S0R3R4A3S26S0S1R5A3S2dS0R5S27S0R6S7R4R3A5S11S0S1R4R3S13S16SaS10A2M0S15SaS10S4S2aR6A1A4S14G0A1A3A5A4F_;F_;Ftp;Frho;Fok;FJ;").
Proof. intros J ok rho tp HOK HST. exact (straight_sound 400%nat [CREF] RETQ PreQ1Bf PostQ1Bf run_Bf (proj1 (proj2 (proj2 NX))) (proj2 (proj2 (proj2 (proj2 (proj2 NX))))) run_Bf_eq chk_Bf J ok rho tp HOK HST). Qed.
Theorem seg_Q1Bf_complete : ltac2:(tb__ "0|1|
S25S1fS12S24Q40A1A1S26S0S1R3A3S2cS0S27S0R4S7R3R2A5S11S0S1R3R2S13S16SaS10A2M0S15SaS10S4S2aR4A1A4S14G0A1A3A5A3F_;Ftp;Frho;FJ;").
Proof. intros J rho tp HST. exact (straight_complete 400%nat [CREF] RETQ PreQ1Bf PostQ1Bf run_Bf (proj1 (proj2 (proj2 NX))) (proj2 (proj2 (proj2 (proj2 (proj2 NX))))) run_Bf_eq chk_Bf J rho tp HST). Qed.
End Arms.
End SegQ1.

