(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "cons"; "andb"; "bool"; "list"; "nil"; "true"; "@Stdlib.ZArith.BinInt.Z"; "add"; "mul"; "div"; "leb"; "le"; "eqb"; "modulo"; "sub"; "max"; "to_nat"; "min"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCredit"; "MUCAP"; "CLS30"; "FACAP"; "nmin"; "sumZ"; "NBQ"; "prim_credit"; "qmax"; "PRIM0"; "QCAP"; "cap_okb"; "creditF"; "creditU"; "credit_c"; "nmin_tab"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "Size"; "kUserMapSize"; "ClassID"; "kFreeArrayMapSize"; "needed"; "kFreeArraySize"; "kQuarantineBatchCount"; "kUserSpaceSize"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "aa_cls"; "class_state"; "AA"; "PRIM_LIVE_MAX"; "cs_empty"; "cs_mapped_free_array"; "cs_mapped_user"; "@Corelib.Lists.ListDef"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget"; "QPRIM"; "@Stdlib.Lists.List"; "In"; "fold_right"; "forallb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition QCAP : Z := kQuarantineMax + kQuarantineCacheMax.
Definition NBQ : Z := QCAP / kQuarantineBatchSize.

Definition nmin_tab : list Z := ltac2:(tb__ "0|0|
S1S0Z1S1S0Z11S1S0Z31S1S0Z41S1S0Z0S1S0Z61S1S0Z81S1S0Za1S1S0Zc1S1S0Ze1S1S0Z101S1S0Z121S1S0Z141S1S0Z161S1S0Z181S1S0Z1a1S1S0Z1c1S1S0Z281S1S0Z381S1S0Z581S1S0Z781S1S0Zb81S1S0Zf81S1S0Z1701S1S0Z1f01S1S0Z2f01S1S0Z3f01S1S0Z5e01S1S0Z7e01S1S0Zbc01S5S0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition nmin (c : Z) : Z := ltac2:(tb__ "0|0|
S32S0S10SeVc;Z1A2A1S20Z0A4").

Definition qmax (c : Z) : Z := ltac2:(tb__ "0|3|
S7S3S0L_;M0ScS15Vc;A1M1Z0M2A2G2S11S8S29S17A2S9S1bG1A2A2X3x2G0ScVc;Z18A2S17G2X3x2A2").

Definition MUCAP (c : Z) : Z := ltac2:(tb__ "0|1|
S7S7S8S23Vc;A1M0S7S7S7S2eZ1A2S19Vc;A1A2Z8A2A2G0A2S24A2").
Definition FACAP (c : Z) : Z := ltac2:(tb__ "0|0|
S7S8Z8S7S9S9S12Vc;A1S23Vc;A1A2Z2A2Z1A2A2S26A2").

Definition creditU (c : Z) (cs : class_state) : Z := ltac2:(tb__ "0|0|
SfZ0S9S8Z9SeS12Vc;A1S31Vcs;A1A2A2Z8A2A2").
Definition creditF (c : Z) (cs : class_state) : Z := ltac2:(tb__ "0|0|
SfZ0S9S8Z9SeS14Vc;A1S30Vcs;A1A2A2Z8A2A2").
Definition credit_c (A : AA) (c : Z) : Z := ltac2:(tb__ "0|0|
S32S2cS10Vc;A1S2bVA;A1S2fA4S2cS7S1eVc;R1A2S1dVc;R1A2A2Tcs;").

Definition CLS30 : list Z := map Z.of_nat (seq 1 30).
Definition sumZ (f : Z -> Z) (l : list Z) : Z := ltac2:(tb__ "0|0|
S35S0S0S0S0S7Vf;R2A1R1A2Lacc;Lc;Z0Vl;A5").
Definition prim_credit (A : AA) : Z := ltac2:(tb__ "0|0|
S16S1fVA;A1S13A2").

Lemma creditU_nonneg : forall c cs, 0 <= creditU c cs.
Proof. intros. unfold creditU. apply Z.le_max_l. Qed.
Lemma creditF_nonneg : forall c cs, 0 <= creditF c cs.
Proof. intros. unfold creditF. apply Z.le_max_l. Qed.
Lemma credit_c_nonneg : forall A c, 0 <= credit_c A c.
Proof. intros. unfold credit_c. cbn zeta. apply Z.add_nonneg_nonneg; [apply creditU_nonneg | apply creditF_nonneg]. Qed.
Lemma sumZ_nonneg : ltac2:(tb__ "0|1|
S0S0Fx;S4S0A1S0S34S0R1R2A3SbZ0M0R4R2A1A2F_;Fc;SbG0S16R3R2A2A2F_;Fl;Ff;").
Proof. intros f. induction l as [|x l IH]; intros H; [cbn; lia|]. change (0 <= f x + sumZ f l). pose proof (H x (or_introl eq_refl)). specialize (IH (fun c Hc => H c (or_intror Hc))). lia. Qed.
Lemma prim_credit_nonneg : forall A, 0 <= prim_credit A.
Proof. intros A. apply sumZ_nonneg. intros c _. apply credit_c_nonneg. Qed.

Lemma prim_credit_same : ltac2:(tb__ "0|0|
S2dS2dS21S4S2cA1S2bR1A1S2bR2A1A3S21S0S18R2A1S18R3A1A3F_;FA';FA;").
Proof. intros A A' E. unfold prim_credit, credit_c. rewrite E. reflexivity. Qed.

Definition PRIM0 : Z := ltac2:(tb__ "0|2|
S16S0S7S9S8Z9M0S12R1A1A2Z8M1A2S9S8G0S14R1A1A2G1A2A2Lc;S13A2").
Lemma QPRIM_ok : ltac2:(tb__ "0|0|
SbS1aS7S8Z1eS8Z2S7S24S9S24Z8A2A2A2A2S33A2A2").
Proof. apply Z.leb_le. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition cap_okb (c : Z) : bool := ltac2:(tb__ "0|5|
S2S2S2S2S2S2S2S2SaZ20S23Vc;A1M0A2SaG0Z10000A2A2ScSdG0Z10A2Z0M1A2A2SaS12Vc;A1M2S2aA2A2ScSdG2Z8M3A2G1A2A2SaS14Vc;A1M4S28A2A2ScSdG4G3A2G1A2A2SaS7S8Z4S9G2G0A2A2S26A2G4A2A2SaG1S19Vc;A1A2A2").
Lemma cap_okb_all : ltac2:(tb__ "0|0|
S21S3S36S0S1cS13A3S6A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition nmin_okb (n : Z) : bool := ltac2:(tb__ "0|0|
S15S25S27Vn;A1A1A1S0S2SaZ1R1A2SaR1Vn;A2A2Tm;").
Lemma nmin_ok : ltac2:(tb__ "0|2|
S0S22SbZ1M0R1A2SbR1Zfc00A2A2S22SbG0S15S25S27R2A1A1A1M1A2SbG1R2A2A2F_;Fn;").
Proof.
  intros n Hn. assert (H : nmin_okb n = true) by (apply (forall_rangeZ_ok nmin_okb 1 64512); [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | lia]).
  unfold nmin_okb in H. cbn zeta in H. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1, H2. lia.
Qed.
