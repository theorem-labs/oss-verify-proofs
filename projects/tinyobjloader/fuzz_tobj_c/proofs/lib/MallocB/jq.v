(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia FunctionalExtensionality.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jn jp.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ja.

(* [comment removed for export] *)
Module SpineMallocR5.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "iff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "cls_keptA"; "cs_cache"; "aa_Kf"; "aa_Km"; "aa_V"; "aa_cls"; "aa_fs_busy"; "aa_geom"; "aa_live"; "class_fresh"; "class_state"; "ageom"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "list"; "length"; "bool"; "prod"; "true"; "nat"; "nil"; "orb"; "cons"; "option"; "pair"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rm"; "rw"; "sv"; "SVar"; "mkVal"; "rl"; "sv_eqb"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "mem_keptA"; "KcA"; "JL_malloc_ok"; "AE_A"; "JL_malloc_null"; "client_addrA"; "client_shadowA"; "ulink"; "L_malloc_ok"; "Posts_malloc"; "UStopLeOrPc"; "ustop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub"; "rho_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jq.SpineMallocR5"; "rho_after"; "same_client"; "posts_conv"; "sx_okb"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillJ"; "JR"; "entryR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "cls_of"; "cst_of"; "rhoM_of"; "chk_of"; "cnt_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel"; "refillA"; "refill_cs"; "kchunks"; "@Corelib.Init.Peano"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR"; "vCHX"; "vK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1"; "JG"; "@Stdlib.PArith.BinPos.Pos"; "eqb"; "lt"; "of_nat"; "@Stdlib.ZArith.BinInt.Z"; "le"; "of_nat"; "to_nat"; "@Corelib.Init.Nat"; "sub"; "@Corelib.Lists.ListDef"; "nth"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jq.SpineMallocR5.PCONV"; "PF_malloc"; "PF_ok"; "@Stdlib.Lists.List"; "forallb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA GlueA2 SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildSM SMGlue InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNullInit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildM PrimCredit PrimCreditLaws RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillTR RefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require io.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jn.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCredit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCreditLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocR1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SpineMallocR2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jc.SpineMallocR3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jn.SpineMallocR4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation segs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree.segsA.

Definition sx_okb (s : wsub) : bool := ltac2:(tb__ "0|0|
S60S18S18S56R1A1S12S1aS1aS25S37Vs;R1A2S22R1A1A2S54R1P95A2A2S54R1P9fA2A2Ti;Ln;S5cU1U9fA2A3").
Lemma sx_ok_id : ltac2:(tb__ "0|0|
S38S12S0S15S3fR2A1S17A3S55R2S29A2S2S0S12R3P95A3A1S2S0S12R4P9fA3A1S0S21S37R6R5A2S22R5A1A3F_;F_;F_;F_;Fi;Fs;").
Proof.
  intros s i H Hi H1 H2. unfold sx_okb in H.
  pose proof (proj1 (forallb_forall _ _) H (Pos.to_nat i) ltac:(apply in_seq; unfold GW in Hi; lia)) as X. cbv beta zeta in X. rewrite Pos2Nat.id in X.
  apply orb_prop in X as [X|X]; [apply orb_prop in X as [X|X]|].
  - apply sv_eqb_sound in X. exact X.
  - apply Pos.eqb_eq in X. contradiction.
  - apply Pos.eqb_eq in X. contradiction.
Qed.

Definition rho_after (rho r : valuation) : valuation := ltac2:(tb__ "0|0|
S23S20Vrho;A1S24Vrho;A1S1fVr;A1A3").

Lemma rhoM_refill : ltac2:(tb__ "0|0|
S4S1eS1eS11S12S2S0S12R1P95A3A1S2S0S12R2P9fA3A1S0S26Q40A1S20S46S4bR7R4A2S3cR6R5A2A2R3A2S20S46R7R6A2R3A2A3F_;F_;Fi;Fc;Fr;Frho;FA;").
Proof.
  intros A rho r c i H1 H2. unfold rhoM_of, rho_sets. cbn [rw rho_set_rw rho_after aa_geom refillA aa_ptr_committed aa_sec].
  repeat match goal with |- context [Pos.eqb i ?kk] => destruct (Pos.eqb_spec i kk); [try reflexivity; try contradiction|] end.
  reflexivity.
Qed.

Lemma cnt_of_refill : ltac2:(tb__ "0|1|
S4S11S4eS59S44R1A1A1S14SfSaR2A1A2A2S0S11S48S4bR3S44R2A1M0A2R2A2S58S14S11S6S4cG0S45R3R2A2A2A1A2A1A3F_;Fn;FA;").
Proof. intros A n H. unfold cnt_of, cst_of, refillA, nthZ. cbn [aa_cls]. rewrite nth_list_upd_same by exact H. reflexivity. Qed.
Lemma chk_of_refill : ltac2:(tb__ "0|1|
S4S11S4eS59S44R1A1A1S14SfSaR2A1A2A2S0S11S47S4bR3S44R2A1M0A2R2A2S6S4cG0S45R3R2A2A2A1S13S11A1S5bS11S5aS14S11R1A2U1A2R1Z0A4Tl;A3F_;Fn;FA;").
Proof. intros A n H. unfold chk_of, cst_of, refillA, nthZ. cbn [aa_cls]. rewrite nth_list_upd_same by exact H. reflexivity. Qed.

Definition same_client (A Ar : AA) : Prop := ltac2:(tb__ "0|1|
S1S0S10ScVAr;A1ScVA;A1A3S1S0S13S16S11S11A2A1M0SdVAr;A1SdVA;A1A3S1S0S13G0A1SbVAr;A1SbVA;A1A3S1S0S11S9VAr;A1S9VA;A1A3S1S0S11S8VAr;A1S8VA;A1A3S0S11S7VAr;A1S7VA;A1A3A2A2A2A2A2").

Definition posts_conv (CST XGL : list (Z * Z)) (PFam : AA -> KcA -> list (axst * jpostA)) : Prop := ltac2:(tb__ "0|3|
S4S4S2bS1eS1eS13S26Q40M0A1A1M1G1S4fS3dR8R7A2S2aVCST;VXGL;R9R8S1fR6A1S1fR5A1A6S4S5RaR1S27G0S20R8PcM2A2A2A3S5RcR2S27G0S20R9G2A2A2A3F_;FA';S3aS28S36S3cR8R7A2R6VPFam;RaR9A2R4A6S3aS28S36R9R6VPFam;RcRaA2R5A6F_;F_;F_;F_;Fw;Ftp0;Ftp;Fr;Frho;FKc;FAr;FA;").

Section PCONV.
Variables CST XGL : list (Z * Z).
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Variables (W : list ulink) (st : ustop).

Lemma client_same : ltac2:(tb__ "0|0|
S4S4S3dR2R1A2S11S3S2fVCST;R3R1A3S2fVCST;R4R1A3A2Fa;F_;FAr;FA;").
Proof.
  intros A Ar (EG & EL & EF & _) a. unfold client_addrA, client_mut_addrA, aa_frames. rewrite EG, EL, EF. reflexivity.
Qed.
Lemma shadow_same : ltac2:(tb__ "0|0|
S4S4S3dR2R1A2S11S3S30VCST;VXGL;R3R1A4S30VCST;VXGL;R4R1A4A2Fa;F_;FAr;FA;").
Proof.
  intros A Ar HS a. unfold client_shadowA. split; (intros [(x & Hx & E)|H]; [left; exists x; split; [apply (client_same A Ar HS); exact Hx | exact E] | right; exact H]).
Qed.

Lemma mem_kept_trans : ltac2:(tb__ "0|2|
S4S4S4S26Q40A1S1cS26Q8A1A1F_;M0G0G0S3dR6R5A2S2aVCST;VXGL;R7R6R4R3A6M1G1S2aVCST;VXGL;R9R7R6R4A6F_;F_;F_;Fm2;Fm1;Fm0;FA';FAr;FA;").
Proof.
  intros A Ar A' m0 m1 m2 HS [K1 K2] [K1' K2']. split.
  - intros a Ha [(H1 & H2 & H3)|(H1 & H2 & H3)].
    + pose proof (proj2 (client_same A Ar HS a) H1) as H1r.
      rewrite (K1' a Ha (or_introl (conj H1r (conj H2 H3)))). exact (K1 a Ha (or_introl (conj H1 (conj H1r H3)))).
    + pose proof (proj2 (shadow_same A Ar HS a) H1) as H1r.
      assert (E1 : m1 (Z_to_bv 64 a) = m0 (Z_to_bv 64 a)) by exact (K1 a Ha (or_intror (conj H1 (conj H1r H3)))).
      assert (D1 : m1 (Z_to_bv 64 a) <> None) by (rewrite E1; exact H3).
      rewrite (K1' a Ha (or_intror (conj H1r (conj H2 D1)))). exact E1.
  - intros x j Hx Hj Hd.
    assert (Hxr : client_addrA CST A x /\ client_addrA CST Ar x \/ in_rangesZ XGL x).
    { destruct Hx as [[X1 X2]|X]; [left; split; [exact X1 | apply (client_same A Ar HS); exact X1] | right; exact X]. }
    apply (K2' x j); [destruct Hx as [[X1 X2]|X]; [left; split; [apply (client_same A Ar HS); exact X1 | exact X2] | right; exact X] | exact Hj|].
    exact (K2 x j Hxr Hj Hd).
Qed.

Lemma conv_null : ltac2:(tb__ "0|3|
S4S4S2bS1eS1eS13S26Q40M0A1A1M1S1eG1S13S41A1S40S3dRaR9A2S2aVCST;VXGL;RbRaS1fR8A1S1fR7A1A6S4S5RcR1S27G0S20RaPcM2A2A2A3S5ReR2S27G0S20RbG2A2A2A3F_;FA';G1S2eVAInv;VCST;VXGL;RdRcS3cRbRaA2R1R8R7R6R5AbS2eVAInv;VCST;VXGL;RfRdRcRaR9R8R7R6AbF_;Ftpx;F_;F_;F_;Fmd;Ftr;Ftp';Frho';Ftp0;Fr;Frho;FKc;FAr;FA;").
Proof.
  intros A Ar Kc rho r tp0 rho' tp' tr md HS HM0 HCK tpx (A' & J1 & J2 & J3 & J4 & J5 & J6 & J7 & J8 & J9 & J10).
  pose proof HS as (EG & EL & EF & EV & EKm & EKf). cbn [rho_after rw rm] in J4, J8, J10.
  exists A'. split; [exact J1|]. split; [rewrite J2; exact EL|]. split; [rewrite J3; unfold aa_frames; rewrite EF; reflexivity|].
  split; [rewrite J4, EV; reflexivity|]. split; [rewrite J5, EKm; reflexivity|]. split; [rewrite J6; exact EKf|]. split; [rewrite J7; exact EG|].
  split; [exact (mem_kept_trans A Ar A' _ _ _ HS HM0 J8)|]. split; [exact J9 | exact (HCK A' J10)].
Qed.
Lemma conv_ok : ltac2:(tb__ "0|3|
S4S4S2bS1eS1eS13S26Q40M0A1A1M1S1eG1S13S41A1S40S3dRaR9A2S2aVCST;VXGL;RbRaS1fR8A1S1fR7A1A6S4S5RcR1S27G0S20RaPcM2A2A2A3S5ReR2S27G0S20RbG2A2A2A3F_;FA';G1S2cVAInv;VCST;VXGL;RdRcS3cRbRaA2R1R8R7R6R5AbS2cVAInv;VCST;VXGL;RfRdRcRaR9R8R7R6AbF_;Ftpx;F_;F_;F_;Fmd;Ftr;Ftp';Frho';Ftp0;Fr;Frho;FKc;FAr;FA;").
Proof.
  intros A Ar Kc rho r tp0 rho' tp' tr md HS HM0 HCK tpx (A' & l1 & l2 & J1 & J2 & J3 & J4 & J5 & J6 & J7 & J8 & J9 & J10 & J11).
  pose proof HS as (EG & EL & EF & EV & EKm & EKf). cbn [rho_after rw rm] in J2, J5, J9, J11.
  exists A', l1, l2. split; [exact J1|]. split; [exact J2|]. split; [rewrite <- EL; exact J3|]. split; [rewrite J4; unfold aa_frames; rewrite EF; reflexivity|].
  split; [rewrite J5, EV; reflexivity|]. split; [rewrite J6, EKm; reflexivity|]. split; [rewrite J7; exact EKf|]. split; [rewrite J8; exact EG|].
  split; [exact (mem_kept_trans A Ar A' _ _ _ HS HM0 J9)|]. split; [exact J10 | exact (HCK A' J11)].
Qed.

Definition PF_malloc : AA -> KcA -> list (axst * jpostA) := ltac2:(tb__ "0|0|
S4S2bS33S2dVAInv;VCST;VXGL;VW;Vst;R2R1A8LKc;LA;").
Definition PF_ok : AA -> KcA -> list (axst * jpostA) := ltac2:(tb__ "0|1|
S4S2bS1bS16S49S3bA2M0S1dS49S3bS32S2dVW;Vst;A3S2cVAInv;VCST;VXGL;R2R1A5A4S19G0A1A3LKc;LA;").
Lemma posts_conv_malloc : ltac2:(tb__ "0|0|
S3eVCST;VXGL;S5eA3").
Proof.
  intros A Ar Kc rho r tp tp0 w HS HM0 HCK (L & JL & rho' & tp' & Hin & Hag & Hsm & HJL).
  unfold PF_malloc, Posts_malloc in Hin. destruct Hin as [E|[E|[]]]; injection E as <- <-.
  - exists (L_malloc_null AE_A W st), (JL_malloc_null AInv CST XGL A Kc), rho', tp'.
    split; [left; reflexivity|]. split; [exact Hag|]. split; [exact Hsm|]. exact (conv_null A Ar Kc rho r tp0 rho' tp' _ _ HS HM0 HCK tp HJL).
  - exists (L_malloc_ok AE_A W st), (JL_malloc_ok AInv CST XGL A Kc), rho', tp'.
    split; [right; left; reflexivity|]. split; [exact Hag|]. split; [exact Hsm|]. exact (conv_ok A Ar Kc rho r tp0 rho' tp' _ _ HS HM0 HCK tp HJL).
Qed.
Lemma posts_conv_ok : ltac2:(tb__ "0|0|
S3eVCST;VXGL;S5fA3").
Proof.
  intros A Ar Kc rho r tp tp0 w HS HM0 HCK (L & JL & rho' & tp' & Hin & Hag & Hsm & HJL).
  unfold PF_ok in Hin. destruct Hin as [E|[]]; injection E as <- <-.
  exists (L_malloc_ok AE_A W st), (JL_malloc_ok AInv CST XGL A Kc), rho', tp'.
  split; [left; reflexivity|]. split; [exact Hag|]. split; [exact Hsm|]. exact (conv_ok A Ar Kc rho r tp0 rho' tp' _ _ HS HM0 HCK tp HJL).
Qed.
End PCONV.

Section FINAL.
Variables CST XGL : list (Z * Z).
Variable PFam : ltac2:(tb__ "0|0|
S4S2bS13S16S49S3bA2A1F_;F_;").
Hypothesis HPF : ltac2:(tb__ "0|0|
S3eVCST;VXGL;VPFam;A3").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Variables (A : AA) (Kc : KcA) (rb : valuation) (tp0 : list word) (md0 : Model).
Variable TR : assn -> assn -> Prop.
Hypothesis KIT : TRok Kc TR.
Hypothesis HKc : Kc_ok Kc.
Variables (W : list ulink) (st : ustop) (rho : valuation).
Hypothesis HW : ltac2:(tb__ "0|0|
S0S35Vst;S34A3S0S13S31A1VW;S19S31A1A3F_;").
Hypothesis HE : ltac2:(tb__ "0|0|
S43VA;Vrb;Vtp0;Vmd0;VW;Vst;Vrho;A7").
Notation JRp := (JR A Kc rb tp0 md0).
Let nv : Z := bv_unsigned (rw rb 12%positive).
Let c : Z := cls_of nv.
Let Ar : AA := refillA A c.
Variable phF : phase.

Hypothesis HREB : ltac2:(tb__ "0|0|
S1eS13S26Q40A1A1S13S41A1S40S42VA;VKc;Vrb;Vtp0;Vmd0;VphF;R4R3R2R1AaS5dS28VAr;R5R4R2A5F_;Fmd;Ftr;Ftp;Fr;").
Hypothesis HMK : ltac2:(tb__ "0|0|
S1eS13S26Q40A1A1S13S41A1S40S42VA;VKc;Vrb;Vtp0;Vmd0;VphF;R4R3R2R1AaS2aVCST;VXGL;VA;VAr;S1fVrb;A1S1fR5A1A6F_;Fmd;Ftr;Ftp;Fr;").
Hypothesis HLEN : ltac2:(tb__ "0|0|
S0S11S58S14S11S6S4cVc;S45VA;Vnv;A2A2A1A2A1S4dVc;A1A3").

Lemma refill_fresh : ltac2:(tb__ "0|0|
S11S1S57Z1R1A2S57R1Z1eA2A2S2S0S11R2Vc;A3A1SeVA;R3A2SeVAr;R4A2F_;F_;F_;Fc';").
Proof.
  intros c' Hc' Hne Hf. unfold class_fresh, Ar, refillA in *. cbn [aa_cls].
  rewrite nth_list_upd_other; [exact Hf|]. pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. unfold cfacts in CF. cbn zeta in CF. fold nv c in CF. destruct CF as ((_ & C1 & _) & _). lia.
Qed.

Lemma JG_after : ltac2:(tb__ "0|0|
S38S1eS13S26Q40A1A1S13S41A1S40S0S15S3fR5A1S17A3S0S21S37R6P95A2S52A3S0S21S37R7P9fA2S51A3S42VA;VKc;Vrb;Vtp0;Vmd0;VphF;R7R6R5R4AaS53VW;Vst;VAr;VKc;S3cVrho;R8A2S39R8R9A2R7R6R5A9F_;F_;F_;F_;Fmd;Ftr;Ftp;Fr;Fs_x;").
Proof.
  intros s_x r tp tr md HSX H149 H159 HJ. pose proof HJ as (HFz & HGh & HK' & _ & _).
  pose proof HE as (Hag & HA & Htp & HU & HB & Hnv & Htop & Hcnt & _). destruct Hag as (Hagw & Hagl & Hagm). destruct HFz as [Fw Fl].
  assert (E12 : rw rb 12%positive = rw rho 12%positive). { rewrite <- (Hagw 12%positive) by (unfold GW; lia). reflexivity. }
  assert (RWid : forall i, (i < GW)%positive -> i <> 149%positive -> i <> 159%positive -> rw (rho_sub r s_x) i = rw (rhoM_of A rho) i).
  { intros i Hi H1 H2. cbn [rho_sub rw]. rewrite (sx_ok_id s_x i HSX Hi H1 H2). cbn [eval]. rewrite <- (Fw i) by (unfold GW in Hi; lia). symmetry. apply Hagw. exact Hi. }
  destruct HGh as (_ & _ & _ & _ & _ & _ & _ & Q227 & _ & Q229). fold nv c in Q227.
  assert (HL32 : (Z.to_nat (cls_of nv) < length (aa_cls A))%nat).
  { pose proof HA as (_ & _ & _ & HRest & _). destruct HRest as (_ & _ & Hprim & _). destruct Hprim as (L32 & _).
    pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. unfold cfacts in CF. cbn zeta in CF. fold nv in CF. destruct CF as ((_ & C1 & _) & _). rewrite L32. lia. }
  split.
  -
    split; [|split].
    + intros i Hi. destruct (Pos.eq_dec i 149) as [->|N1]; [|destruct (Pos.eq_dec i 159) as [->|N2]].
      * cbn [rho_sub rw]. rewrite H149. unfold vK. cbn [eval]. rewrite Q227.
        change (rw (rhoM_of Ar (rho_after rho r)) 149%positive) with (Z_to_bv 64 (cnt_of Ar (bv_unsigned (rw rho 12%positive)))).
        rewrite <- E12. fold nv. unfold Ar, c. rewrite (cnt_of_refill A nv HL32). fold c. rewrite HLEN. reflexivity.
      * cbn [rho_sub rw]. rewrite H159. unfold vCHX. cbn [eval]. rewrite Q229.
        change (rw (rhoM_of Ar (rho_after rho r)) 159%positive) with (Z_to_bv 64 (chk_of Ar (bv_unsigned (rw rho 12%positive)))).
        rewrite <- E12. fold nv. unfold Ar, c. rewrite (chk_of_refill A nv HL32). reflexivity.
      * rewrite (RWid i Hi N1 N2). apply rhoM_refill; assumption.
    + intros l. unfold rhoM_of. rewrite rl_rho_sets. cbn [rho_after rl rho_sub]. rewrite <- Fl. rewrite <- Hagl. unfold rhoM_of. rewrite rl_rho_sets. reflexivity.
    + intros a. unfold rhoM_of. rewrite rm_rho_sets. reflexivity.
  -
    assert (R12 : rw (rho_sub r s_x) 12%positive = rw rb 12%positive) by (rewrite (RWid 12%positive) by (unfold GW; lia); apply Hagw; unfold GW; lia).
    split; [|split; [exact HK'|split; [|split; [|split; [|split]]]]].
    + apply (AInvA_view Ar r (rho_sub r s_x) tp md (HREB r tp tr md HJ)). intros a. reflexivity.
    + unfold tp_ok in *. rewrite (RWid 24%positive) by (unfold GW; lia). rewrite (Hagw 24%positive) by (unfold GW; lia). exact Htp.
    + unfold unwind_stopJ. destruct W as [|l W']; [exact I|]. destruct st; [exact I|]. discriminate (HW eq_refl).
    + cbn [eval]. rewrite R12. fold nv. exact HB.
    + cbn [eval]. rewrite R12. fold nv. lia.
    + unfold top_high in *. rewrite (RWid 10%positive) by (unfold GW; lia). rewrite (RWid V_DEPTH) by (unfold GW, V_DEPTH; lia).
      rewrite (Hagw 10%positive) by (unfold GW; lia). rewrite (Hagw V_DEPTH) by (unfold GW, V_DEPTH; lia). exact Htop.
Qed.

Lemma posts_after : ltac2:(tb__ "0|0|
S1eS13S26Q40A1A1S4fS2aVCST;VXGL;VA;VAr;S1fVrho;A1S1fR3A1A6S3aS28S36S3cVrho;R4A2R3VPFam;VAr;VKc;A2R2A6S3aS28S36Vrho;Vtp0;VPFam;VA;VKc;A2R3A6F_;F_;Fw;Ftp;Fr;").
Proof.
  intros r tp w HM0 H.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. unfold cfacts in CF. cbn zeta in CF. fold nv c in CF. destruct CF as ((Hnv & C1 & _) & _).
  pose proof HE as (HagE & _). destruct HagE as (Hagw & _ & _).
  assert (E12 : rw rb 12%positive = rw rho 12%positive). { rewrite <- (Hagw 12%positive) by (unfold GW; lia). reflexivity. }
  assert (Ecls : ClassID (needed (bv_unsigned (rw rho 12%positive))) = c) by (rewrite <- E12; fold nv; exact (proj1 (cls_needed nv Hnv))).
  apply (HPF A Ar Kc rho r tp tp0 w); [repeat split; reflexivity | exact HM0 | | exact H].
  intros A' HCK c' Hc' Hn Hf. apply (HCK c' Hc' Hn). apply refill_fresh; [exact Hc'| |exact Hf].
  destruct Hn as [Hn|Hn]; [rewrite <- E12 in Hn; fold nv in Hn; lia | rewrite Ecls in Hn; exact Hn].
Qed.

Variables (E3P EZ : axst) (s_x : wsub).
Hypothesis ENT_x : ltac2:(tb__ "0|0|
S0S15S4aVEZ;VE3P;Vs_x;A3S17A3").
Hypothesis SX_x : sx_okb s_x = true.
Hypothesis S149_x : ltac2:(tb__ "0|0|
S0S21S37Vs_x;P95A2S52A3").
Hypothesis S159_x : ltac2:(tb__ "0|0|
S0S21S37Vs_x;P9fA2S51A3").

Hypothesis HPOP : ltac2:(tb__ "0|0|
S1eS13S26Q40A1A1S1eVTR;S50S28S53VW;Vst;VAr;VKc;R3A5VE3P;R1R2A5S3aS28S36R3R2VPFam;VAr;VKc;A2A5A2FrX;Ftp';Frho';").

Theorem refill_back : ltac2:(tb__ "0|0|
S1eS13S26Q40A1A1VTR;S50S28S42VA;VKc;Vrb;Vtp0;Vmd0;VphF;A6VEZ;R2R1A5S3aS28S36Vrho;Vtp0;VPFam;VA;VKc;A2A5A2Ftp;Fr;").
Proof.
  intros r tp.
  assert (Erm : rm rb = rm rho).
  { destruct HE as ((_ & _ & Hm) & _). apply functional_extensionality. intros a. rewrite <- (Hm a). unfold rhoM_of. rewrite rm_rho_sets. reflexivity. }
  apply (tr_pure Kc TR KIT (mem_keptA CST XGL A Ar (rm rho) (rm r))).
  { intros w [_ HJ]. rewrite <- Erm. exact (HMK r tp _ _ HJ). }
  intros HM0.
  apply (tr_post Kc TR KIT _ _ _ (fun w Hw => posts_after r tp w HM0 Hw)).
  apply (tr_pre Kc TR KIT (SPA segs (JG W st Ar Kc (rho_after rho r)) E3P (rho_sub r s_x) tp)); [|apply HPOP].
  intros w Hw. apply (SPA_entails_J (JRp phF) (JG W st Ar Kc (rho_after rho r)) EZ E3P s_x r tp w ENT_x); [|exact Hw].
  intros HJ. exact (JG_after s_x r tp _ _ SX_x S149_x S159_x HJ).
Qed.
End FINAL.
End SpineMallocR5.

(* [comment removed for export] *)
Module SecLinks.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Logic"; "and"; "eq"; "not"; "False"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rm"; "rl"; "rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "div"; "pow"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "@Corelib.Init.Datatypes"; "None"; "list"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "Sh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "ageom"; "AA"; "aa_depot"; "aa_geom"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineMallocSec4"; "slink4"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jn.DepotCallS"; "dlink"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "mem_keptA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.SecOKInv"; "pendS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dfp_static"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "secmapsize"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec2"; "IMG_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3"; "slink"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundR SymSummary SymFrame Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import BackingAlgebra LedgerA Virt StepA SoundA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Inv.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildSM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SMGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocSec2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jn.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.RebuildN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.SecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.SecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.SegD_cost OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jb.InvEnsure OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.LiveGeom OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineMallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.InvD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jn.DepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.RebuildS.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section Links.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTS : ltac2:(tb__ "0|0|
S0SaVCST;R1A2SaS23R2A2S5F_;F_;Fa;").
Hypothesis HCSTD : ltac2:(tb__ "0|0|
S0SaVCST;R1A2S4S21R2A1A1F_;Fa;").

Lemma slink4_refl : ltac2:(tb__ "0|2|
S16S0S0S6S0S2SbS15R4A1M0R1A2ScR1SdG0SeR3Z8A2A2A2A2S4S3S14S10Q8A1M1A1S7R3S11Q40R2A2A2S12G1A1A3A1F_;Fz;S1aR5R4R3R2R2A5F_;Fr;FL;Fua;FG;").
Proof. intros G ua L r RD. split; [reflexivity|]. split; [reflexivity|]. split; [intros a; left; reflexivity | exact RD]. Qed.

Theorem links_kept : ltac2:(tb__ "0|4|
S17S6S13S10Q40M0A1M1A1S1bS0S0S6S6S6S6S1fS1cRaR9R8R7A5S2SbZfc01R7A2ScR7SfZ2Z27A2A2A2S19RcA1S16S22R9A1S0S20ReR9R1RbA4S24RaR2R9R8A4S1aR4RbR3R9R8A5S1dS18R11A1R9R8A3S2S1eVCST;VXGL;R12R12S7RcA1S7R9A1A6S2S0S2SbS15ReA1M2R1A2ScR1SdG2SeR6Z8A2A2A2A2S4S3S14S10Q8A1M3A1S7RbS11G0R2A2A2S12G3A1A3A1F_;Fz;S2S1S3G1S9RaR1A2S9RdR1A2A3Fi;S1S3S13G3A1S8RaR1A2S8RdR1A2A3Fl;A2A2A2F_;F_;F_;F_;TL;TG;F_;F_;Frho3;Frho2;Frho1;Frho0;Fua;Fnv;Fmd;Ftp;Fr;FAs;").
Proof.
  intros A r tp md nv ua rho0 rho1 rho2 rho3 HA Hnv. cbn zeta. intros HPD (W1 & L1 & M1 & D1) (W2 & L2 & M2 & D2) (W3 & L3 & M3).
  pose proof HA as (HG & HR & HF & HRest & HM & HI3 & HB).
  destruct HRest as (Hsep & Hlive & HPR & HSR & HQR & HDW & HIA & HTH & HMI).
  set (G := aa_geom A) in *. set (T := ag_thread G) in *. set (L := secmapsize nv) in *.
  pose proof (geom_numsS _ HG) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & ACV). fold T in G4, G5, G10, G13, G14.
  pose proof (geom_bands _ HG) as (FB & TB & CB & DB & TI & CI & DI). fold G T in TB, TI. fold G in FB, CB, DB, CI, DI.
  unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END, IMG_LO, IMG_HI in FB, TB, CB, DB, TI, CI, DI. rewrite FS_total_val in FB.
  destruct HPD as (PM & PAL & PL0 & PDI & ST & SC & SD & SF & SS & SP & SX & SDB). fold G L in PM, PL0, PDI, ST, SC, SD, SF, SS, SP, SX, SDB. fold T in ST.
  pose proof (secmapsize_bounds nv ltac:(clear -Hnv; lia)) as [SMB SMM]. fold L in SMB, SMM. unfold PG in SMM, PAL.
  pose proof (dyn_in_big _ _ _ PDI ltac:(clear -SMB; lia)) as UI. destruct PDI as (_ & _ & PDT & _ & PDB).
  pose proof (pab_facts _ A HSR) as (P1 & P2 & P3 & P4 & P5). fold G in P1, P2, P3.
  assert (U8 : ua mod 8 = 0).
  { pose proof (Z.div_mod ua 4096 ltac:(clear; lia)) as X. rewrite PAL, Z.add_0_r in X. rewrite X. replace (4096 * (ua / 4096)) with ((512 * (ua / 4096)) * 8) by (clear; lia). apply Z_mod_mult. }
  assert (L8 : L mod 8 = 0).
  { pose proof (Z.div_mod L 4096 ltac:(clear; lia)) as X. rewrite SMM, Z.add_0_r in X. rewrite X. replace (4096 * (L / 4096)) with ((512 * (L / 4096)) * 8) by (clear; lia). apply Z_mod_mult. }
  assert (UT : ua + L <= 140737479966720) by (clear -PDT ACV; lia).
  unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in PDB.
  pose proof (live_foot_new ua L U8 L8 PL0 UI UT ltac:(unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END; exact PDB) A _ HG Hsep HI3 HPR HSR SS SX) as LFN.
  unfold sepZ in SF, ST. cbn [fst snd] in SF, ST. rewrite FS_total_val in SF.
  assert (ESHL : Sh (ua + L) = Sh ua + L / 8).
  { unfold Sh. pose proof (Z.div_mod L 8 ltac:(clear; lia)) as DL. rewrite L8, Z.add_0_r in DL. rewrite DL at 1. rewrite Z.mul_comm, Z.div_add by (clear; lia). clear. lia. }

  assert (RUNB : forall z, Sh ua <= z < Sh ua + L / 8 -> 2147446784 <= z < 17594333495296).
  { intros z Hz. rewrite <- ESHL in Hz.
    pose proof (sh_run_band2 ua (ua + L) z ltac:(unfold IMG_HI in UI; clear -UI; lia) ltac:(clear -UT PL0; lia) Hz) as BY.
    unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in BY. exact BY. }
  idtac "lk:0".

  assert (NOC : forall a, client_addrA CST A a -> ~ rtint G a /\ ~ (ua <= a < ua + L)).
  { intros a Hcl.
    destruct (client_addr_cases CST A a _ HF Hcl) as [S|[Lv|[FR|[C|FL]]]].
    - fold G in S. split; [|clear -S PDT; lia].
      intros [X|X]; [unfold SEC_INST in X; clear -X S ACV; lia | clear -X S P2; lia].
    - destruct Lv as (b & n & Hbn & Hx). destruct (Hsep b n Hbn) as (S1 & S2 & _). unfold IMG_HI in S2.
      pose proof (rz_bound n) as RZ.
      pose proof (LFN b n a Hbn ltac:(left; clear -Hx RZ; lia)) as NZ.
      pose proof (live_foot _ A HG Hsep HI3 HPR HSR b n a Hbn ltac:(left; clear -Hx RZ; lia)) as (X1 & X2 & _).
      pose proof (live_foot_pab _ A HG Hsep HI3 HPR HSR b n a Hbn ltac:(left; clear -Hx RZ; lia)) as X3. fold G T in X2, X3.
      split; [|intros X; apply NZ; left; exact X].
      intros [X|X]; [unfold SEC_INST, IMG_HI in *; clear -X X1; lia | exact (X3 X)].
    - destruct FR as (c & p & Hcp & Hp & _ & Hx). pose proof (fs_geom_nums G c p HG Hcp Hp) as M. cbn zeta in M.
      rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M. unfold IMG_HI in M. fold G in Hx.
      destruct HI3 as ((_ & _ & _ & _ & _ & PF & _) & _). fold G in PF. rewrite FS_total_val in PF. unfold kPtrArrayReserve in *.
      split; [|clear -Hx M SF; lia].
      intros [X|X]; [unfold SEC_INST in X; clear -X Hx M; lia | unfold kPtrArrayReserve in X; clear -X Hx M PF; lia].
    - destruct (HCST _ C) as [X0 _]. unfold IMG_LO, IMG_HI in X0.
      split; [|unfold IMG_HI in UI; clear -X0 UI; lia].
      intros [X|X].
      + apply (HCSTS a C). unfold IMG_S, in_rangesZ. unfold SEC_INST in *.
        exists 0xeaa98, (0xead04 - 0xeaa98). split; [left; reflexivity | clear -X; lia].
      + unfold IMG_HI in P1. clear -X X0 P1. lia.
    - destruct FL as (c & p & Hcp & Hp & _ & Ea). pose proof (fs_geom_nums G c p HG Hcp Hp) as M. cbn zeta in M.
      rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M. fold G in Ea. unfold fs_flags in M, Ea. rewrite FS_kFlagsOffset_val in M, Ea. unfold IMG_HI in M.
      destruct HI3 as ((_ & _ & _ & _ & _ & PF & _) & _). fold G in PF. rewrite FS_total_val in PF. unfold kPtrArrayReserve in *.
      split; [|clear -M Ea SF; lia].
      intros [X|X]; [unfold SEC_INST in X; clear -X M Ea; lia | unfold kPtrArrayReserve in X; clear -X M Ea PF; lia]. }
  idtac "lk:1".

  destruct (AInvA_X A r tp md HA) as (HXd & _ & _).
  assert (NOD : forall a, KEEPD CST XGL A a -> ~ DFP (aa_depot A) a).
  { intros a HK. exact (keep_not_DFP UStopLe CST XGL HCST HXGL HCSTD A r tp md a HXd HK). }
  assert (BAND : forall a, 2147446784 <= a < 17594333495296 -> ~ DFP (aa_depot A) a).
  { intros a HB' HD.
    assert (HSEC : forall i ch, nth_error (aa_sec A) i = Some ch -> dyn_in (topG (aa_geom A)) (sc_map_beg ch) (sc_map_size ch)).
    { intros i ch Hi. destruct HSR as [X1 _]. destruct (X1 i ch Hi) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & D10 & _). exact D10. }
    assert (HPAB : dyn_ok (topG (aa_geom A)) (ag_pab (aa_geom A)) kPtrArrayReserve) by (destruct HSR as (_ & _ & _ & _ & X4' & _); exact X4').
    pose proof (zones_not_DFPw A a HG HI3 HSEC HPAB) as ZN. cbn zeta in ZN.
    destruct (DFP_split _ _ HD) as [Hs|Hws]; [pose proof (dstat_range a Hs) as DR; unfold MAP1, MAP1N, STORE in DR; clear -HB' DR; lia | ].
    apply ZN; [do 8 right; left; unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END; exact HB' | exact Hws]. }

  assert (BRT : forall a, 2147446784 <= a < 17594333495296 -> ~ rtint G a).
  { intros a HB' [X|X]; [unfold SEC_INST in X; clear -X HB'; lia |].
    unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in P3. clear -X HB' P3. lia. }
  idtac "lk:2".

  assert (NOS : forall a, client_shadowA CST XGL A a -> 2147446784 <= a < 17594333495296 /\ ~ (Sh ua <= a < Sh ua + L / 8)).
  { intros a C1. pose proof (client_shadow_bounds CST XGL HCST HXGL A a _ HG HF Hsep C1) as B0. unfold SHADOW_OFF, HIGH_SHADOW_END in B0.
    split; [clear -B0; lia|]. intros X.
    assert (XIN : forall x, a = Sh x -> 0 <= x -> ua <= x < ua + L).
    { intros x -> Hx0. unfold Sh in X. pose proof (Z.div_mod L 8 ltac:(clear; lia)) as DL. rewrite L8, Z.add_0_r in DL.
      pose proof (Z.div_mod ua 8 ltac:(clear; lia)) as DU. rewrite U8, Z.add_0_r in DU.
      pose proof (Z.div_mod x 8 ltac:(clear; lia)) as DX. pose proof (Z.mod_pos_bound x 8 ltac:(clear; lia)) as MX. clear -X DL DU DX MX. lia. }
    destruct C1 as [(y & Cy & Ey)|(y & Gy & Ey)].
    - destruct (client_addr_bounds CST HCST A y _ HG HF Hsep Cy) as [By _]. pose proof (XIN y Ey ltac:(clear -By; lia)) as YIN.
      exact (proj2 (NOC y Cy) YIN).
    - destruct (HXGL y Gy) as [Y1 Y2]. pose proof (XIN y Ey ltac:(clear -Y1; unfold IMG_LO in *; lia)) as YIN. clear -YIN Y2 UI. lia. }
  idtac "lk:3".

  assert (DEFB : forall z, 2147446784 <= z < 17594333495296 -> rm rho0 (Z_to_bv 64 z) <> None -> rm rho3 (Z_to_bv 64 z) <> None).
  { intros z Hz Hd.
    assert (EZ : bv_unsigned (Z_to_bv 64 z) = z) by (rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with 18446744073709551616; apply Z.mod_small; clear -Hz; lia).
    assert (H1 : rm rho1 (Z_to_bv 64 z) <> None).
    { destruct (M1 (Z_to_bv 64 z)) as [E|[(N & _)|(_ & N)]]; [rewrite E; exact Hd | exact (False_ind _ (Hd N)) | exact N]. }
    assert (H2 : rm rho2 (Z_to_bv 64 z) <> None).
    { destruct (M2 (Z_to_bv 64 z)) as [E|[(N & _)|[(_ & N)|N]]]; [rewrite E; exact H1 | exact (False_ind _ (H1 N)) | exact N |].
      rewrite EZ in N. exact (False_ind _ (BRT z Hz N)). }
    rewrite (M3 (Z_to_bv 64 z)); [exact H2|]. rewrite EZ. exact (BAND z Hz). }
  idtac "lk:4".
  split; [|split; [|split]].
  - split.
    + intros a Ba Hcl.
      assert (EZ : bv_unsigned (Z_to_bv 64 a) = a) by (rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with 18446744073709551616; apply Z.mod_small; clear -Ba; lia).
      assert (KD : KEEPD CST XGL A a) by (destruct Hcl as [(C1 & _)|(C1 & _)]; [left; exact C1 | right; exact C1]).
      rewrite (M3 (Z_to_bv 64 a)) by (rewrite EZ; exact (NOD a KD)).
      destruct Hcl as [(C1 & _ & NE)|(C1 & _ & Hd)].
      * destruct (NOC a C1) as (N1 & N2).
        destruct (client_addr_bounds CST HCST A a _ HG HF Hsep C1) as [_ NB].
        assert (NRUN : ~ (Sh ua <= a < Sh ua + L / 8)) by (intros X; pose proof (RUNB a X) as Y; clear -Y NB; lia).
        assert (E1 : rm rho1 (Z_to_bv 64 a) = rm rho0 (Z_to_bv 64 a)).
        { destruct (M1 (Z_to_bv 64 a)) as [E|[(_ & _ & N)|(N & _)]]; [exact E | | ]; rewrite EZ in N; exfalso;
            [unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in N; clear -N NB; lia | exact (NRUN N)]. }
        rewrite <- E1.
        destruct (M2 (Z_to_bv 64 a)) as [E|[(_ & _ & N)|[(N & _)|N]]]; [exact E | | | ]; rewrite EZ in N; exfalso;
          [unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in N; clear -N NB; lia | exact (NRUN N) | exact (N1 N)].
      * destruct (NOS a C1) as (B0 & NRUN).
        assert (E1 : rm rho1 (Z_to_bv 64 a) = rm rho0 (Z_to_bv 64 a)).
        { destruct (M1 (Z_to_bv 64 a)) as [E|[(N & _)|(N & _)]]; [exact E | exact (False_ind _ (Hd N)) | rewrite EZ in N; exact (False_ind _ (NRUN N))]. }
        rewrite <- E1. rewrite <- E1 in Hd.
        destruct (M2 (Z_to_bv 64 a)) as [E|[(N & _)|[(N & _)|N]]]; [exact E | exact (False_ind _ (Hd N)) | rewrite EZ in N; exact (False_ind _ (NRUN N)) |].
        rewrite EZ in N. exact (False_ind _ (BRT a B0 N)).
    + intros x j Hx Hj Hdef.
      assert (Bx : SHADOW_OFF <= Sh x < HIGH_SHADOW_END).
      { destruct Hx as [[C1 C2]|GX].
        - destruct (client_addr_bounds CST HCST A x _ HG HF Hsep C1) as [B _]. unfold Sh, SHADOW_OFF, HIGH_SHADOW_END. clear -B. lia.
        - destruct (HXGL x GX) as [X0 X1]. unfold IMG_LO, IMG_HI, Sh, SHADOW_OFF, HIGH_SHADOW_END in *. clear -X0 X1. lia. }
      unfold SHADOW_OFF, HIGH_SHADOW_END in Bx.
      destruct (word_byte_range (Sh x) j ltac:(clear -Bx; lia) Hj) as (W1' & W2' & W3').
      unfold word_byte in *. apply DEFB; [|exact Hdef]. clear -W3' Bx Hj. lia.
  - intros z Hz. pose proof (RUNB z Hz) as Bz.
    assert (EZ : bv_unsigned (Z_to_bv 64 z) = z) by (rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with 18446744073709551616; apply Z.mod_small; clear -Bz; lia).
    rewrite (M3 (Z_to_bv 64 z)); [exact (D2 z Hz)|]. rewrite EZ. exact (BAND z Bz).
  - intros i. rewrite W3, W2. apply W1.
  - intros l. rewrite L3, L2. apply L1.
Qed.
End Links.
End SecLinks.

(* [comment removed for export] *)
Module SpineMallocSec5.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_setS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@Corelib.Init.Datatypes"; "list"; "bool"; "cons"; "nil"; "true"; "prod"; "Some"; "option"; "pair"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sprop"; "ss_next"; "sv"; "holds"; "swf"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertMallocSU"; "F_g4"; "DPENT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "@stdpp.bitvector.definitions"; "bv"; "@Corelib.Lists.ListDef"; "Forall"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.CertMallocSS"; "nxS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3"; "JGs"; "@Stdlib.PArith.BinPos.Pos"; "leb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA EntailA CFGA GlueA GlueA2 SummaryA SysCallA MmapA MmapFixedA LedgerA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts Placement StartLib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import StartDefsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildSM SMGlue InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNullInit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require io.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SpineMallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.RebuildN.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import MmapSymA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require id.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocSec SpineMallocSec2 SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jl.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.CertMallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.id.CertMallocSN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.SegD_cost OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.LedgerLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.InvD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.DepotK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.SecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SecReveal OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.InvReveal OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import EnsureMapA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.SecBump.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import SecLog2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jp.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jb.InvEnsure OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertMallocSU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineMallocSec4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section SEC5.
Variable nW : nat. Variable st : ustop. Variable tmax : Z. Variable hi : bool.
Let W : list ulink := Wcan nW.
Let segs : list Segment := segsA.
Variable nx : positive.
Hypothesis Hnx : ltac2:(tb__ "0|0|
S0S15S21VW;Vst;Vtmax;A3Vnx;A3").
Hypothesis NXG : ltac2:(tb__ "0|0|
S0S6S25S22Vnx;A2S9A3").
Let GS : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3.GS nx.
Let JG (BX : AA -> AA) : AA -> KcA -> valuation -> word -> jpredA := ltac2:(tb__ "0|0|
S24VnW;Vst;Vnx;VBX;A4").

Lemma F_g4_hold : ltac2:(tb__ "0|1|
S4S4F_;S4S19SeS1aQ40A1M0SeS5G0A1S5S1dA1S1cVJG;R9R8R7R6R5R4R3R2R1A9S1bSfS12R5A1S17Vnx;A1A3F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a r tp tr md HJ.
  pose proof (JGs_rigidS nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (E12 & Enx & ENS & _).
  destruct HJ as (_ & _ & _ & HP & _ & _ & _ & Hnv & _). cbn zeta in Hnv.
  set (nv := bv_unsigned (rw rho 12%positive)) in *.
  destruct HP as (_ & _ & _ & (D1 & D2 & D3 & _) & _). pose proof (topG_range (aa_geom A)) as TG.
  pose proof (secmapsize_bounds nv ltac:(lia)) as (MB1 & MB2).
  assert (NSV : secneeded nv = (nv + 8 - 1) / 8 * 8 + 4096) by reflexivity.
  pose proof (Z.div_mod (nv + 8 - 1) 8 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound (nv + 8 - 1) 8 ltac:(lia)) as MBd.
  pose proof (urange a) as Ra.
  unfold F_g4. apply Forall_cons; [|apply Forall_nil]. cbn [holds eval branch_taken]. intros H. unfold bv_ltu in H. apply Z.ltb_lt in H.
  rewrite !add_val, ENS, Enx, E12, !u64_lit in H by lia. fold nv in H.
  rewrite (Z.mod_small (bv_unsigned a + 4096)) in H by lia. rewrite (Z.mod_small (bv_unsigned a + 6144)) in H by lia.
  rewrite !Z.mod_small in H by lia. lia.
Qed.

Section G41.
Variables (T4 U4 X5 : axst).
Hypothesis WU4 : ltac2:(tb__ "0|0|
S0S6S13S1VU4;A1A1S9A3").
Hypothesis DU4 : ltac2:(tb__ "0|4|
S0ScSaS5SaS11S11A2M0A1M1S5SfA1M2A2M3A1S1fS1VT4;A1S1VU4;A1A2SbG3SdG1G2S8G0A1S17Vnx;A1A4A2A3").
Hypothesis NXU4 : ltac2:(tb__ "0|0|
S0S15S10S1VU4;A1A1S10S1VT4;A1A1A3").
Hypothesis HU4 : ltac2:(tb__ "0|0|
S0S2S3VT4;S1VU4;A1A2VU4;A3").
Hypothesis Cert5 : ltac2:(tb__ "0|1|
S0S6S20S23Ufa0S7S14S18S8S14A1A3VGS;S7S2VU4;S8S2A1M0A3S7S2VX5;G0A3A6S9A3").

Lemma RSU4 : ltac2:(tb__ "0|1|
S4S4F_;S4S19SeS1aQ40A1M0SeS5G0A1S1eS16Vsegs;VJG;R8R7R6R5R4A5VT4;R3R2R1A6S16Vsegs;VJG;R9R8R7R6R5A5VU4;R4R3R2A6F_;Fw;Ftp;FrhoX;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a rhoX tp w Hw. destruct w as [tr [ms md]]. rewrite <- HU4.
  eapply SPA_restate; [exact WU4 | exact DU4 | exact NXU4 | constructor | | exact Hw].
  exact (F_g4_hold BX A Kc rho a rhoX tp tr md (proj2 Hw)).
Qed.
End G41.
End SEC5.
End SpineMallocSec5.

(* [comment removed for export] *)
Module SpineMallocSecE2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "entailsA"; "ax_setS"; "ax_X"; "ax_base"; "shadow_addr"; "@Corelib.Init.Datatypes"; "cons"; "bool"; "true"; "nil"; "list"; "app"; "prod"; "pair"; "option"; "length"; "None"; "Some"; "false"; "fst"; "snd"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sv"; "sprop"; "ss_next"; "sobj"; "SLit"; "reg_sv"; "SVar"; "rw"; "ss_facts"; "eval"; "ss_objs"; "SPBranch"; "rm"; "swf"; "sprop_below"; "SPNot"; "obj_range"; "ranges_disjoint"; "ro_addr"; "ss_pc"; "sv_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_ecfgA"; "check_cfgA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "stableA"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_sec"; "aa_geom"; "sec_chunk"; "aa_ptr_committed"; "budget_bound"; "ageom"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "ulink"; "KcA"; "UStopLeOrPc"; "ustop"; "Kc_ok"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "@Stdlib.ZArith.BinInt.Z"; "add"; "lt"; "le"; "of_nat"; "pow"; "div"; "ge"; "modulo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "wsub_get"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocST"; "genL"; "Bw"; "F_l2"; "F_g3"; "O_1"; "O_2"; "x11e3"; "O_blk"; "O_w"; "a0e3"; "carveS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "secmapsize"; "stopJ_stable"; "@Stdlib.Lists.List"; "incl"; "In"; "forallb"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3"; "skel"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_EQ"; "instr"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.CertMallocSS"; "V_NCH"; "V_NRES"; "nxS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "Sh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineMallocSec4"; "slink4"; "JGo"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "alloc_top"; "m_vmmaps"; "map_contains"; "region_free"; "vm_forget_range"; "vm_maps"; "vm_reserved"; "with_vmmaps"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3"; "SKEL0"; "JGs"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap"; "mmap_fixed_rw_next"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "S_after"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "instr_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.BackingAlgebra"; "overlap_sum"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "smatch_pendingA";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "headroom"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA EntailA CFGA GlueA GlueA2 SummaryA SysCallA MmapA MmapFixedA LedgerA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts Placement StartLib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import StartDefsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildSM SMGlue InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNullInit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require io.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SpineMallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.RebuildN.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import MmapSymA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require id.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocSec SpineMallocSec2 SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jl.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.CertMallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.id.CertMallocSN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.SegD_cost OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.LedgerLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.InvD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.DepotK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.SecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SecReveal OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.InvReveal OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import EnsureMapA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.SecBump.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import SecLog2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jm.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jb.InvEnsure OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineMallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jm.SpineMallocSecE1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac rr X := intros; eapply X; revgoals; [> eassumption ..].

Section SEC4E.
Variable nW : nat. Variable st : ustop. Variable tmax : Z. Variable hi : bool.
Let W : list ulink := Wcan nW.
Let segs : list Segment := segsA.
Variable nx : positive.
Hypothesis Hnx : ltac2:(tb__ "0|0|
S0S1bS73VW;Vst;Vtmax;A3Vnx;A3").
Hypothesis NXG : ltac2:(tb__ "0|0|
S0ScS57S8bVnx;A2SdA3").
Variable AX : AA -> AA.
Hypothesis AXg : ltac2:(tb__ "0|0|
S3dS0S43S3fVAX;R1A1A1S3fR1A1A3FX;").
Hypothesis AXs : ltac2:(tb__ "0|0|
S3dS0SfS40A1S3eVAX;R1A1A1S3eR1A1A3FX;").
Hypothesis AXp : ltac2:(tb__ "0|0|
S3dS0S1aS41VAX;R1A1A1S41R1A1A3FX;").
Hypothesis AXb : ltac2:(tb__ "0|0|
S3dS0S1aS42VAX;R1A1A1S42R1A1A3FX;").
Let GS : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3.GS nx.
Let JG (BX : AA -> AA) : AA -> KcA -> valuation -> word -> jpredA := ltac2:(tb__ "0|0|
S84VnW;Vst;Vnx;VBX;A4").
Let slink : Z -> Z -> valuation -> valuation -> Prop := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3.slink.
Let AXP : AA -> AA := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineMallocSec4.AXP AX.
Let JGo : ltac2:(tb__ "0|0|
S3dS45S1cS3bQ40A1S38Fa;Frho;FKc;FA;") := ltac2:(tb__ "0|0|
S76VnW;Vst;Vnx;VAX;A4").

Lemma ecfg_2 : ltac2:(tb__ "0|3|
SfS1aA1S5S5S5S38S55OF_;SfS3bQ40A1A1S1cS39Vsegs;VGS;R4A3S0ScS57VGS;S1fS4R8A1A1A2SdA3S0ScS34S56Ufa0RaVGS;SbS32S33R9Z1S21Z0M0A1M1A3SeS32A1M2A3SbS32S33R8G0G1A3SbS32S33R7G0G1A3G2A3A3A6SdA3S1cS54Vsegs;S37Vsegs;R8RaR1R6A5R7A3Frho';S1cS54Vsegs;S37Vsegs;R9RaR1R7A5R8A3Frho';S54Vsegs;S37Vsegs;R9RcR6R7A5R8A3F_;F_;F_;F_;F_;Frho;Ftp;FQ;FJx;FE2;FE1;FC;Fcutpcs;").
Proof.
  intros cutpcs C E1 E2 Jx Q tp rho HST NXC HC HE1 HE2.
  apply (ecfg_cutG 4000%nat cutpcs GS [mkVNA C 1 (SLit 0)] [mkVNA E1 0 (SLit 0); mkVNA E2 0 (SLit 0)] Jx Q tp C rho HST).
  - intros n Hn. destruct Hn as [<-|[]]. cbn [vna_state]. apply Pos.leb_le. exact NXC.
  - exact HC.
  - intros E' rho' HinE. destruct HinE as [<-|[<-|[]]]; cbn [vna_state].
    + eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | exact (HE1 rho')].
    + eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | exact (HE2 rho')].
  - left. reflexivity.
Qed.

Section G3E.

Variables (D2 U2 X3a X3b CS3 G3 X3a3 L3a L3b CO3b T4a T4b Y4a0 Y4a1 Y4b0 Y4b1 : axst).
Variables (sLa sLb s4a0 s4a1 s4b0 s4b1 : wsub).

Hypothesis WU2 : ltac2:(tb__ "0|0|
S0ScS2aS4VU2;A1A1SdA3").
Hypothesis DU2 : ltac2:(tb__ "0|4|
S0S13S11SfS11S1dS1dA2M0A1M1SfS1eA1M2A2M3A1S82S4VD2;A1S4VU2;A1A2S16G3S12G1G2SeG0A1S5dA4A2A3").
Hypothesis NXU2 : ltac2:(tb__ "0|0|
S0S1bS1fS4VU2;A1A1S1fS4VD2;A1A1A3").
Hypothesis HU2 : ltac2:(tb__ "0|0|
S0S5S7VD2;S4VU2;A1A2VU2;A3").

Hypothesis Cert3 : ltac2:(tb__ "0|1|
S0ScS35S56Ufa0SbS1aZ706a0SbS1aZ410f0SeS1aA1A3A3VGS;SbS5VU2;SeS5A1M0A3SbS5VX3a;SbS5VX3b;G0A3A3A6SdA3").

Hypothesis WC3 : ltac2:(tb__ "0|0|
S0ScS2aS4VCS3;A1A1SdA3").
Hypothesis DC3 : ltac2:(tb__ "0|4|
S0S13S11SfS11S1dS1dA2M0A1M1SfS1eA1M2A2M3A1S82S4VX3a;A1S4VCS3;A1A2S16G3S12G1G2SbG0S12S1dS1dS63S5bA4SeG0A1A3SeS1eA1A4A2A3").
Hypothesis NXC3 : ltac2:(tb__ "0|0|
S0S1bS1fS4VCS3;A1A1S1fS4VX3a;A1A1A3").
Hypothesis HC3 : ltac2:(tb__ "0|0|
S0S5S7VX3a;S4VCS3;A1A2VCS3;A3").
Hypothesis FX3a : ltac2:(tb__ "0|0|
S67S1eS10S1eSbS1eS28S6eS23S71A1S23S72A1A3SeS1eA1A3S5dA3S25S4VX3a;A1A1A3").
Hypothesis IC3 : ltac2:(tb__ "0|0|
S0S13S6fA1S87S56S30S4VCS3;A1A1A2S16S6fS70A2A3").
Hypothesis R17 : ltac2:(tb__ "0|0|
S0S1dS22S4VCS3;A1Z11A2S21ZdeA1A3").
Hypothesis R10 : ltac2:(tb__ "0|0|
S0S1dS22S4VCS3;A1ZaA2S5bA3").
Hypothesis BBw : ltac2:(tb__ "0|0|
S0ScS31S1fS4VCS3;A1A1S5bA2SdA3").
Hypothesis R11 : ltac2:(tb__ "0|0|
S0S1dS22S4VCS3;A1ZbA2S21Z20000A1A3").
Hypothesis R12 : ltac2:(tb__ "0|0|
S0S1dS22S4VCS3;A1ZcA2S21Z3A1A3").
Hypothesis R13 : ltac2:(tb__ "0|0|
S0S1dS22S4VCS3;A1ZdA2S21Z32A1A3").
Hypothesis R14 : ltac2:(tb__ "0|0|
S0S1dS22S4VCS3;A1ZeA2S21ZffffffffffffffffA1A3").
Hypothesis R15 : ltac2:(tb__ "0|0|
S0S1dS22S4VCS3;A1ZfA2S21Z0A1A3").
Hypothesis XC3 : ax_X CS3 = [].
Hypothesis SK3 : ltac2:(tb__ "0|2|
S0SfS11S11S1dS1dA2S1dA2M0A1S6aS20G0S6bS27S4VCS3;A1A1A4S6aS20G0S6bS10S20SbS20S5fVnx;A1SbS20S5eVnx;A1SeS20A1M1A3A3S10S20S83VnW;Vnx;A2G1A3A3A4A3").
Hypothesis FC3 : ltac2:(tb__ "0|0|
S67S1eS10S1eS4bVW;Vst;A2S4aS49A1A3S25S4VCS3;A1A1A3").
Hypothesis FCS3 : ltac2:(tb__ "0|0|
S67S1eS10S1eSbS1eS28S6eS23S71A1S23S72A1A3SeS1eA1A3S5dA3S25S4VCS3;A1A1A3").
Hypothesis NXS3 : ltac2:(tb__ "0|0|
S0ScS57VGS;S1fS4VCS3;A1A1A2SdA3").

Hypothesis HG3 : ltac2:(tb__ "0|1|
S0S5S7VCS3;S86S4VCS3;A1M0S5bS10S20S27G0A1SbS20S61SeS20A1A3A3S1fG0A1A4A2VG3;A3").

Hypothesis Cert3a : ltac2:(tb__ "0|1|
S0ScS35S56Ufa0SbS1aZ410f0SeS1aA1A3VGS;SbS5VG3;SeS5A1M0A3SbS5VX3a3;G0A3A6SdA3").

Hypothesis ELa : ltac2:(tb__ "0|0|
S0ScS6VX3a3;S5aVX3a3;A1VsLa;A3SdA3").
Hypothesis IDa : ltac2:(tb__ "0|0|
S0ScS58VsLa;VGS;A2SdA3").
Hypothesis GLa : ltac2:(tb__ "0|0|
S0S1dS59VsLa;S1fS4VX3a3;A1A1A2S60A3").
Hypothesis FBLa : ltac2:(tb__ "0|0|
S0ScS69S1eS2bS1fS4S5aVX3a3;A1A1A1A1S5cS1fS4VX3a3;A1A1A1A3SdA3").
Hypothesis HL3a : ltac2:(tb__ "0|0|
S0S5S36S5cS1fS4VX3a3;A1A1A1S5aVX3a3;A1A2VL3a;A3").
Hypothesis ELb : ltac2:(tb__ "0|0|
S0ScS6VX3b;S5aVX3b;A1VsLb;A3SdA3").
Hypothesis IDb : ltac2:(tb__ "0|0|
S0ScS58VsLb;VGS;A2SdA3").
Hypothesis GLb : ltac2:(tb__ "0|0|
S0S1dS59VsLb;S1fS4VX3b;A1A1A2S60A3").
Hypothesis FBLb : ltac2:(tb__ "0|0|
S0ScS69S1eS2bS1fS4S5aVX3b;A1A1A1A1S5cS1fS4VX3b;A1A1A1A3SdA3").
Hypothesis HL3b : ltac2:(tb__ "0|0|
S0S5S36S5cS1fS4VX3b;A1A1A1S5aVX3b;A1A2VL3b;A3").

Hypothesis HCOb : ltac2:(tb__ "0|0|
S0S5S64VL3b;S62A2VCO3b;A3").
Hypothesis WCOb : ltac2:(tb__ "0|0|
S0ScS2aS4VCO3b;A1A1SdA3").
Hypothesis XCb : ax_X L3b = [].
Hypothesis SKb : ltac2:(tb__ "0|2|
S0SfS11S11S1dS1dA2S1dA2M0A1S6aS20G0S6bS27S4VL3b;A1A1A4S6aS20G0S6bS10S20SbS20S5fVnx;A1SbS20S5eVnx;A1SeS20A1M1A3A3S10S20S83VnW;Vnx;A2G1A3A3A4A3").
Hypothesis FCb : ltac2:(tb__ "0|0|
S67S1eS10S1eS4bVW;Vst;A2S4aS49A1A3S25S4VL3b;A1A1A3").
Hypothesis FXb : ltac2:(tb__ "0|0|
S67S1eSbS1eS2cS28S6eS23S71A1S23S72A1A3A1SeS1eA1A3S25S4VL3b;A1A1A3").

Hypothesis Cert4a : ltac2:(tb__ "0|1|
S0ScS35S56Ufa0SbS1aZ3c614SeS1aA1A3VGS;SbS5VL3a;SeS5A1M0A3SbS5VY4a0;SbS5VY4a1;G0A3A3A6SdA3").
Hypothesis E4a0 : ltac2:(tb__ "0|0|
S0ScS6VY4a0;VT4a;Vs4a0;A3SdA3").
Hypothesis I4a0 : ltac2:(tb__ "0|0|
S0ScS58Vs4a0;VGS;A2SdA3").
Hypothesis E4a1 : ltac2:(tb__ "0|0|
S0ScS6VY4a1;VT4a;Vs4a1;A3SdA3").
Hypothesis I4a1 : ltac2:(tb__ "0|0|
S0ScS58Vs4a1;VGS;A2SdA3").
Hypothesis Cert4b : ltac2:(tb__ "0|1|
S0ScS35S56Ufa0SbS1aZ3c614SeS1aA1A3VGS;SbS5VCO3b;SeS5A1M0A3SbS5VY4b0;SbS5VY4b1;G0A3A3A6SdA3").
Hypothesis E4b0 : ltac2:(tb__ "0|0|
S0ScS6VY4b0;VT4b;Vs4b0;A3SdA3").
Hypothesis I4b0 : ltac2:(tb__ "0|0|
S0ScS58Vs4b0;VGS;A2SdA3").
Hypothesis E4b1 : ltac2:(tb__ "0|0|
S0ScS6VY4b1;VT4b;Vs4b1;A3SdA3").
Hypothesis I4b1 : ltac2:(tb__ "0|0|
S0ScS58Vs4b1;VGS;A2SdA3").

Hypothesis NXEU2 : ltac2:(tb__ "0|0|
S0ScS57VGS;S1fS4VU2;A1A1A2SdA3").
Hypothesis NXEG3 : ltac2:(tb__ "0|0|
S0ScS57VGS;S1fS4VG3;A1A1A2SdA3").
Hypothesis NXEL3a : ltac2:(tb__ "0|0|
S0ScS57VGS;S1fS4VL3a;A1A1A2SdA3").
Hypothesis NXECOb : ltac2:(tb__ "0|0|
S0ScS57VGS;S1fS4VCO3b;A1A1A2SdA3").
Hypothesis ECert3 : ltac2:(tb__ "0|3|
S0ScS34S56Ufa0SbS1aZ706a0SbS1aZ410f0SeS1aA1A3A3VGS;SbS32S33VU2;Z1S21Z0M0A1M1A3SeS32A1M2A3SbS32S33VX3a;G0G1A3SbS32S33VX3b;G0G1A3G2A3A3A6SdA3").
Hypothesis ECert3a : ltac2:(tb__ "0|3|
S0ScS34S56Ufa0SbS1aZ410f0SeS1aA1A3VGS;SbS32S33VG3;Z1S21Z0M0A1M1A3SeS32A1M2A3SbS32S33VX3a3;G0G1A3G2A3A6SdA3").
Hypothesis ECert4a : ltac2:(tb__ "0|3|
S0ScS34S56Ufa0SbS1aZ3c614SeS1aA1A3VGS;SbS32S33VL3a;Z1S21Z0M0A1M1A3SeS32A1M2A3SbS32S33VY4a0;G0G1A3SbS32S33VY4a1;G0G1A3G2A3A3A6SdA3").
Hypothesis ECert4b : ltac2:(tb__ "0|3|
S0ScS34S56Ufa0SbS1aZ3c614SeS1aA1A3VGS;SbS32S33VCO3b;Z1S21Z0M0A1M1A3SeS32A1M2A3SbS32S33VY4b0;G0G1A3SbS32S33VY4b1;G0G1A3G2A3A3A6SdA3").

Lemma RSU' : ltac2:(tb__ "0|1|
S3dS45S1cS3bQ40A1M0S1cSfG0A1S55S4dS4cS4fS14S40S3eR7A1A2A1Z1A2S50Z2Z14A2A2S37Vsegs;VJG;VAX;R8R7R6R5A5VD2;R4R3R2A6S37Vsegs;VJG;VAX;R9R8R7R6A5VU2;R5R4R3A6F_;F_;Fw;Ftp;FrhoX;Fa;Frho;FKc;FA;").
Proof. rr RSU. Qed.
Lemma RS3' : ltac2:(tb__ "0|1|
S3dS45S1cS3bQ40A1M0S1cSfG0A1S55S37Vsegs;VJG;VAX;R7R6R5R4A5VX3a;R3R2R1A6S37Vsegs;VJG;VAX;R8R7R6R5A5VCS3;R4R3R2A6F_;Fw;Ftp;FrhoX;Fa;Frho;FKc;FA;").
Proof. rr RS3. Qed.
Lemma ens_oblig' : ltac2:(tb__ "0|c|
S3dS45S1cS3bQ40M0A1M1S1cSfG1A1S0S47Vst;S46A3S0SfS44A1VW;SeS44A1A3F_;S48R6A1S4dS4cS4fS14S40S3eR8A1A2A1Z1A2S50Z2Z14A2A2SfS79A1M2S77S78S89Vsegs;R8R7VCS3;S12G2S6cR3S6dR2R1A2A4A5VJG;VAX;RdRcRbRaR9R8R4R2A9S26RaS5bA2G1S3aG0R1A2M3S1aZ20000S1aS1S0S1aS53R2Z1000A2Z0M4A3S1S4dG4R2A2S1S4eS4cR2R1A2M5S7aS7bR6A1M6A1A2S1S0ScS7dS80G6A1R3S3cG0R1A2M7A3SdA3S1S0ScS7cS7fG6A1M8R3G7A3SdA3S1S4eS88G8R2G5A3R1A2S1S52S8aR6RcA2R1A2S1S20S68S20R1S27S4VCS3;A1A1A3S2eS2dRfR2A2S12S1aS1aR4S4cR4R3A2A4A2F_;Fo;S1G1S1S4eR3G3A2S4dG3S4cR3R2A2A2A2S0ScS2fVsegs;R2A2S17A3F_;Fx;S1S11S1dS1dA2M9S1aS68G9R2S8VCS3;A1A3S1S4eS3aG0S26R10S18S1dS1dR3A3A2A2MaR2A2S4dR2S4cGaS3aG0S26R10S19S1dS1dR3A3A2A2A2A2A2S2S1S4eR6S3aG0SaS3aG0S26R11S9VCS3;A1A2A2R3A2A2MbA2S4dGbS4cR6R5A2A2A2A1F_;F_;Fy;Frr;VJGo;R11R10RfReRdRcR8S7eR2G5S81S85G6R3G7A3R6A2A3A8A2A2A2A2A2A2A2A2A2A2Tnlit;Tua;Ta0;F_;F_;Fmd;Fms;Ftr;F_;F_;F_;Ftp;FrhoX;Fa;Frho;FKc;FA;").
Proof. rr ens_oblig. Qed.
Lemma ensure_post' : ltac2:(tb__ "0|6|
S3dS45S1cS3bQ40M0A1M1S1cSfG1A1SfS79A1M2S77S78S0S47Vst;S46A3S0SfS44A1VW;SeS44A1A3F_;S1aS1S4eS74S3aG0R8A2A1M3R1A2S4dR1S4cG3S51S65S3aG0S24R9PcM4A2A2A1Z8A2A2A2A2S2S0S13S3bQ8A1M5A1S29RaS3cG0R2A2A2S15G5A1A3A1F_;Fz;S37Vsegs;VJGo;RbRaR9R8A4VG3;R7R6S12G2S6cR5S6dR4R3A2A4A6S3S1cS1cS3S1cS1cS1S75S3fReA1S3aG0RbA2S65S3aG0S24RcG4A2A2A1RcR1A5S37Vsegs;VJG;VAXP;ReRdR1RbA5VG3;R2R9S12G2S6cR8S6dR7R6A2A4A6A2Lrho'';A2Lr2;A2F_;F_;F_;Fmd';Fms;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;").
Proof. rr ensure_post. Qed.
Lemma carve_w' : ltac2:(tb__ "0|1|
S3dS45S1cS3bQ40A1M0S1cSfG0A1S55S0S47Vst;S46A3S0SfS44A1VW;SeS44A1A3F_;S37Vsegs;VJG;VAX;R8R7R6R5A5VL3b;R4R3R2A6S37Vsegs;VJG;VAX;R9R8R7R6A5VCO3b;R5R4R3A6F_;F_;Fw;Ftp;Fr;Fa;Frho;FKc;FA;").
Proof. rr carve_w. Qed.

Lemma epath_b : ltac2:(tb__ "0|2|
S3dS45S1cS3bQ40A1M0S55OF_;S0S47Vst;S46A3S0SfS44A1VW;SeS44A1A3F_;S66VW;Vst;A2S48R6A1S1cSfG0A1M1S54Vsegs;S37Vsegs;VJG;VAX;RaR9R8R7A5VT4b;R2R1A5R6A3FtY;FrY;S1cG1S54Vsegs;S37Vsegs;VJG;VAX;RbRaR9R8A5VX3b;R2R1A5R7A3Ftp;Fr;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a Q HW HUS HKc HCb r tp.
  pose proof (JGs_stable nW st tmax nx Hnx NXG AX A Kc rho a HUS HKc) as HST.
  apply (etc_pre (SPA segs (JG AX A Kc rho a) CO3b (rho_sub r sLb) tp));
    [intros w Hw; exact (carve_w' A Kc rho a _ tp w HW (gen_x11 nW st tmax nx Hnx NXG AX A Kc rho a X3b L3b sLb r tp w HUS HKc ELb IDb GLb FBLb HL3b Hw))|].
  apply (ecfg_2 [0x3c614] CO3b Y4b0 Y4b1 (JG AX A Kc rho a) Q tp _ HST NXECOb ECert4b); intros rE.
  - apply (etc_pre (SPA segs (JG AX A Kc rho a) T4b (rho_sub rE s4b0) tp)); [intros w Hw; exact (join4 nW st tmax nx Hnx NXG AX A Kc rho a Y4b0 T4b s4b0 rE tp w HUS HKc E4b0 I4b0 Hw) | apply HCb].
  - apply (etc_pre (SPA segs (JG AX A Kc rho a) T4b (rho_sub rE s4b1) tp)); [intros w Hw; exact (join4 nW st tmax nx Hnx NXG AX A Kc rho a Y4b1 T4b s4b1 rE tp w HUS HKc E4b1 I4b1 Hw) | apply HCb].
Qed.

Lemma epath_a : ltac2:(tb__ "0|6|
S3dS45S1cS3bQ40M0A1M1S55OF_;S0S47Vst;S46A3S0SfS44A1VW;SeS44A1A3F_;S66VW;Vst;A2S48R6A1S4dS4cS4fS14S40S3eR8A1A2A1Z1A2S50Z2Z14A2A2S1aS1S4eS74S3aG0R7A2A1M2R1A2S4dR1S4cG2S51S65S3aG0S24R8PcM3A2A2A1Z8A2A2A2A2S2S0S13S3bQ8A1M4A1S29R9S3cG0R2A2A2S15G4A1A3A1F_;Fz;S1cS1cSfG1A1M5S75S3fRdA1S3aG0RaA2S65S3aG0S24RbG3A2A2A1RbR3A5S54Vsegs;S37Vsegs;VJG;VAXP;ReRdR4RbA5VT4a;R3R2A5RaA3F_;FtY;FrY;Frho'';S1cG5S54Vsegs;S37Vsegs;VJG;VAX;RdRcRbRaA5VX3a;R2R1A5R9A3Ftp;Fr;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a Q HW HUS HKc Hok RUNDEF HCa r tp.
  pose proof (JGs_stable nW st tmax nx Hnx NXG AX A Kc rho a HUS HKc) as HST.
  apply (etc_pre (SPA segs (JG AX A Kc rho a) CS3 r tp)); [intros w Hw; exact (RS3' A Kc rho a r tp w Hw)|].
  assert (HST' : stableA segs (ss_next (ax_S CS3)) (JG AX A Kc rho a)).
  { eapply stableA_mono; [|exact HST]. apply Pos.leb_le. exact NXS3. }
  eapply etriple_seq.
  { apply (etriple_fixed_commitA segs (JG AX A Kc rho a) (JGo A Kc rho a) CS3 r tp Bw 131072 HST' IC3 R17 R10 BBw R11 R12 R13 R14 R15 eq_refl ltac:(lia)).
    exact (ens_oblig' A Kc rho a r tp HW HKc Hok). }
  fold O_blk. rewrite HG3.
  apply (etc_pre (fun w => exists r2 rho'', slink4 (aa_geom A) (bv_unsigned a) (secmapsize (bv_unsigned (rw rho 12%positive))) rho rho'' /\ SPA segs (JG AXP A Kc rho'' a) G3 r2 tp w));
    [intros w Hw; destruct w as [tr [ms md]]; exact (ensure_post' A Kc rho a r tp tr ms md HW RUNDEF Hw)|].
  apply etriple_ex; intros r2. apply etriple_ex; intros rho''.
  apply (etriple_pre_pure segs _ _ (slink4 (aa_geom A) (bv_unsigned a) (secmapsize (bv_unsigned (rw rho 12%positive))) rho rho'')); [intros w [SL _]; exact SL|]. intros SL.
  apply (etc_pre (SPA segs (JG AXP A Kc rho'' a) G3 r2 tp)); [intros w [_ Hw]; exact Hw|].
  pose proof (JGs_stable nW st tmax nx Hnx NXG AXP A Kc rho'' a HUS HKc) as HST2.
  apply (ecfg_1 nx [0x410f0] G3 X3a3 (JG AXP A Kc rho'' a) Q tp r2 HST2 NXEG3 ECert3a). intros rE.
  apply (etc_pre (SPA segs (JG AXP A Kc rho'' a) L3a (rho_sub rE sLa) tp));
    [intros w Hw; exact (gen_x11 nW st tmax nx Hnx NXG AXP A Kc rho'' a X3a3 L3a sLa rE tp w HUS HKc ELa IDa GLa FBLa HL3a Hw)|].
  apply (ecfg_2 [0x3c614] L3a Y4a0 Y4a1 (JG AXP A Kc rho'' a) Q tp _ HST2 NXEL3a ECert4a); intros rE'.
  - apply (etc_pre (SPA segs (JG AXP A Kc rho'' a) T4a (rho_sub rE' s4a0) tp)); [intros w Hw; exact (join4 nW st tmax nx Hnx NXG AXP A Kc rho'' a Y4a0 T4a s4a0 rE' tp w HUS HKc E4a0 I4a0 Hw) | apply HCa; exact SL].
  - apply (etc_pre (SPA segs (JG AXP A Kc rho'' a) T4a (rho_sub rE' s4a1) tp)); [intros w Hw; exact (join4 nW st tmax nx Hnx NXG AXP A Kc rho'' a Y4a1 T4a s4a1 rE' tp w HUS HKc E4a1 I4a1 Hw) | apply HCa; exact SL].
Qed.

Theorem esec_g3 : ltac2:(tb__ "0|6|
S3dS45S1cS3bQ40M0A1M1S55OF_;S0S47Vst;S46A3S0SfS44A1VW;SeS44A1A3F_;S66VW;Vst;A2S48R6A1S4dS4cS4fS14S40S3eR8A1A2A1Z1A2S50Z2Z14A2A2S1aS1S4eS74S3aG0R7A2A1M2R1A2S4dR1S4cG2S51S65S3aG0S24R8PcM3A2A2A1Z8A2A2A2A2S2S0S13S3bQ8A1M4A1S29R9S3cG0R2A2A2S15G4A1A3A1F_;Fz;S1cS1cSfG1A1M5S75S3fRdA1S3aG0RaA2S65S3aG0S24RbG3A2A2A1RbR3A5S54Vsegs;S37Vsegs;VJG;VAXP;ReRdR4RbA5VT4a;R3R2A5RaA3F_;FtY;FrY;Frho'';S1cG5S54Vsegs;S37Vsegs;VJG;VAX;RdRcRbRaA5VT4b;R2R1A5R9A3FtY;FrY;S1cG5S54Vsegs;S37Vsegs;VJG;VAX;ReRdRcRbA5VD2;R2R1A5RaA3FtX;FrX;F_;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;").
Proof.
  assert (USED := (WU2, DU2, NXU2, HU2, Cert3, WC3, DC3, NXC3, HC3, FX3a, IC3, R17, R10, BBw, R11, R12, R13, R14, R15, XC3, SK3, FC3, FCS3, NXS3, HG3, Cert3a, ELa, IDa, GLa, FBLa, HL3a, ELb, IDb, GLb, FBLb, HL3b, HCOb, WCOb, XCb, SKb, FCb, FXb, Cert4a, E4a0, I4a0, E4a1, I4a1, Cert4b, E4b0, I4b0, E4b1, I4b1, NXEU2, NXEG3, NXEL3a, NXECOb, ECert3, ECert3a, ECert4a, ECert4b)); clear USED.
  intros A Kc rho a Q HW HUS HKc Hok RUNDEF HCa HCb rX tX.
  pose proof (JGs_stable nW st tmax nx Hnx NXG AX A Kc rho a HUS HKc) as HST.
  apply (etc_pre (SPA segs (JG AX A Kc rho a) U2 rX tX)); [intros w Hw; exact (RSU' A Kc rho a rX tX w Hok Hw)|].
  apply (ecfg_2 [0x706a0; 0x410f0] U2 X3a X3b (JG AX A Kc rho a) Q tX rX HST NXEU2 ECert3); intros rE.
  - exact (epath_a A Kc rho a Q HW HUS HKc Hok RUNDEF HCa rE tX).
  - exact (epath_b A Kc rho a Q HW HUS HKc HCb rE tX).
Qed.
End G3E.
End SEC4E.
End SpineMallocSecE2.

(* [comment removed for export] *)
Module SpineCallocOvA.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "entailsA"; "@Corelib.Init.Logic"; "eq"; "and"; "False"; "ex"; "@Corelib.Init.Datatypes"; "list"; "bool"; "true"; "nil"; "pair"; "prod"; "cons"; "Some"; "option"; "app"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sv"; "rw"; "ss_next"; "valuation"; "SLit"; "sobj"; "swf"; "SVar"; "sprop_below"; "holds"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "AE_A"; "Pre_callocI"; "KcA"; "L_calloc_null"; "JL_calloc_null"; "Kc_ok"; "unwind_stopJ"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@Stdlib.Lists.List"; "In"; "forallb"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "ax_add_facts"; "check_cfgA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.CertCallocOv"; "stRo_S"; "EXo"; "s_o"; "stKo"; "N_ovn"; "R_o"; "stRo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineCallocI"; "Jc"; "rho_ce"; "sa_c"; "@Stdlib.ZArith.BinInt.Z"; "le"; "mul"; "pow"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_obj"; "carve_spec"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull"; "NW2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1"; "RT_m1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM"; "IMG_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineCallocIo"; "FACTSo"; "P0o"; "sb_o"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ji.SpineCallocOv"; "JGe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec2"; "IMG_S"; "@Stdlib.PArith.BinPos.Pos"; "le"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA GlueA2 SummaryA SysCallA MmapA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts StartLib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildSM SMGlue InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNullInit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocS9 RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.RebuildN.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import MmapSymA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require id.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocSec SpineMallocSec2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineCallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineCallocSec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ja.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ji.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.CertMallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.id.CertMallocSN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CallocArith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineCallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineCallocIo OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.CertCallocOv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineCallocSec OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ja.SpineCallocE OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ji.SpineCallocOv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section OVA.
Variable nW : nat. Variable st : ustop.
Let W : list ulink := Wcan nW.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTM : ltac2:(tb__ "0|0|
S27S2fVCST;R1A2S2fS51R2A2S5F_;F_;Fa;").
Hypothesis HCSTS : ltac2:(tb__ "0|0|
S27S2fVCST;R1A2S2fS56R2A2S5F_;F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let law_die : forall A rho tp md, AInv A rho tp md -> cell_ok (view segs (rm rho)) (mkACell 0x17fbdc 4 0) := AInvA_die.

Hypothesis HUS : stopJ_stable W st.
Hypothesis Wa : ltac2:(tb__ "0|0|
S3S8S18S40VW;Vst;A2A1S9A3").
Hypothesis Da : ltac2:(tb__ "0|4|
S3SfScS7ScS12S12A2M0A1M1S7S11A1M2A2M3A1S49S1S1dS1cVW;Vst;A3A1S40VW;Vst;A2A2SeG3SbG1G2SdG0SbS12S12S19P18A1S16S4aA1A4SaG0A1A3SaS11A1A4A2A3").
Hypothesis Wb : ltac2:(tb__ "0|0|
S3S8S18S54VW;Vst;A2A1S9A3").
Hypothesis Fbo : ltac2:(tb__ "0|0|
S3S8S26S11S1aS4fA1S52VW;Vst;A2A3S9A3").
Hypothesis RN : ltac2:(tb__ "0|0|
S3S7S17A1S3bVW;Vst;A2S10S17S50S44S4eS17S4dS3aA4A3A3").
Hypothesis WRn : ltac2:(tb__ "0|0|
S3S8S18S36VW;Vst;A2A1S9A3").
Hypothesis DKRn : ltac2:(tb__ "0|4|
S3SfScS7ScS12S12A2M0A1M1S7S11A1M2A2M3A1S49S1S39VW;Vst;A2A1S36VW;Vst;A2A2SeG3SbG1G2SdG0SbS12S12S16S4aA1S19P18A1A4SaG0A1A3SaS11A1A4A2A3").
Hypothesis NXRn : ltac2:(tb__ "0|0|
S3S28S14S36VW;Vst;A2A1S14S1S39VW;Vst;A2A1A1A3").
Hypothesis ENTn : ltac2:(tb__ "0|0|
S3S8S2S3cVW;Vst;A2S1fS1cVW;Vst;A3S38VW;Vst;A2A3S9A3").
Hypothesis IDn : ltac2:(tb__ "0|0|
S3S8S4cS38VW;Vst;A2S30A2S9A3").

Variable cuts : list axst.
Hypothesis HCUT : ltac2:(tb__ "0|2|
S2eS15S22VW;Vst;S3fR2R1A2A3S6S7S11A1M0G0S4S25S0S33R1S53VW;Vst;A2M1A2Vcuts;A3S4S45S11S1bS3fR4R3A2A1R1A3S3S8S26S11S1aS14S1G1A1A1A1R1A3S9A3A2A2Lsx;A2F_;Frho;FA;").
Hypothesis CertO : ltac2:(tb__ "0|0|
S3S8S34S4bUfa0SaS27A1S3dVcuts;SdS0S37VW;Vst;A2SaS0A1A3A6S9A3").

Lemma ov_front : ltac2:(tb__ "0|1|
S2eS1eS15S7S24Q40M0A1A1S46S41S43Z2Z40A2S42S23G0S13R3PcA2A2S23G0S13R3PdA2A2A2A2S29Vsegs;S3eVW;Vst;R6R5A4S1dS1cVW;Vst;A3R4R3R2A6S6S0S0S4S25S0R1Vcuts;A3S29Vsegs;S55VnW;Vst;R8R7R6A5R1S3fR8R6A2R5R4A6A2LC;A2F_;F_;Fw;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp w HOV Hw.
  pose proof (c_instantiate_ov law_die W st A Kc rho tp w HUS Wa Da Wb Fbo HOV Hw) as H1.
  destruct (HCUT A rho (proj1 (proj2 (proj2 (proj2 (proj2 H1)))))) as (sx & Hin & Hh & Hb).
  exists (ax_add_facts sx (P0o W st)). split; [exact Hin|].
  apply (SPA_withG_intro segs (Jc W st A Kc) GW _ (rho_ce A rho) tp w).
  exact (SPA_add_facts' segs (Jc W st A Kc) (rho_ce A rho) (P0o W st) sx tp w Hh Hb H1).
Qed.

Theorem calloc_ov : ltac2:(tb__ "0|2|
S46OF_;S2eS1eS15S7S24Q40M0A1A1S7ScS0S2cA2M1A1S21R4A1S2bVsegs;R7S2aR5A1A3S25G1SbS0S2cS1fS1cVW;Vst;A3S20VAInv;VCST;VXGL;R7R6A5A4R3A3S41S43Z2Z40A2S42S23G0S13R6PcA2A2S23G0S13R6PdA2A2A2A2S48Vsegs;RaS29Vsegs;S3eVW;Vst;R9R8A4S1dS1cVW;Vst;A3R7R6A5S2dVsegs;S30R7R6R5A5A4F_;F_;F_;F_;FPosts;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp Posts HKc Hokl HPin HOV.
  apply triple_conseq with (P := fun w => exists C, In C cuts /\ SPA segs (JGe nW st A Kc rho) C (rho_ce A rho) tp w) (Q := LQPA segs NF rho tp Posts);
    [intros w Hw; exact (ov_front A Kc rho tp w HOV Hw) | intros w Hw; exact Hw |].
  intros n Hg w (C & HinC & HwC). revert n Hg w HwC.
  change (triple segs ok (SPA segs (JGe nW st A Kc rho) C (rho_ce A rho) tp) (LQPA segs NF rho tp Posts)).
  apply (cfg_soundA segs 4000%nat [] GW cuts [EXo W st] (JGe nW st A Kc rho) ok (LQPA segs NF rho tp Posts) tp).
  - intros r t tr ms md msv' [_ HJ]. apply (Hokl r t tr ms md msv'). destruct HJ as (_ & HK & _). exact HK.
  - exact (JGe_stable nW st A Kc rho HUS HKc).
  - exact CertO.
  - intros E rhoE HinE. destruct HinE as [<-|[]].
    eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw |].
    eapply triple_conseq; [intros w Hw; exact Hw | | apply triple_refl].
    intros w Hw. exact (ov_null_finish nW st CST XGL HCST HXGL HCSTM HCSTS RN WRn DKRn NXRn ENTn IDn A Kc rho tp w rhoE Posts HKc HPin Hw).
  - exact HinC.
Qed.

Hypothesis NXcuts : ltac2:(tb__ "0|0|
S0S25S0R1Vcuts;A3S57S3dS14S1R2A1A1A2F_;FC;").
Hypothesis ECertO : ltac2:(tb__ "0|2|
S3S8S35S4bUfa0SaS27A1S3dS44S0S31S0S32R1Z1S16Z0M0A1M1A3Lc;Vcuts;A4SdS31S32S37VW;Vst;A2G0G1A3SaS31A1A3A6S9A3").
Theorem ecalloc_ov : ltac2:(tb__ "0|2|
S2eS1eS15S7S24Q40M0A1A1S7ScS0S2cA2M1A1S21R4A1S25G1SbS0S2cS1fS1cVW;Vst;A3S20VAInv;VCST;VXGL;R6R5A5A4R2A3S41S43Z2Z40A2S42S23G0S13R5PcA2A2S23G0S13R5PdA2A2A2A2S47Vsegs;S29Vsegs;S3eVW;Vst;R8R7A4S1dS1cVW;Vst;A3R6R5A5S2dVsegs;S30R6R5R4A5A3F_;F_;F_;FPosts;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp Posts HKc HPin HOV w Hw0.
  destruct (ov_front A Kc rho tp w HOV Hw0) as (C & HinC & HwC). clear Hw0. revert w HwC.
  change (etriple segs (SPA segs (JGe nW st A Kc rho) C (rho_ce A rho) tp) (LQPA segs NF rho tp Posts)).
  apply (ecfg_cut 4000%nat [] GW (map (fun c => mkVNA c 1 (SLit 0)) cuts) [mkVNA (EXo W st) 0 (SLit 0)] (JGe nW st A Kc rho) (LQPA segs NF rho tp Posts) tp C _
           (JGe_stable nW st A Kc rho HUS HKc)).
  - intros n Hn. apply in_map_iff in Hn. destruct Hn as (c & <- & Hc). cbn [vna_state]. exact (NXcuts c Hc).
  - exact ECertO.
  - intros E rhoE HinE. destruct HinE as [<-|[]]. cbn [vna_state].
    eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw |].
    eapply etriple_conseq; [intros w Hw; exact Hw | | apply etriple_refl].
    intros w Hw. exact (ov_null_finish nW st CST XGL HCST HXGL HCSTM HCSTS RN WRn DKRn NXRn ENTn IDn A Kc rho tp w rhoE Posts HKc HPin Hw).
  - apply in_map_iff. exists C. split; [reflexivity | exact HinC].
Qed.
End OVA.
End SpineCallocOvA.

(* [comment removed for export] *)
Module SpineCallocSec3I.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "leafA"; "ax_setS"; "la_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jq.SpineCallocSec3I.INST"; "nx0"; "CO1c"; "CO2c"; "CT1c"; "CT2c"; "T0c"; "ET1c"; "ET2c"; "D1c"; "E0c"; "R1c"; "R2c"; "T1c"; "T2c"; "s1c"; "s2c"; "D2c"; "run1"; "run2"; "@Corelib.Init.Datatypes"; "true"; "nil"; "bool"; "cons"; "list"; "prod"; "app"; "option"; "pair"; "Some"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "sprop"; "ss_next"; "ss_facts"; "sprop_below"; "valuation"; "swf"; "ss_objs"; "DUnknown"; "SLit"; "cell"; "mkObj"; "holds"; "rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "GW"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3"; "skel"; "@Stdlib.Lists.List"; "forallb"; "incl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP"; "MSENT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3"; "GS"; "SKEL0"; "JGs"; "JGsC"; "clsP"; "slink"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "KcA"; "Kc_ok"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "assn"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA"; "runsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "smatchA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSS"; "ES1g"; "nxS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocST"; "B2"; "F_map"; "L1"; "L2"; "Pret_ms"; "carveS"; "B1"; "O_1"; "a0e2"; "a2e1"; "a2e2"; "fx2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "secmapsize"; "stopJ_stable"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jp.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.CSecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import CallocBase2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.CallocPosts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 0. Let st : ustop := UStopLe. Let tmax : Z := 2.
Definition nx0 : positive := 220%positive.

Lemma Hnx_0 : ltac2:(tb__ "0|0|
S0S35S5bVW;Vst;Vtmax;A3S6A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXG_0 : ltac2:(tb__ "0|0|
S0S1bS49S33S6A2S19A3").
Proof. reflexivity. Qed.

Definition E0c : axst := Eval vm_compute in (ES1g W st tmax).
Lemma HE0_0 : ltac2:(tb__ "0|0|
S0S2S5aVW;Vst;Vtmax;A3SfA3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition T0c : axst := Eval vm_compute in (ax_add_facts (F_map nx0 true) E0c).
Lemma SKT_0 : ltac2:(tb__ "0|1|
S0S1dS1eS1eS23S23A2S23A2M0A1S36S24G0S3aS2bS1SbA1A1A4S36S24G0S3aS3fU0S6A2A4A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FCT_0 : ltac2:(tb__ "0|0|
S3cS25S1fS25S46VW;Vst;A2S45S44A1A3S27S1SbA1A1A3").
Proof. apply inclb_incl. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FBM_0 : ltac2:(tb__ "0|0|
S0S1bS3bS25S28S26S1SfA1A1A1S5dS6S19A2A3S19A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma AF0_0 : ltac2:(tb__ "0|0|
S29S1dS4bQ40A1A1S1eS1dS6cA1S6bA2S54S32R3R2SfR1A5S37S25S30R4A1S5dS6S19A2A3S54S32R5R4SbR3A5F_;F_;Fw;Ftp;Frho;").
Proof.
  intros rho tp w Hsm HF. replace T0c with (ax_add_facts (F_map nx0 true) E0c) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
  apply smatchA_add_facts; [exact Hsm | exact HF | exact FBM_0].
Qed.

Definition run1 : option (list leafA) := Eval vm_compute in (runT0 T0c).
Lemma run1__runeq : ltac2:(tb__ "0|1|
S0S1dS20S1dS3A1A1M0A1S51S32Ufa0S1cS34S3dS1aS34A1A3S1cS2SbS1aS2A1A3A4S1cG0S17S1aG0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run1]). Qed.
Definition ET1c : axst := Eval vm_compute in (leafS 0 run1).
Lemma Cert1_0 : ltac2:(tb__ "0|1|
S0S1bS50S32Ufa0S1cS34S3dS1aS34A1A3S3eS6A1S1cS2SbS1aS2A1M0A3S1cS2ScG0A3A6S19A3").
Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] (GS nx0) [T0c] [ET1c] [run1]); [exact run1__runeq | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]. Qed.
Definition CT1c : axst := Eval vm_compute in (CT1 ET1c).
Definition CO1c : axst := Eval vm_compute in (CO1 W st tmax ET1c).
Lemma WC1_0 : ltac2:(tb__ "0|0|
S0S1bS2aS1S9A1A1S19A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma DF1_0 : ltac2:(tb__ "0|4|
S0S20S1eS1dS1eS23S23A2M0A1M1S1dS25A1M2A2M3A1S4fS1ScA1S1S9A1A2S22G3S21G1G2S1cG0S21S23S23S65S6A1S5eA4S1aG0A1A3S1aS25A1A4A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NX1_0 : ltac2:(tb__ "0|0|
S0S35S26S1S9A1A1S26S1ScA1A1A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HC1_0 : ltac2:(tb__ "0|0|
S0S2S4ScS1S9A1A2S9A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SK1_0 : ltac2:(tb__ "0|2|
S0S1dS1eS1eS23S23A2S23A2M0A1S36S24G0S3aS2bS1S9A1A1A4S36S24G0S3aS1fS24S1aS24A1M1S1fS24S3fU0S6A2G1A3A3A4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FC1_0 : ltac2:(tb__ "0|0|
S3cS25S1fS25S46VW;Vst;A2S45S44A1A3S27S1S9A1A1A3"). Proof. apply inclb_incl. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma XC1_0 : ax_X CT1c = []. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HCO1_0 : ltac2:(tb__ "0|0|
S0S2S61S9S2fS62S6A1S2dZ0A1S5eS1aS2eA1S2cA5A2S7A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma WCO1_0 : ltac2:(tb__ "0|0|
S0S1bS2aS1S7A1A1S19A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition s1c : wsub := Eval vm_compute in (callsub CO1c Pre_memsetA).
Definition R1c : list sobj := Eval vm_compute in (callR CO1c Pre_memsetA s1c).
Definition T1c : axst := Eval vm_compute in (callT CO1c Pre_memsetA Pret_ms s1c R1c).
Lemma He1_0 : ltac2:(tb__ "0|1|
S0S20S1dS24A1M0A1S58S7S38S14A3S22G0S10A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Hchk1_0 : ltac2:(tb__ "0|0|
S0S1bS57S7S38S14S10S36S3S2S5S39A4A5S19A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HT1_0 : ltac2:(tb__ "0|0|
S0S2S59S14S38S60S7S10A5S12A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FBC1_0 : ltac2:(tb__ "0|1|
S0S1bS3bS25S28S26S1S7A1M0A1A1S27G0A1A3S19A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FBT1_0 : ltac2:(tb__ "0|0|
S0S1bS3bS25S28S26S1S12A1A1A1S27S1S7A1A1A3S19A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXC1_0 : ltac2:(tb__ "0|0|
S0S1bS49S3eS6A1S26S1S7A1A1A2S19A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition D1c : axst := Eval vm_compute in (ax_with_facts T1c (ss_facts (ax_S CO1c))).
Lemma HD1_0 : ltac2:(tb__ "0|0|
S0S2S52S12S27S1S7A1A1A2SeA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition run2 : option (list leafA) := Eval vm_compute in (runT0 D1c).
Lemma run2__runeq : ltac2:(tb__ "0|1|
S0S1dS20S1dS3A1A1M0A1S51S32Ufa0S1cS34S3dS1aS34A1A3S1cS2SeS1aS2A1A3A4S1cG0S18S1aG0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run2]). Qed.
Definition ET2c : axst := Eval vm_compute in (leafS 0 run2).
Lemma Cert2_0 : ltac2:(tb__ "0|1|
S0S1bS50S32Ufa0S1cS34S3dS1aS34A1A3S3eS6A1S1cS2SeS1aS2A1M0A3S1cS2SdG0A3A6S19A3").
Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] (GS nx0) [D1c] [ET2c] [run2]); [exact run2__runeq | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]. Qed.
Definition CT2c : axst := Eval vm_compute in (CT2 W st tmax ET2c).
Definition CO2c : axst := Eval vm_compute in (CO2 W st tmax ET2c).
Lemma WC2_0 : ltac2:(tb__ "0|0|
S0S1bS2aS1SaA1A1S19A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma DF2_0 : ltac2:(tb__ "0|4|
S0S20S1eS1dS1eS23S23A2M0A1M1S1dS25A1M2A2M3A1S4fS1SdA1S1SaA1A2S22G3S21G1G2S1cG0S21S23S23S64S6A1S5cS6A1A4S1cG0S21S23S23S66S6A1S5fA4S1aG0A1A3A3S67A4A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NX2_0 : ltac2:(tb__ "0|0|
S0S35S26S1SaA1A1S26S1SdA1A1A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HC2_0 : ltac2:(tb__ "0|0|
S0S2S4SdS1SaA1A2SaA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SK2_0 : ltac2:(tb__ "0|2|
S0S1dS1eS1eS23S23A2S23A2M0A1S36S24G0S3aS2bS1SaA1A1A4S36S24G0S3aS1fS24S1cS24S63S6A1S1aS24A1M1A3S1fS24S3fU0S6A2G1A3A3A4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FC2_0 : ltac2:(tb__ "0|0|
S3cS25S1fS25S46VW;Vst;A2S45S44A1A3S27S1SaA1A1A3"). Proof. apply inclb_incl. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma XC2_0 : ax_X CT2c = []. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HCO2_0 : ltac2:(tb__ "0|0|
S0S2S61SaS2fS5cS6A1S2dZ0A1S5fS1aS2eA1S2cA5A2S8A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma WCO2_0 : ltac2:(tb__ "0|0|
S0S1bS2aS1S8A1A1S19A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition s2c : wsub := Eval vm_compute in (callsub CO2c Pre_memsetA).
Definition R2c : list sobj := Eval vm_compute in (callR CO2c Pre_memsetA s2c).
Definition T2c : axst := Eval vm_compute in (callT CO2c Pre_memsetA Pret_ms s2c R2c).
Lemma He2_0 : ltac2:(tb__ "0|1|
S0S20S1dS24A1M0A1S58S8S38S15A3S22G0S11A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Hchk2_0 : ltac2:(tb__ "0|0|
S0S1bS57S8S38S15S11S36S3S2S5S39A4A5S19A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HT2_0 : ltac2:(tb__ "0|0|
S0S2S59S15S38S60S8S11A5S13A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FBC2_0 : ltac2:(tb__ "0|1|
S0S1bS3bS25S28S26S1S8A1M0A1A1S27G0A1A3S19A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FBT2_0 : ltac2:(tb__ "0|0|
S0S1bS3bS25S28S26S1S13A1A1A1S27S1S8A1A1A3S19A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXC2_0 : ltac2:(tb__ "0|0|
S0S1bS49S3eS6A1S26S1S8A1A1A2S19A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition D2c : axst := Eval vm_compute in (ax_with_facts T2c (ss_facts (ax_S CO2c))).
Lemma HD2_0 : ltac2:(tb__ "0|0|
S0S2S52S13S27S1S8A1A1A2S16A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Theorem sec_g12_0h : ltac2:(tb__ "0|5|
S4eOF_;S68S47S29S4bQ40M0A1M1S1dG1A1M2S4dS6aVW;Vst;A2S48R6A1S56S32R9S55R7A1A3S4aG0S31R7PcA2A2S34S42S19S4aG0R7A2S69R1A1A3S29S29G2S43S4aG0RbA2S69R5A1RcR3A4S4cS32R10S53S32S40U0M3Vst;S6S68R1LX;M4RfReR4RcA8S16R3R2A5RaA4F_;FtpY;FrhoY;Frho';S29S4cS32ReS53S32S41G3Vst;S6G4RdRcRbRaA8S5aVW;Vst;Vtmax;A3R1R9A5R8A4FrhoX;F_;F_;Tnv;F_;F_;F_;FQ;Ftp;Fa;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho a tp Q HUS HKc Hokl nv HC HCONT rhoX. rewrite HE0_0. rewrite <- HD2_0 in HCONT.
  exact (sec_g12 0%nat st tmax true nx0 Hnx_0 NXG_0 (fun X : AA => X) (fun X => eq_refl) (fun X => eq_refl) E0c T0c SKT_0 FCT_0 AF0_0
           ET1c CT1c CO1c T1c ET2c CT2c CO2c T2c s1c s2c R1c R2c
           Cert1_0 ltac:(rewrite HD1_0; exact Cert2_0)
           WC1_0 DF1_0 NX1_0 HC1_0 SK1_0 FC1_0 XC1_0 HCO1_0 WCO1_0 He1_0 Hchk1_0 HT1_0 FBC1_0 FBT1_0 NXC1_0
           WC2_0 DF2_0 NX2_0 HC2_0 SK2_0 FC2_0 XC2_0 HCO2_0 WCO2_0 He2_0 Hchk2_0 HT2_0 FBC2_0 FBT2_0 NXC2_0
           ok A Kc rho a tp Q ltac:(hw_discharge) HUS HKc Hokl HC HCONT rhoX).
Qed.
End INST.
End SpineCallocSec3I.

