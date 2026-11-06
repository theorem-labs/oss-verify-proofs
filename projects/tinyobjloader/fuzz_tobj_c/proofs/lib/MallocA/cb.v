(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Ox.F128_070.   (* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia FunctionalExtensionality.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c7.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require dc.

(* [comment removed for export] *)
Module RebuildQQ.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "bool"; "true"; "list"; "false"; "length"; "nat"; "@Corelib.Init.Logic"; "eq"; "iff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cb.RebuildQQ"; "phQ"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillJ"; "gh_new"; "phase"; "JR"; "mkPh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c7.SpineMallocQ15"; "phFin"; "phU3"; "phUF3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "ulink"; "ustop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b2.InvQC"; "AInvQC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_cache_inited"; "class_state"; "cs_free_array"; "cs_mapped_free_array"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel"; "kchunks"; "refillA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "cls_of"; "cst_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b5.SpineMallocQ1"; "entryRq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.SpineMallocQ7"; "popfacts"; "@Stdlib.ZArith.BinInt.Z"; "add"; "lt"; "mul"; "of_nat"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymFrame Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require PrimCredit PrimCreditLaws Inv SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RebuildM RefillModel RefillModelP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillTR RefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bm.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RebuildRZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require az.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCredit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCreditLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b2.InvQC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.DrainS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.DrainSG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.RefillS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModelP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.RefillJP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b5.SpineMallocQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b6.SpineMallocQ2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.SpineMallocQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bm.SpineMallocQ4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bn.SpineMallocQ5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bq.SpineMallocQ6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.SpineMallocQ7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bm.SpineMallocQ9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bs.SpineMallocQ12 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bu.SpineMallocQ13 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c2.SpineMallocQ14 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c7.SpineMallocQ15 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildRZ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.RebuildRP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.RebuildRM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b2.RebuildR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.RebuildG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b5.RebuildGC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b5.RebuildD.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c3.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation segs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree.segsA.

Definition phQ (b : bool) (new k : Z) : phase := ltac2:(tb__ "0|1|
S11U3M0S1S6Lb;Vb;G0U0X1x2Vnew;Vk;S2S2A6").
Lemma phQ_P : ltac2:(tb__ "0|0|
S0S0S7SfS12S13R2R1A3SbS4R2R1A3A3Fk;Fnew;"). Proof. reflexivity. Qed.
Lemma phQ_M : ltac2:(tb__ "0|0|
S0S0S7SfS12S14R2R1A3SbS2R2R1A3A3Fk;Fnew;"). Proof. reflexivity. Qed.

Section RQ.
Theorem refill_rebuild_Q : ltac2:(tb__ "0|2|
S19S15S9S3S28Q40M0A1A1M1ScS3S16A1S17S9S22R8R6R5R4R3R2R1A7S23R9R7A2S1S7S1S1aRbA1S2A3S29G0SaRaPcA2A2S0S20R1A1S0S21ReR2A2S1bS8S7S1R5S2A3S25S1dR1A1S26Z4S24S27S5S0S1cR1A1A2A1SeRfRdA2A2A2A2A2S9G1S3SdA1ScS10R14R13R12R11R10SbRaSeR14R12A2S1eR7A1A3R4R3R2R1AaS18S1fR15R8A2R5R4R2A4F_;Fmd;Ftr;Ftp;Fr;F_;Tcs;Tc;Tnv;F_;Fb;FPF;FHE;Frho;Fst;FW;Fmd0;Ftp0;Frb;FKc;FA;").
Proof.
  intros A Kc rb tp0 md0 W st rho HE PF b Hini nv c cs HB r tp tr md (HFz & HGh & HK & HM & HR & HRM).
  destruct (pop_geo A rb tp0 md0 W st rho HE PF) as (C1 & S1 & AU0 & MU1 & N4 & K1 & KN & NF0 & MF1 & MF2 & MF0 & G13 & G14 & FAr & T1 & PS1 & TB).
  fold nv c cs in C1, S1, AU0, MU1, N4, K1, KN, NF0, MF1, MF2, MF0, FAr.
  destruct (entry_pure A rb tp0 md0 W st rho HE PF) as (HP & Hc0 & NP & RM). fold nv c cs in HP, Hc0, NP, RM.
  pose proof (P_csR A rb tp0 md0 W st rho HE PF) as (X1 & X2 & X3 & X5 & X6 & X7 & LP' & HIDS). cbn zeta in X1, X2, X3, X5, X6, X7, LP', HIDS. fold nv c cs in X1, X2, X3, X5, X6, X7, LP', HIDS.
  pose proof (P_fields c cs _ C1 HP NP RM) as PFL. cbn zeta in PFL. destruct PFL as (_ & _ & _ & XFA & _). pose proof (P_newZ A rb) as ENZ. fold nv c cs in ENZ. pose proof (P_faP_len c cs _ C1 HP RM) as LPz. rewrite ENZ in LPz. rewrite LPz in XFA.
  destruct (refill_pure c cs _ C1 HP Hc0 ltac:(intros _; exact RM)) as (HPR & _). cbn zeta in HPR.
  pose proof (pop_credit_eq A rb tp0 md0 W st rho HE PF) as CEQ. fold nv c cs in CEQ.
  set (k := kchunks c) in *. set (new := gh_new A rb) in *. set (nf := Z.of_nat (length (cs_free_array cs))) in *.
  set (mu := cs_mapped_user cs) in *. set (mfa := cs_mapped_free_array cs) in *. set (au := cs_allocated_user cs) in *. set (fP := faP c cs) in *.
  set (G := aa_geom A) in *. set (SB := ag_spacebeg G) in *. set (T := ag_thread G) in *.
  assert (Eb : (mfa <? 4 * (nf + new)) = b).
  { destruct b; [apply Z.ltb_lt; apply (proj1 HB); reflexivity | apply Z.ltb_ge; destruct (Z_lt_dec mfa (4 * (nf + new))) as [X|X]; [discriminate (proj2 HB X) | clear -X; lia]]. }
  rewrite Eb in X7, CEQ.
  pose proof HE as (_ & HA & _ & _ & _ & Hnv & _ & _ & HWF). fold nv in Hnv.
  pose proof HA as (HG & _ & _ & HRest0 & HMI0 & HI3 & HB0). destruct HRest0 as (_ & _ & (PL & _) & _).

  assert (EU0 : U0 A rb = SB + c * 4294967296 + mu) by (unfold U0, region_beg, kRegionSize; fold nv c cs; fold G SB mu; clear; lia).
  assert (EF0 : F0 A rb = SB + c * 4294967296 + 3758096384 + mfa) by (unfold F0, free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize; fold nv c cs; fold G SB mfa; clear; lia).
  assert (PCr : PCE A rb = T + 208 + 80 * c) by (unfold PCE; fold nv c; fold G T; clear; lia).
  assert (G12 : SB mod 65536 = 0).
  { pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. unfold cfacts in CF. cbn zeta in CF. destruct CF as (_ & _ & _ & _ & _ & (X & _) & _). exact X. }
  assert (MU18 : mu mod 262144 = 0).
  { pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. unfold cfacts in CF. cbn zeta in CF. fold nv c cs in CF. destruct CF as (_ & _ & (X & _) & _). exact X. }
  assert (UM : U0 A rb mod 65536 = 0).
  { rewrite EU0. destruct (proj1 (Z.mod_divide mu 262144 ltac:(clear; lia)) MU18) as [q Hq]. destruct (proj1 (Z.mod_divide SB 65536 ltac:(clear; lia)) G12) as [q2 Hq2].
    rewrite Hq, Hq2. replace (q2 * 65536 + c * 4294967296 + q * 262144) with ((q2 + c * 65536 + q * 4) * 65536) by (clear; lia). apply Z_mod_mult. }
  assert (FM : F0 A rb mod 65536 = 0).
  { rewrite EF0. destruct (proj1 (Z.mod_divide mfa 262144 ltac:(clear; lia)) MF0) as [q Hq]. destruct (proj1 (Z.mod_divide SB 65536 ltac:(clear; lia)) G12) as [q2 Hq2].
    rewrite Hq, Hq2. replace (q2 * 65536 + c * 4294967296 + 3758096384 + q * 262144) with ((q2 + c * 65536 + 57344 + q * 4) * 65536) by (clear; lia). apply Z_mod_mult. }
  destruct (sh_run_nums SB (U0 A rb) ltac:(clear -G13; lia) ltac:(rewrite EU0; clear -C1 AU0; lia) ltac:(rewrite EU0; clear -C1 MU1; lia) G14 UM) as (QU1 & QU2 & QU3 & QU4).
  destruct (sh_run_nums SB (F0 A rb) ltac:(clear -G13; lia) ltac:(rewrite EF0; clear -C1 NF0 MF1; lia) ltac:(rewrite EF0; clear -C1 MF2; lia) G14 FM) as (QF1 & QF2 & QF3 & QF4).
  set (ri := region_info SB c) in *.
  assert (RIr : SB + 137438953472 + 128 <= ri /\ ri + 128 <= SB + 137438953472 + 4096).
  { unfold ri, region_info, kRegionInfoStride. rewrite kSpaceSize_val. clear -C1. lia. }

  set (ZQ := fun z : Z => (Sh (U0 A rb) <= z < Sh (U0 A rb) + 32768) \/ (U0 A rb <= z < U0 A rb + 262144)
                          \/ (b = true /\ Sh (F0 A rb) <= z < Sh (F0 A rb) + 32768) \/ (b = true /\ F0 A rb <= z < F0 A rb + 262144)
                          \/ (FAb A rb + 4 * nf <= z < FAb A rb + 4 * (nf + new))
                          \/ (PCE A rb + 16 <= z < PCE A rb + 16 + 4 * k) \/ (PCE A rb <= z < PCE A rb + 4) \/ (ri <= z < ri + 128)).
  assert (ZI : forall z, zoneR A rb (phQ b new k) z <-> ZQ z).
  { intros z. unfold zoneR, phQ, ZQ, revealedp, releasedp, kUserMapSize, kFreeArrayMapSize. cbn [ph_u ph_f ph_fill ph_pop ph_cnt ph_ri Nat.leb].
    unfold gh_nf. fold nv c cs nf new. fold G SB ri. replace (nf + new - new) with nf by (clear; lia).
    destruct b; cbn [Nat.leb]; split.
    - intros [[_ H]|[[_ H]|[[_ H]|[[_ H]|[[H _]|[H|[[_ H]|[_ H]]]]]]]].
      + left; exact H.
      + right; left; exact H.
      + right; right; left; split; [reflexivity | exact H].
      + right; right; right; left; split; [reflexivity | exact H].
      + right; right; right; right; left; exact H.
      + right; right; right; right; right; left; exact H.
      + right; right; right; right; right; right; left; exact H.
      + right; right; right; right; right; right; right; exact H.
    - intros [H|[H|[[_ H]|[[_ H]|[H|[H|[H|H]]]]]]].
      + left; split; [reflexivity | exact H].
      + right; left; split; [reflexivity | exact H].
      + right; right; left; split; [reflexivity | exact H].
      + right; right; right; left; split; [reflexivity | exact H].
      + right; right; right; right; left; split; [exact H | clear -N4; lia].
      + right; right; right; right; right; left; exact H.
      + right; right; right; right; right; right; left; split; [reflexivity | exact H].
      + right; right; right; right; right; right; right; split; [reflexivity | exact H].
    - intros [[_ H]|[[_ H]|[[X _]|[[X _]|[[H _]|[H|[[_ H]|[_ H]]]]]]]]; try discriminate X.
      + left; exact H.
      + right; left; exact H.
      + right; right; right; right; left; exact H.
      + right; right; right; right; right; left; exact H.
      + right; right; right; right; right; right; left; exact H.
      + right; right; right; right; right; right; right; exact H.
    - intros [H|[H|[[X _]|[[X _]|[H|[H|[H|H]]]]]]]; try discriminate X.
      + left; split; [reflexivity | exact H].
      + right; left; split; [reflexivity | exact H].
      + right; right; right; right; left; split; [exact H | clear -N4; lia].
      + right; right; right; right; right; left; exact H.
      + right; right; right; right; right; right; left; split; [reflexivity | exact H].
      + right; right; right; right; right; right; right; split; [reflexivity | exact H]. }
  assert (ZD : forall z, zoneR A rb (phQ b new k) z \/ ~ zoneR A rb (phQ b new k) z).
  { intros z. assert (D : ZQ z \/ ~ ZQ z).
    { unfold ZQ. destruct b.
      - assert (D' : (Sh (U0 A rb) <= z < Sh (U0 A rb) + 32768 \/ U0 A rb <= z < U0 A rb + 262144 \/ Sh (F0 A rb) <= z < Sh (F0 A rb) + 32768 \/ F0 A rb <= z < F0 A rb + 262144
                        \/ FAb A rb + 4 * nf <= z < FAb A rb + 4 * (nf + new) \/ PCE A rb + 16 <= z < PCE A rb + 16 + 4 * k \/ PCE A rb <= z < PCE A rb + 4 \/ ri <= z < ri + 128)
                       \/ ~ (Sh (U0 A rb) <= z < Sh (U0 A rb) + 32768 \/ U0 A rb <= z < U0 A rb + 262144 \/ Sh (F0 A rb) <= z < Sh (F0 A rb) + 32768 \/ F0 A rb <= z < F0 A rb + 262144
                        \/ FAb A rb + 4 * nf <= z < FAb A rb + 4 * (nf + new) \/ PCE A rb + 16 <= z < PCE A rb + 16 + 4 * k \/ PCE A rb <= z < PCE A rb + 4 \/ ri <= z < ri + 128)) by (clear; lia).
        destruct D' as [D'|D']; [left | right]; [clear -D'; tauto | intros X; apply D'; clear -X; tauto].
      - assert (D' : (Sh (U0 A rb) <= z < Sh (U0 A rb) + 32768 \/ U0 A rb <= z < U0 A rb + 262144
                        \/ FAb A rb + 4 * nf <= z < FAb A rb + 4 * (nf + new) \/ PCE A rb + 16 <= z < PCE A rb + 16 + 4 * k \/ PCE A rb <= z < PCE A rb + 4 \/ ri <= z < ri + 128)
                       \/ ~ (Sh (U0 A rb) <= z < Sh (U0 A rb) + 32768 \/ U0 A rb <= z < U0 A rb + 262144
                        \/ FAb A rb + 4 * nf <= z < FAb A rb + 4 * (nf + new) \/ PCE A rb + 16 <= z < PCE A rb + 16 + 4 * k \/ PCE A rb <= z < PCE A rb + 4 \/ ri <= z < ri + 128)) by (clear; lia).
        destruct D' as [D'|D']; [left; clear -D'; tauto|]. right. intros X. apply D'. clear -X. destruct X as [X|[X|[[E _]|[[E _]|X]]]]; try discriminate E; tauto. }
    destruct D as [D|D]; [left; apply ZI; exact D | right; intros X; apply D; apply ZI; exact X]. }
  unfold rlink in HR. destruct HR as (L1 & L2 & L3 & L4 & L5 & L6).
  set (m0 := view segs (rm rb)) in *. set (m := view segs (rm r)) in *.

  unfold mlink in HM. cbn zeta in HM. unfold phQ in HM. cbn [ph_u ph_f] in HM.
  destruct HM as (M1 & M2 & M3 & M4 & M5 & M6 & tp1 & M7 & M8 & M9 & M10).
  assert (ECF : committed (if b then 3%nat else 0%nat) = b) by (destruct b; reflexivity).
  assert (ERF : revealedp (if b then 3%nat else 0%nat) = b) by (destruct b; reflexivity).
  rewrite ECF in M5, M6, M10. rewrite ERF in M8, M9, M10. change (committed 3) with true in M5, M6, M10. change (revealedp 3) with true in M8, M9, M10.
  rewrite refillA_setcls. change (nth (Z.to_nat c) (aa_cls A) cs_empty) with cs.
  eapply proj1. apply (class_rebuildC [] [] OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c3.DrainF.cst_ok_nil OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c3.DrainF.xgl_ok_nil A rb r tp0 tp md0 md c (refill_cs c cs) (zoneR A rb (phQ b new k)) HA C1 Hini); change (nthZ (aa_cls A) c cs_empty) with cs; fold c cs; fold G; fold SB T; fold nf mu.
  - exact HPR.
  - rewrite X5. fold au. clear -N4 S1. nia.
  - rewrite X6. clear; lia.
  - rewrite X7. fold mfa. destruct b; clear; lia.
  - rewrite X2. destruct (kchunks_facts c C1) as (_ & K2 & _). fold k in K2. clear -K1 K2. lia.
  - exact ZD.
  -
    intros z HZ. apply ZI in HZ. unfold envR. unfold ZQ in HZ. rewrite EU0, EF0, FAr, PCr in HZ. rewrite EU0 in QU3, QU4. rewrite EF0 in QF3, QF4.
    pose proof (Geometry.Sh_mono (SB + c * 4294967296 + mu) (SB + c * 4294967296 + 3758096384 + mfa) ltac:(clear -MU1 NF0 MF1; lia)) as SM1.
    pose proof (Geometry.Sh_mono (SB + c * 4294967296 + mu + 262144) (SB + c * 2 ^ 32 + 2 ^ 32) ltac:(clear -MU1; lia)) as SM2.
    pose proof (Geometry.Sh_mono (SB + c * 4294967296 + 3758096384 + mfa + 262144) (SB + c * 2 ^ 32 + 2 ^ 32) ltac:(clear -MF2; lia)) as SM3.
    replace (SB + c * 2 ^ 32 + mu) with (SB + c * 4294967296 + mu) by (clear; lia).
    destruct HZ as [X|[X|[[_ X]|[[_ X]|[X|[X|[X|X]]]]]]].
    + right; right; right; right; right. clear -X QU4 SM2. lia.
    + right; right; right; right; left. clear -X MU1. lia.
    + right; right; right; right; right. clear -X QF4 SM1 SM3. lia.
    + right; right; right; left. clear -X MF1 MF2. lia.
    + right; right; right; left. clear -X N4 MF1 MF2. lia.
    + right; right; left. clear -X K1. lia.
    + right; left. clear -X. lia.
    + left. unfold ri, region_info, kRegionInfoStride in X. rewrite kSpaceSize_val in X. clear -X. lia.
  - intros z Hz. exact (L1 z Hz).
  - intros z Hz. pose proof (L2 z Hz) as D. change (exists b0, m z = Some b0). destruct (m z) as [b0|]; [exists b0; reflexivity | contradiction].
  - exact HRM.
  - exact (proj1 (L6 eq_refl)).
  - exact (proj1 (proj2 (L6 eq_refl))).
  - exact (proj1 (proj2 (proj2 (L6 eq_refl)))).
  - exact (proj1 (proj2 (proj2 (proj2 (L6 eq_refl))))).
  - exact (proj1 (proj2 (proj2 (proj2 (proj2 (L6 eq_refl)))))).
  - exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (L6 eq_refl))))))).
  - exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (L6 eq_refl)))))))).
  - exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (L6 eq_refl)))))))).
  -
    rewrite XFA. intros i x Hi. pose proof (nth_error_Some_lt _ _ _ Hi) as Li. rewrite firstn_length_le in Li by (clear -LP' KN NF0 K1; lia).
    rewrite nth_error_firstn in Hi. replace (i <? Z.to_nat (nf + new - k))%nat with true in Hi by (symmetry; apply Nat.ltb_lt; exact Li).
    pose proof (P_HSRC A rb tp0 md0 W st rho HE PF (phQ b new k) m eq_refl ltac:(cbn [ph_pop phQ]; clear -K1; lia) (conj L1 (conj L2 (conj L3 (conj L4 (conj L5 L6))))) (Z.of_nat i)
                  ltac:(fold nv c cs fP; rewrite LP'; clear -Li KN NF0 K1; lia)) as CE.
    fold nv c cs fP in CE. rewrite Nat2Z.id in CE. rewrite (nth_error_nth _ _ 0 Hi) in CE.
    replace (free_array SB c) with (FAb A rb) by (unfold FAb; fold nv c; reflexivity). exact CE.
  - rewrite X2. replace (T + 208 + 80 * c) with (PCE A rb) by (rewrite PCr; reflexivity). exact (L5 eq_refl).
  - intros i x Hi. pose proof (nth_error_Some_lt _ _ _ Hi) as Li. rewrite <- (Nat2Z.id (length (cs_cache (refill_cs c cs)))) in Li. rewrite X2 in Li.
    pose proof (L4 (Z.of_nat i)) as CE. cbn [ph_pop phQ] in CE. specialize (CE ltac:(clear -Li K1; lia)).
    rewrite Nat2Z.id in CE. fold nv c cs in CE. rewrite (nth_error_nth _ _ 0 Hi) in CE.
    replace (T + 208 + 80 * c + 16 + 4 * Z.of_nat i) with (PCE A rb + 16 + 4 * Z.of_nat i) by (rewrite PCr; reflexivity). exact CE.
  - rewrite X6. intros z Hz. apply ZI. right; left. rewrite EU0. unfold region_beg, kRegionSize in Hz. clear -Hz. lia.
  - rewrite X6. intros z Hz. apply ZI. left. rewrite EU0 in QU4 |- *. unfold region_beg, kRegionSize in Hz.
    replace (SB + c * 2 ^ 32 + mu) with (SB + c * 4294967296 + mu) in Hz by (clear; lia).
    replace (SB + c * 2 ^ 32 + (mu + 262144)) with (SB + c * 4294967296 + mu + 262144) in Hz by (clear; lia). clear -Hz QU4. lia.
  - rewrite X7. fold mfa. intros z Hz. destruct b; [|exfalso; clear -Hz; lia]. apply ZI. right; right; right; left. split; [reflexivity|].
    rewrite EF0. unfold free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize in Hz. clear -Hz. lia.
  -
    change (subF A rb b (subU A rb true (vm_noaccess (m_vmmaps md0))))
      with (sub2 true (U0 A rb) (U0 A rb + kUserMapSize) b (F0 A rb) (F0 A rb + kFreeArrayMapSize) (vm_noaccess (m_vmmaps md0))) in M5.
    change (subF A rb b (subU A rb true (m_vm_lazy md0)))
      with (sub2 true (U0 A rb) (U0 A rb + kUserMapSize) b (F0 A rb) (F0 A rb + kFreeArrayMapSize) (m_vm_lazy md0)) in M6.
    rewrite M7.
    apply (model_inv_sub2 A (refillA A c) tp0 tp1 md0 md true b (U0 A rb) (U0 A rb + kUserMapSize) (F0 A rb) (F0 A rb + kFreeArrayMapSize)); try reflexivity; try assumption.
    + unfold kUserMapSize. clear; lia.
    + unfold kFreeArrayMapSize. clear; lia.
    + fold G SB. rewrite EU0. clear -C1 AU0. lia.
    + fold G SB. rewrite EU0, kSpaceSize_val. unfold kUserMapSize. clear -C1 MU1. lia.
    + fold G SB. rewrite EF0. clear -C1 NF0 MF1. lia.
    + fold G SB. rewrite EF0, kSpaceSize_val. unfold kFreeArrayMapSize. clear -C1 MF2. lia.
    + fold G SB. unfold HIGH_SHADOW_END. clear -G13. lia.
    + intros p Hp. destruct (M8 p Hp) as [_ [[_ (j & Hj & Ej)]|[_ (j & Hj & Ej)]]]; rewrite Ej; unfold band_page; right; unfold HIGH_SHADOW_BEG, HIGH_SHADOW_END, PG.
      * clear -Hj QU2 QU3. lia.
      * clear -Hj QF2 QF3. lia.
    +
      destruct HMI0 as (_ & PB0 & _). rewrite <- M7. unfold kUserMapSize, kFreeArrayMapSize in M10.
      destruct b; clear -PB0 M10 CEQ; lia.
  -
    rewrite M7. apply (bandtp_grow m tp0).
    + eapply bandtp_mono; [|exact HB0]. intros z _ Hd. fold m0 in Hd. destruct (ZD z) as [ZIz|ZOz]; [exact (L2 z ZIz) | rewrite (L1 z ZOz); exact Hd].
    + intros p Hp. apply in_app_or in Hp as [Hp|Hp]; [|left; exact Hp]. right. intros _ z Hz.
      assert (ZIz : zoneR A rb (phQ b new k) z).
      { apply ZI. destruct (M8 p Hp) as [_ [[_ (j & Hj & Ej)]|[Eb' (j & Hj & Ej)]]]; rewrite Ej in Hz; unfold PG in Hz.
        - left. clear -Hz Hj. lia.
        - right; right; left. split; [exact Eb' | clear -Hz Hj; lia]. }
      pose proof (L2 z ZIz) as D. destruct (m z) as [b0|]; [exists b0; reflexivity | contradiction].
Qed.
End RQ.
End RebuildQQ.

(* [comment removed for export] *)
Module DrainIg1.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "la_state"; "ax_S"; "leafA"; "sym_runA"; "ax_X"; "axst"; "entailsA"; "@Corelib.Init.Datatypes"; "true"; "cons"; "nil"; "bool"; "list"; "prod"; "Some"; "option"; "pair"; "app"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "sprop"; "ss_next"; "SLit"; "ss_objs"; "swf"; "ss_facts"; "SAlu"; "reg_sv"; "ss_lenient"; "sprop_below"; "ss_pc"; "sv_below"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cb.DrainIg1"; "N"; "lm_0"; "lx_0"; "FUEL"; "rl"; "l1_0"; "l5_0"; "l5_1"; "l2_0"; "dm"; "l60_0"; "l60_1"; "l60_2"; "l61_0"; "l61_1"; "l61_2"; "cr_00"; "cr_01"; "cr_02"; "cr_10"; "cr_11"; "cr_12"; "s_00"; "s_01"; "s_02"; "s_10"; "s_11"; "s_12"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR"; "beg2"; "cX"; "nobj"; "vMFA"; "cFm"; "relM"; "rMS"; "ri_e"; "sMS"; "vRI"; "idx_rot"; "rotM"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c3.DrainF"; "rstD"; "O_riX"; "ri_hasD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocR10"; "cMc"; "dMSf"; "cMr"; "a2_e"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c7.DrainG6"; "leaf_okG"; "run_okG"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "eqb"; "@Corelib.Init.Nat"; "sub"; "@Corelib.Lists.ListDef"; "firstn"; "map"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "instr"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bu.DrainG4"; "cCD"; "cG0"; "mid_okG"; "XFG"; "rupD_e"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.DrainS"; "NXD"; "O_cntD"; "O_dstD"; "dst_cells"; "JD"; "JLD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.DrainSG"; "L_dh_g"; "Pre_dh_g"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "F_sp_high"; "KcA"; "Kc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cf.DrainG2"; "SKELG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR"; "commit_post"; "memset_post"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3"; "skel"; "inclb"; "@Stdlib.Lists.List"; "In"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineMallocR9"; "O_piece"; "O_shp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "nodupN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "call_checkA"; "entails_frA"; "@Corelib.Init.Peano"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "instr_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget"; "LIMIT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DrainTR"; "TRokD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "budget_bound";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bp.SpineMallocR11"; "a0_e"; "@Stdlib.Arith.PeanoNat.Nat"; "leb"; "@Stdlib.ZArith.BinInt.Z"; "le"; "@stdpp.bitvector.definitions"; "bv"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillTR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bi.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require DrainModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require DrainTR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineMallocR9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocR10 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bp.SpineMallocR11 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DrainModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.DrainS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.DrainSG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DrainTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c3.DrainF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c8.DrainG1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cf.DrainG2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bu.DrainG4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c7.DrainG6.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition N : Z := 1.
Definition FUEL : nat := 6000%nat.
Lemma W_0 : ltac2:(tb__ "0|0|
S0SbS19S2S5fS22A1A1A1S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_0 : ltac2:(tb__ "0|4|
S0SfSdScSdS13S13A2M0A1M1ScS15A1M2A2M3A1S5dS2S6aS22A1A1S2S5fS22A1A1A2SeG3S10G1G2SaG0A1S61A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Definition R_1__R : option (list leafA) := ltac2:(tb__ "0|0|
S4S4eS25S9S4aZ3ef90SaS4aA1A3S5fS22A1S8A5").
Local Strategy expand [R_1__R].
Definition l1 := Eval vm_compute in ((fun ro1__ : option (list leafA) => (match ro1__ with Some l => l | None => [] end)) R_1__R).
Definition l1_0 := Eval vm_compute in (nth 0 l1 (mkLeafA (cG0 N) RsCut)).
Lemma R_1 : ltac2:(tb__ "0|1|
S0SfScS3A1M0A1S4S4eS25S9S4aZ3ef90SaS4aA1A3S5fS22A1S8A5SeG0S9S3S27SaS3A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_1__R <: R_1__R = Some [l1_0]). Qed.
Lemma LN_1 : ltac2:(tb__ "0|0|
S0SbS1dS2S5fS22A1A1A1S12A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Definition R_a__R : option (list leafA) := ltac2:(tb__ "0|0|
S4S4eS25S9S4aZ3f270SaS4aA1A3S4bS1S27A1U8A2S8A5").
Local Strategy expand [R_a__R].
Definition l2 := Eval vm_compute in ((fun ro2__ : option (list leafA) => (match ro2__ with Some l => l | None => [] end)) R_a__R).
Definition l2_0 := Eval vm_compute in (nth 0 l2 (mkLeafA (rstD (la_state l1_0) 8) RsCut)).
Lemma W_a : ltac2:(tb__ "0|0|
S0SbS19S2S4bS1S27A1U8A2A1A1S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_a : ltac2:(tb__ "0|5|
S0SfSdScSdS13S13A2M0A1M1ScS15A1M2A2M3A1S5dS2S1S27A1M4A1S2S4bG4U8A2A1A2SeG3S10G1G2S9G0S10S13S13S45S47A4SaG0A1A3SaS15A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_a : ltac2:(tb__ "0|1|
S0SbS56S16S2S4bS1S27A1M0U8A2A1A1S16S2G0A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma LN_a : ltac2:(tb__ "0|0|
S0SbS1dS2S4bS1S27A1U8A2A1A1S12A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NL_a : ltac2:(tb__ "0|0|
S0SbS55Pf0S16S2S4bS1S27A1U8A2A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_a : ltac2:(tb__ "0|1|
S0SfScS3A1M0A1S4S4eS25S9S4aZ3f270SaS4aA1A3S4bS1S27A1U8A2S8A5SeG0S9S3S2aSaS3A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_a__R <: R_a__R = Some [l2_0]). Qed.
Lemma m_a : ltac2:(tb__ "0|0|
S60S25U8S9S4aZ3f270SaS4aA1A3S6S0S6R1S1S2aA1A3LL';S1S27A1A5").
Proof.
  split; [exact W_a|]. split; [exact D_a|]. split; [exact NXe_a|]. split; [exact LN_a|]. split; [exact NL_a|].
  exists [l2_0]. split; [exact R_a|]. intros L' HIn. repeat (destruct HIn as [<-|HIn]); [reflexivity | destruct HIn].
Qed.
Lemma W_fm : ltac2:(tb__ "0|0|
S0SbS19S2S42S1S2aA1A1A1A1S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_fm : ltac2:(tb__ "0|5|
S0SfSdScSdS13S13A2M0A1M1ScS15A1M2A2M3A1S5dS2S1S2aA1M4A1S2S42G4A1A1A2SeG3S10G1G2S9G0S10S13S13S62S22A1S1bS5aS41S17Z40000A1A3A4SaG0A1A3SaS15A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Definition R_x__R : option (list leafA) := ltac2:(tb__ "0|0|
S4S4eS25S9S4aZ7050cSaS4aA1A3S42S1S2aA1A1S8A5").
Local Strategy expand [R_x__R].
Definition lx := Eval vm_compute in ((fun ro3__ : option (list leafA) => (match ro3__ with Some l => l | None => [] end)) R_x__R).
Definition lx_0 := Eval vm_compute in (nth 0 lx (mkLeafA (cFm (la_state l2_0)) RsCut)).
Lemma R_x : ltac2:(tb__ "0|1|
S0SfScS3A1M0A1S4S4eS25S9S4aZ7050cSaS4aA1A3S42S1S2aA1A1S8A5SeG0S9S3S24SaS3A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_x__R <: R_x__R = Some [lx_0]). Qed.
Lemma LN_0 : ltac2:(tb__ "0|0|
S0SbS1dS2S42S1S2aA1A1A1A1S12A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_0 : ltac2:(tb__ "0|0|
S0SbS55Pf0S16S2S42S1S2aA1A1A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_x : ltac2:(tb__ "0|0|
S0SbS19S2S3fS1S24A1S3eA2A1A1S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_x : ltac2:(tb__ "0|5|
S0SfSdScSdS13S13A2M0A1M1ScS15A1M2A2M3A1S5dS2S1S24A1M4A1S2S3fG4S3eA2A1A2SeG3S10G1G2S9G0S10S13S13S88S3eA1S3eA4SaG0A1A3SaS15A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma SK_x : ltac2:(tb__ "0|1|
S0ScSdSdS13S13A2S13A2M0A1S59S14G0S72S18S2S3fS1S24A1S3eA2A1A1A4S6fS22SaS14A1A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_xb : ltac2:(tb__ "0|0|
S0SbS73S9S15S6bSaS15A1A3S1aS2S3fS1S24A1S3eA2A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XF_x : ltac2:(tb__ "0|0|
S74S15S6bS1aS2S3fS1S24A1S3eA2A1A1A3").
Proof. exact (inclb_incl _ _ XF_xb F_sp_high (or_introl eq_refl)). Qed.
Lemma XX_x : ltac2:(tb__ "0|1|
S0ScSdS13S13A2M0A1S5S3fS1S24A1S3eA2A1SaG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NX_x : ltac2:(tb__ "0|0|
S0SbS55Pf0S16S2S3fS1S24A1S3eA2A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma IC_x : ltac2:(tb__ "0|0|
S0SfS5bA1S82S4eS1fS2S3fS1S24A1S3eA2A1A1A2SeS5bS5cA2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R17_x : ltac2:(tb__ "0|0|
S0S13S1cS2S3fS1S24A1S3eA2A1Z11A2S17ZdeA1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R10_x : ltac2:(tb__ "0|0|
S0S13S1cS2S3fS1S24A1S3eA2A1ZaA2S3eA3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R11_x : ltac2:(tb__ "0|0|
S0S13S1cS2S3fS1S24A1S3eA2A1ZbA2S17Z40000A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R12_x : ltac2:(tb__ "0|0|
S0S13S1cS2S3fS1S24A1S3eA2A1ZcA2S17Z3A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R13_x : ltac2:(tb__ "0|0|
S0S13S1cS2S3fS1S24A1S3eA2A1ZdA2S17Z32A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R14_x : ltac2:(tb__ "0|0|
S0S13S1cS2S3fS1S24A1S3eA2A1ZeA2S17ZffffffffffffffffA1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R15_x : ltac2:(tb__ "0|0|
S0S13S1cS2S3fS1S24A1S3eA2A1ZfA2S17Z0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma BEL_x : ltac2:(tb__ "0|0|
S0SbS20S16S2S3fS1S24A1S3eA2A1A1S3eA2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Definition R_m__R : option (list leafA) := ltac2:(tb__ "0|0|
S4S4eS25S9S4aZde378SaS4aA1A3S70S3fS1S24A1S3eA2S3eZ40000A3S8A5").
Local Strategy expand [R_m__R].
Definition lm := Eval vm_compute in ((fun ro4__ : option (list leafA) => (match ro4__ with Some l => l | None => [] end)) R_m__R).
Definition lm_0 := Eval vm_compute in (nth 0 lm (mkLeafA (commit_post (cX (la_state lx_0) beg2) beg2 262144) RsCut)).
Lemma R_m : ltac2:(tb__ "0|1|
S0SfScS3A1M0A1S4S4eS25S9S4aZde378SaS4aA1A3S70S3fS1S24A1S3eA2S3eZ40000A3S8A5SeG0S9S3S23SaS3A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_m__R <: R_m__R = Some [lm_0]). Qed.
Lemma LN_g : ltac2:(tb__ "0|0|
S0SbS1dS2S70S3fS1S24A1S3eA2S3eZ40000A3A1A1S12A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_g : ltac2:(tb__ "0|0|
S0SbS55Pf0S16S2S70S3fS1S24A1S3eA2S3eZ40000A3A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SK_m : ltac2:(tb__ "0|1|
S0ScSdSdS13S13A2S13A2M0A1S59S14G0S72S18S2S1S23A1A1A1A4S6fS22S9S14S76S3eA1SaS14A1A3A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_mb : ltac2:(tb__ "0|0|
S0SbS73S9S15S6bSaS15A1A3S1aS2S1S23A1A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XF_m : ltac2:(tb__ "0|0|
S74S15S6bS1aS2S1S23A1A1A1A3").
Proof. exact (inclb_incl _ _ XF_mb F_sp_high (or_introl eq_refl)). Qed.
Lemma XX_m : ltac2:(tb__ "0|1|
S0ScSdS13S13A2M0A1S5S1S23A1A1SaG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma W_mr : ltac2:(tb__ "0|0|
S0SbS19S2S51S1S23A1A1A1A1S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_mr : ltac2:(tb__ "0|5|
S0SfSdScSdS13S13A2M0A1M1ScS15A1M2A2M3A1S5dS2S1S23A1M4A1S2S51G4A1A1A2SeG3S10G1G2S9G0S10S13S13S52S3eA1S17Z8000A1A4SaG0A1A3SaS15A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma W_mc : ltac2:(tb__ "0|0|
S0SbS19S2S4fS1S23A1S3eA2A1A1S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma E_ms : ltac2:(tb__ "0|2|
S0SfScS14A1M0A1S7fS4fS1S23A1S3eA2M1S78S46G1A1A3SeG0S44G1A1A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma CHK_ms : ltac2:(tb__ "0|1|
S0SbS7eS4fS1S23A1S3eA2M0S78S46G0A1S44G0A1S59S3S6S1S79A4A5S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NF_ms : ltac2:(tb__ "0|0|
S0SbS55S81S16S2S4fS1S23A1S3eA2A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NX_ms : ltac2:(tb__ "0|0|
S0SbS55Pf0S16S2S4fS1S23A1S3eA2A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBC_ms : ltac2:(tb__ "0|1|
S0SbS75S15S1eS16S2S4fS1S23A1S3eA2A1M0A1A1S1aG0A1A3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT_ms : ltac2:(tb__ "0|1|
S0SbS75S15S1eS16S2S71S4fS1S23A1S3eA2M0S46G0A1S44G0A1A3A1A1A1S1aS2G0A1A1A3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Definition dm := Eval vm_compute in (dMSf (cMc (la_state lm_0) beg2)).
Lemma DM_eq : ltac2:(tb__ "0|0|
S0S6S50S4fS1S23A1S3eA2A1S2bA3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma ND_rb : ltac2:(tb__ "0|0|
S0SbS7bS48S2bA1A1S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NO_rb : ltac2:(tb__ "0|0|
S0SbS89U1S40S2bA1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma OB_rb : ltac2:(tb__ "0|1|
S0ScS14A1S18S2S49S2bA1A1A1M0S11S14S58S14S57S40S2bA1U2A2G0A3S9S14S76S3eA1S9S14S77S3eA1SaS14A1A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma ND_r : ltac2:(tb__ "0|0|
S0SbS7bS48S50S4fS1S23A1S3eA2A1A1A1S8A3"). Proof. rewrite DM_eq. exact ND_rb. Qed.
Lemma NO_r : ltac2:(tb__ "0|0|
S80U1S40S50S4fS1S23A1S3eA2A1A1A2"). Proof. rewrite DM_eq. apply Nat.leb_le. exact NO_rb. Qed.
Lemma OB_r : ltac2:(tb__ "0|2|
S0ScS14A1S18S2S49S50S4fS1S23A1S3eA2A1M0A1A1A1M1S11S14S58S14S57S40G0A1U2A2G1A3S9S14S76S3eA1S9S14S77S3eA1SaS14A1A3A3A3A3"). Proof. rewrite DM_eq. exact OB_rb. Qed.
Definition rl := Eval vm_compute in (relM dm).
Lemma RL_eq : ltac2:(tb__ "0|0|
S0S6S43S50S4fS1S23A1S3eA2A1A1S26A3"). Proof. rewrite DM_eq. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma SK_cb : ltac2:(tb__ "0|1|
S0ScSdSdS13S13A2S13A2M0A1S59S14G0S72S18S2S26A1A1A4S6fS22SaS14A1A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_cbb : ltac2:(tb__ "0|0|
S0SbS73S9S15S6bSaS15A1A3S1aS2S26A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XF_cb : ltac2:(tb__ "0|0|
S74S15S6bS1aS2S26A1A1A3").
Proof. exact (inclb_incl _ _ XF_cbb F_sp_high (or_introl eq_refl)). Qed.
Lemma XX_cb : ltac2:(tb__ "0|1|
S0ScSdS13S13A2M0A1S5S26A1SaG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma W_cb : ltac2:(tb__ "0|0|
S0SbS19S2S5eS22S26A2A1A1S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SK_c : ltac2:(tb__ "0|1|
S0ScSdSdS13S13A2S13A2M0A1S59S14G0S72S18S2S43S50S4fS1S23A1S3eA2A1A1A1A1A4S6fS22SaS14A1A2A3"). Proof. rewrite RL_eq. exact SK_cb. Qed.
Lemma XF_c : ltac2:(tb__ "0|0|
S74S15S6bS1aS2S43S50S4fS1S23A1S3eA2A1A1A1A1A3"). Proof. rewrite RL_eq. exact XF_cb. Qed.
Lemma XX_c : ltac2:(tb__ "0|1|
S0ScSdS13S13A2M0A1S5S43S50S4fS1S23A1S3eA2A1A1A1SaG0A1A3"). Proof. rewrite RL_eq. exact XX_cb. Qed.
Lemma W_c : ltac2:(tb__ "0|0|
S0SbS19S2S5eS22S43S50S4fS1S23A1S3eA2A1A1A2A1A1S8A3"). Proof. rewrite RL_eq. exact W_cb. Qed.
Definition R_5__R : option (list leafA) := ltac2:(tb__ "0|0|
S4S4eS25S9S4aZ3f440SaS4aA1A3S5eS22S26A2S8A5").
Local Strategy expand [R_5__R].
Definition l5 := Eval vm_compute in ((fun ro7__ : option (list leafA) => (match ro7__ with Some l => l | None => [] end)) R_5__R).
Definition l5_0 := Eval vm_compute in (nth 0 l5 (mkLeafA (cCD N rl) RsCut)).
Definition l5_1 := Eval vm_compute in (nth 1 l5 (mkLeafA (cCD N rl) RsCut)).
Definition R_b0__R : option (list leafA) := ltac2:(tb__ "0|0|
S4S4eS25S9S4aZ3ede4SaS4aA1A3S4bS1S28A1U16A2S8A5").
Local Strategy expand [R_b0__R].
Definition l60 := Eval vm_compute in ((fun ro5__ : option (list leafA) => (match ro5__ with Some l => l | None => [] end)) R_b0__R).
Definition l60_0 := Eval vm_compute in (nth 0 l60 (mkLeafA (rstD (la_state l5_0) 22) RsCut)).
Definition l60_1 := Eval vm_compute in (nth 1 l60 (mkLeafA (rstD (la_state l5_0) 22) RsCut)).
Definition l60_2 := Eval vm_compute in (nth 2 l60 (mkLeafA (rstD (la_state l5_0) 22) RsCut)).
Definition cr_00 := Eval vm_compute in (ob_cells (nth (nobj (la_state l60_0) - 2) (ss_objs (ax_S (la_state l60_0))) O_pcc0)).
Definition s_00 := Eval vm_compute in (infer_sub NXD (ax_S (la_state l60_0)) (ax_S (L_dh_g N))).
Lemma XX_00 : ltac2:(tb__ "0|1|
S0ScSdS13S13A2M0A1S5S1S2cA1A1SaG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_00 : ltac2:(tb__ "0|2|
S0ScS14A1S18S2S1S2cA1M0A1A1M1S11S14S58S14S57S40G0A1U3A2G1A3S9S14S64S22A1S9S14S4cS32A1S9S14S65S22S66S22A1A2SaS14A1A3A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_00 : ltac2:(tb__ "0|0|
S0SbS4dS22S1bS5aS41S17Z40000A1A3S32A3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_00 : ltac2:(tb__ "0|0|
S0SbS7S1S2cA1S69S22A1S38A3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_00 : ltac2:(tb__ "0|0|
S0SbS6eS38S63A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma k_00 : ltac2:(tb__ "0|0|
S53S22S1S2cA1A2").
Proof. exists cr_00, s_00. exact (conj XX_00 (conj OB_00 (conj RI_00 (conj ENT_00 SID_00)))). Qed.
Definition cr_01 := Eval vm_compute in (ob_cells (nth (nobj (la_state l60_1) - 2) (ss_objs (ax_S (la_state l60_1))) O_pcc0)).
Definition s_01 := Eval vm_compute in (infer_sub NXD (ax_S (la_state l60_1)) (ax_S (L_dh_g N))).
Lemma XX_01 : ltac2:(tb__ "0|1|
S0ScSdS13S13A2M0A1S5S1S2dA1A1SaG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_01 : ltac2:(tb__ "0|2|
S0ScS14A1S18S2S1S2dA1M0A1A1M1S11S14S58S14S57S40G0A1U3A2G1A3S9S14S64S22A1S9S14S4cS33A1S9S14S65S22S66S22A1A2SaS14A1A3A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_01 : ltac2:(tb__ "0|0|
S0SbS4dS22S1bS5aS41S17Z40000A1A3S33A3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_01 : ltac2:(tb__ "0|0|
S0SbS7S1S2dA1S69S22A1S39A3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_01 : ltac2:(tb__ "0|0|
S0SbS6eS39S63A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma k_01 : ltac2:(tb__ "0|0|
S53S22S1S2dA1A2").
Proof. exists cr_01, s_01. exact (conj XX_01 (conj OB_01 (conj RI_01 (conj ENT_01 SID_01)))). Qed.
Definition cr_02 := Eval vm_compute in (ob_cells (nth (nobj (la_state l60_2) - 2) (ss_objs (ax_S (la_state l60_2))) O_pcc0)).
Definition s_02 := Eval vm_compute in (infer_sub NXD (ax_S (la_state l60_2)) (ax_S (L_dh_g N))).
Lemma XX_02 : ltac2:(tb__ "0|1|
S0ScSdS13S13A2M0A1S5S1S2eA1A1SaG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_02 : ltac2:(tb__ "0|2|
S0ScS14A1S18S2S1S2eA1M0A1A1M1S11S14S58S14S57S40G0A1U3A2G1A3S9S14S64S22A1S9S14S4cS34A1S9S14S65S22S66S22A1A2SaS14A1A3A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_02 : ltac2:(tb__ "0|0|
S0SbS4dS22S1bS5aS41S17Z40000A1A3S34A3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_02 : ltac2:(tb__ "0|0|
S0SbS7S1S2eA1S69S22A1S3aA3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_02 : ltac2:(tb__ "0|0|
S0SbS6eS3aS63A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma k_02 : ltac2:(tb__ "0|0|
S53S22S1S2eA1A2").
Proof. exists cr_02, s_02. exact (conj XX_02 (conj OB_02 (conj RI_02 (conj ENT_02 SID_02)))). Qed.
Lemma W_b0 : ltac2:(tb__ "0|0|
S0SbS19S2S4bS1S28A1U16A2A1A1S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_b0 : ltac2:(tb__ "0|5|
S0SfSdScSdS13S13A2M0A1M1ScS15A1M2A2M3A1S5dS2S1S28A1M4A1S2S4bG4U16A2A1A2SeG3S10G1G2S9G0S10S13S13S45S47A4SaG0A1A3SaS15A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_b0 : ltac2:(tb__ "0|1|
S0SbS56S16S2S4bS1S28A1M0U16A2A1A1S16S2G0A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma LN_b0 : ltac2:(tb__ "0|0|
S0SbS1dS2S4bS1S28A1U16A2A1A1S12A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NL_b0 : ltac2:(tb__ "0|0|
S0SbS55Pf0S16S2S4bS1S28A1U16A2A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_b0 : ltac2:(tb__ "0|1|
S0SfScS3A1M0A1S4S4eS25S9S4aZ3ede4SaS4aA1A3S4bS1S28A1U16A2S8A5SeG0S9S3S2cS9S3S2dS9S3S2eSaS3A1A3A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_b0__R <: R_b0__R = Some [l60_0; l60_1; l60_2]). Qed.
Lemma m_b0 : ltac2:(tb__ "0|0|
S60S25U16S9S4aZ3ede4SaS4aA1A3S53S22A1S1S28A1A5").
Proof.
  split; [exact W_b0|]. split; [exact D_b0|]. split; [exact NXe_b0|]. split; [exact LN_b0|]. split; [exact NL_b0|].
  exists [l60_0; l60_1; l60_2]. split; [exact R_b0|]. intros L' HIn. repeat (destruct HIn as [<-|HIn]); [exact k_00 | exact k_01 | exact k_02 | destruct HIn].
Qed.
Definition R_b1__R : option (list leafA) := ltac2:(tb__ "0|0|
S4S4eS25S9S4aZ3ede4SaS4aA1A3S4bS1S29A1U16A2S8A5").
Local Strategy expand [R_b1__R].
Definition l61 := Eval vm_compute in ((fun ro6__ : option (list leafA) => (match ro6__ with Some l => l | None => [] end)) R_b1__R).
Definition l61_0 := Eval vm_compute in (nth 0 l61 (mkLeafA (rstD (la_state l5_1) 22) RsCut)).
Definition l61_1 := Eval vm_compute in (nth 1 l61 (mkLeafA (rstD (la_state l5_1) 22) RsCut)).
Definition l61_2 := Eval vm_compute in (nth 2 l61 (mkLeafA (rstD (la_state l5_1) 22) RsCut)).
Definition cr_10 := Eval vm_compute in (ob_cells (nth (nobj (la_state l61_0) - 2) (ss_objs (ax_S (la_state l61_0))) O_pcc0)).
Definition s_10 := Eval vm_compute in (infer_sub NXD (ax_S (la_state l61_0)) (ax_S (L_dh_g N))).
Lemma XX_10 : ltac2:(tb__ "0|1|
S0ScSdS13S13A2M0A1S5S1S2fA1A1SaG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_10 : ltac2:(tb__ "0|2|
S0ScS14A1S18S2S1S2fA1M0A1A1M1S11S14S58S14S57S40G0A1U3A2G1A3S9S14S64S22A1S9S14S4cS35A1S9S14S65S22S66S22A1A2SaS14A1A3A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_10 : ltac2:(tb__ "0|0|
S0SbS4dS22S1bS5aS41S17Z40000A1A3S35A3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_10 : ltac2:(tb__ "0|0|
S0SbS7S1S2fA1S69S22A1S3bA3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_10 : ltac2:(tb__ "0|0|
S0SbS6eS3bS63A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma k_10 : ltac2:(tb__ "0|0|
S53S22S1S2fA1A2").
Proof. exists cr_10, s_10. exact (conj XX_10 (conj OB_10 (conj RI_10 (conj ENT_10 SID_10)))). Qed.
Definition cr_11 := Eval vm_compute in (ob_cells (nth (nobj (la_state l61_1) - 2) (ss_objs (ax_S (la_state l61_1))) O_pcc0)).
Definition s_11 := Eval vm_compute in (infer_sub NXD (ax_S (la_state l61_1)) (ax_S (L_dh_g N))).
Lemma XX_11 : ltac2:(tb__ "0|1|
S0ScSdS13S13A2M0A1S5S1S30A1A1SaG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_11 : ltac2:(tb__ "0|2|
S0ScS14A1S18S2S1S30A1M0A1A1M1S11S14S58S14S57S40G0A1U3A2G1A3S9S14S64S22A1S9S14S4cS36A1S9S14S65S22S66S22A1A2SaS14A1A3A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_11 : ltac2:(tb__ "0|0|
S0SbS4dS22S1bS5aS41S17Z40000A1A3S36A3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_11 : ltac2:(tb__ "0|0|
S0SbS7S1S30A1S69S22A1S3cA3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_11 : ltac2:(tb__ "0|0|
S0SbS6eS3cS63A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma k_11 : ltac2:(tb__ "0|0|
S53S22S1S30A1A2").
Proof. exists cr_11, s_11. exact (conj XX_11 (conj OB_11 (conj RI_11 (conj ENT_11 SID_11)))). Qed.
Definition cr_12 := Eval vm_compute in (ob_cells (nth (nobj (la_state l61_2) - 2) (ss_objs (ax_S (la_state l61_2))) O_pcc0)).
Definition s_12 := Eval vm_compute in (infer_sub NXD (ax_S (la_state l61_2)) (ax_S (L_dh_g N))).
Lemma XX_12 : ltac2:(tb__ "0|1|
S0ScSdS13S13A2M0A1S5S1S31A1A1SaG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_12 : ltac2:(tb__ "0|2|
S0ScS14A1S18S2S1S31A1M0A1A1M1S11S14S58S14S57S40G0A1U3A2G1A3S9S14S64S22A1S9S14S4cS37A1S9S14S65S22S66S22A1A2SaS14A1A3A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_12 : ltac2:(tb__ "0|0|
S0SbS4dS22S1bS5aS41S17Z40000A1A3S37A3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_12 : ltac2:(tb__ "0|0|
S0SbS7S1S31A1S69S22A1S3dA3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_12 : ltac2:(tb__ "0|0|
S0SbS6eS3dS63A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma k_12 : ltac2:(tb__ "0|0|
S53S22S1S31A1A2").
Proof. exists cr_12, s_12. exact (conj XX_12 (conj OB_12 (conj RI_12 (conj ENT_12 SID_12)))). Qed.
Lemma W_b1 : ltac2:(tb__ "0|0|
S0SbS19S2S4bS1S29A1U16A2A1A1S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_b1 : ltac2:(tb__ "0|5|
S0SfSdScSdS13S13A2M0A1M1ScS15A1M2A2M3A1S5dS2S1S29A1M4A1S2S4bG4U16A2A1A2SeG3S10G1G2S9G0S10S13S13S45S47A4SaG0A1A3SaS15A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_b1 : ltac2:(tb__ "0|1|
S0SbS56S16S2S4bS1S29A1M0U16A2A1A1S16S2G0A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma LN_b1 : ltac2:(tb__ "0|0|
S0SbS1dS2S4bS1S29A1U16A2A1A1S12A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NL_b1 : ltac2:(tb__ "0|0|
S0SbS55Pf0S16S2S4bS1S29A1U16A2A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_b1 : ltac2:(tb__ "0|1|
S0SfScS3A1M0A1S4S4eS25S9S4aZ3ede4SaS4aA1A3S4bS1S29A1U16A2S8A5SeG0S9S3S2fS9S3S30S9S3S31SaS3A1A3A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_b1__R <: R_b1__R = Some [l61_0; l61_1; l61_2]). Qed.
Lemma m_b1 : ltac2:(tb__ "0|0|
S60S25U16S9S4aZ3ede4SaS4aA1A3S53S22A1S1S29A1A5").
Proof.
  split; [exact W_b1|]. split; [exact D_b1|]. split; [exact NXe_b1|]. split; [exact LN_b1|]. split; [exact NL_b1|].
  exists [l61_0; l61_1; l61_2]. split; [exact R_b1|]. intros L' HIn. repeat (destruct HIn as [<-|HIn]); [exact k_10 | exact k_11 | exact k_12 | destruct HIn].
Qed.
Lemma R_5 : ltac2:(tb__ "0|1|
S0SfScS3A1M0A1S4S4eS25S9S4aZ3f440SaS4aA1A3S5eS22S26A2S8A5SeG0S9S3S28S9S3S29SaS3A1A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_5__R <: R_5__R = Some [l5_0; l5_1]). Qed.
Lemma LN_5 : ltac2:(tb__ "0|0|
S0SbS1dS2S5eS22S26A2A1A1S12A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NL_5 : ltac2:(tb__ "0|0|
S0SbS55Pf0S16S2S5eS22S26A2A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma T_5 : ltac2:(tb__ "0|1|
S54S25S9S4aZ3f440SaS4aA1M0A3S60S25U16S9S4aZ3ede4G0A3S53S22A1A4S5eS22S43S50S4fS1S23A1S3eA2A1A1A2A4").
Proof.
  rewrite RL_eq. split; [exact LN_5|]. split; [exact NL_5|]. exists [l5_0; l5_1]. split; [exact R_5|].
  intros L' HIn. repeat (destruct HIn as [<-|HIn]); [exact m_b0 | exact m_b1 | destruct HIn].
Qed.

Theorem drain_g_1 : ltac2:(tb__ "0|1|
S6cS7aS7aOF_;F_;S85R2R1A2S6dR3A1S86S4aS21ScS8bQ40A1A1S8aS87R4A1S84A2R8S83S4eS67S22S8R5R9R4A5S6aS22A1R3R2A5S7dS4eS63R3R2S9SdS6S7cA2M0S10S6S7cS69S22A1S68R5R9R4A3A4SaG0A1A3A5A2F_;Ftp;Frho;Fc;FA;FHKc;FKIT;FTR;FKc;").
Proof.
  apply (drain_g N). intros A Kc c rb tp0 md0 TR KIT HKc HE.
  exact (drain_growth_chain N A Kc c rb tp0 md0 TR KIT HKc HE FUEL l1_0 l2_0 lx_0 lm_0 W_0 D_0 R_1 LN_1 m_a W_fm D_fm R_x LN_0 NX_0 W_x D_x SK_x XF_x XX_x NX_x IC_x
           R17_x R10_x BEL_x R11_x R12_x R13_x R14_x R15_x R_m LN_g NX_g SK_m XF_m XX_m W_mr D_mr W_mc E_ms CHK_ms NF_ms NX_ms FBC_ms FBT_ms ND_r NO_r OB_r
           SK_c XF_c XX_c W_c T_5).
Qed.
End DrainIg1.

(* [comment removed for export] *)
Module DrainIg2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "la_state"; "ax_S"; "leafA"; "sym_runA"; "ax_X"; "axst"; "entailsA"; "@Corelib.Init.Datatypes"; "true"; "cons"; "nil"; "bool"; "list"; "prod"; "Some"; "option"; "pair"; "app"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "sprop"; "ss_next"; "SLit"; "ss_objs"; "swf"; "ss_facts"; "SAlu"; "reg_sv"; "ss_lenient"; "sprop_below"; "ss_pc"; "sv_below"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cb.DrainIg2"; "N"; "lm_0"; "lx_0"; "FUEL"; "rl"; "l1_0"; "l5_0"; "l5_1"; "l2_0"; "dm"; "l60_0"; "l60_1"; "l60_2"; "l61_0"; "l61_1"; "l61_2"; "cr_00"; "cr_01"; "cr_02"; "cr_10"; "cr_11"; "cr_12"; "s_00"; "s_01"; "s_02"; "s_10"; "s_11"; "s_12"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR"; "beg2"; "cX"; "nobj"; "vMFA"; "cFm"; "relM"; "rMS"; "ri_e"; "sMS"; "vRI"; "idx_rot"; "rotM"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c3.DrainF"; "rstD"; "O_riX"; "ri_hasD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocR10"; "cMc"; "dMSf"; "cMr"; "a2_e"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c7.DrainG6"; "leaf_okG"; "run_okG"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "eqb"; "@Corelib.Init.Nat"; "sub"; "@Corelib.Lists.ListDef"; "firstn"; "map"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "instr"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bu.DrainG4"; "cCD"; "cG0"; "mid_okG"; "XFG"; "rupD_e"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.DrainS"; "NXD"; "O_cntD"; "O_dstD"; "dst_cells"; "JD"; "JLD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.DrainSG"; "L_dh_g"; "Pre_dh_g"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "F_sp_high"; "KcA"; "Kc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cf.DrainG2"; "SKELG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR"; "commit_post"; "memset_post"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3"; "skel"; "inclb"; "@Stdlib.Lists.List"; "In"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineMallocR9"; "O_piece"; "O_shp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "nodupN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "call_checkA"; "entails_frA"; "@Corelib.Init.Peano"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "instr_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget"; "LIMIT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DrainTR"; "TRokD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "budget_bound";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bp.SpineMallocR11"; "a0_e"; "@Stdlib.Arith.PeanoNat.Nat"; "leb"; "@Stdlib.ZArith.BinInt.Z"; "le"; "@stdpp.bitvector.definitions"; "bv"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillTR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bi.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require DrainModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require DrainTR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineMallocR9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocR10 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bp.SpineMallocR11 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DrainModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.DrainS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.DrainSG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DrainTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c3.DrainF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c8.DrainG1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cf.DrainG2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bu.DrainG4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c7.DrainG6.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition N : Z := 2.
Definition FUEL : nat := 6000%nat.
Lemma W_0 : ltac2:(tb__ "0|0|
S0SbS19S2S5fS22A1A1A1S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_0 : ltac2:(tb__ "0|4|
S0SfSdScSdS13S13A2M0A1M1ScS15A1M2A2M3A1S5dS2S6aS22A1A1S2S5fS22A1A1A2SeG3S10G1G2SaG0A1S61A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Definition R_1__R : option (list leafA) := ltac2:(tb__ "0|0|
S4S4eS25S9S4aZ3ef90SaS4aA1A3S5fS22A1S8A5").
Local Strategy expand [R_1__R].
Definition l1 := Eval vm_compute in ((fun ro1__ : option (list leafA) => (match ro1__ with Some l => l | None => [] end)) R_1__R).
Definition l1_0 := Eval vm_compute in (nth 0 l1 (mkLeafA (cG0 N) RsCut)).
Lemma R_1 : ltac2:(tb__ "0|1|
S0SfScS3A1M0A1S4S4eS25S9S4aZ3ef90SaS4aA1A3S5fS22A1S8A5SeG0S9S3S27SaS3A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_1__R <: R_1__R = Some [l1_0]). Qed.
Lemma LN_1 : ltac2:(tb__ "0|0|
S0SbS1dS2S5fS22A1A1A1S12A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Definition R_a__R : option (list leafA) := ltac2:(tb__ "0|0|
S4S4eS25S9S4aZ3f270SaS4aA1A3S4bS1S27A1U8A2S8A5").
Local Strategy expand [R_a__R].
Definition l2 := Eval vm_compute in ((fun ro2__ : option (list leafA) => (match ro2__ with Some l => l | None => [] end)) R_a__R).
Definition l2_0 := Eval vm_compute in (nth 0 l2 (mkLeafA (rstD (la_state l1_0) 8) RsCut)).
Lemma W_a : ltac2:(tb__ "0|0|
S0SbS19S2S4bS1S27A1U8A2A1A1S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_a : ltac2:(tb__ "0|5|
S0SfSdScSdS13S13A2M0A1M1ScS15A1M2A2M3A1S5dS2S1S27A1M4A1S2S4bG4U8A2A1A2SeG3S10G1G2S9G0S10S13S13S45S47A4SaG0A1A3SaS15A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_a : ltac2:(tb__ "0|1|
S0SbS56S16S2S4bS1S27A1M0U8A2A1A1S16S2G0A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma LN_a : ltac2:(tb__ "0|0|
S0SbS1dS2S4bS1S27A1U8A2A1A1S12A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NL_a : ltac2:(tb__ "0|0|
S0SbS55Pf0S16S2S4bS1S27A1U8A2A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_a : ltac2:(tb__ "0|1|
S0SfScS3A1M0A1S4S4eS25S9S4aZ3f270SaS4aA1A3S4bS1S27A1U8A2S8A5SeG0S9S3S2aSaS3A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_a__R <: R_a__R = Some [l2_0]). Qed.
Lemma m_a : ltac2:(tb__ "0|0|
S60S25U8S9S4aZ3f270SaS4aA1A3S6S0S6R1S1S2aA1A3LL';S1S27A1A5").
Proof.
  split; [exact W_a|]. split; [exact D_a|]. split; [exact NXe_a|]. split; [exact LN_a|]. split; [exact NL_a|].
  exists [l2_0]. split; [exact R_a|]. intros L' HIn. repeat (destruct HIn as [<-|HIn]); [reflexivity | destruct HIn].
Qed.
Lemma W_fm : ltac2:(tb__ "0|0|
S0SbS19S2S42S1S2aA1A1A1A1S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_fm : ltac2:(tb__ "0|5|
S0SfSdScSdS13S13A2M0A1M1ScS15A1M2A2M3A1S5dS2S1S2aA1M4A1S2S42G4A1A1A2SeG3S10G1G2S9G0S10S13S13S62S22A1S1bS5aS41S17Z40000A1A3A4SaG0A1A3SaS15A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Definition R_x__R : option (list leafA) := ltac2:(tb__ "0|0|
S4S4eS25S9S4aZ7050cSaS4aA1A3S42S1S2aA1A1S8A5").
Local Strategy expand [R_x__R].
Definition lx := Eval vm_compute in ((fun ro3__ : option (list leafA) => (match ro3__ with Some l => l | None => [] end)) R_x__R).
Definition lx_0 := Eval vm_compute in (nth 0 lx (mkLeafA (cFm (la_state l2_0)) RsCut)).
Lemma R_x : ltac2:(tb__ "0|1|
S0SfScS3A1M0A1S4S4eS25S9S4aZ7050cSaS4aA1A3S42S1S2aA1A1S8A5SeG0S9S3S24SaS3A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_x__R <: R_x__R = Some [lx_0]). Qed.
Lemma LN_0 : ltac2:(tb__ "0|0|
S0SbS1dS2S42S1S2aA1A1A1A1S12A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_0 : ltac2:(tb__ "0|0|
S0SbS55Pf0S16S2S42S1S2aA1A1A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_x : ltac2:(tb__ "0|0|
S0SbS19S2S3fS1S24A1S3eA2A1A1S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_x : ltac2:(tb__ "0|5|
S0SfSdScSdS13S13A2M0A1M1ScS15A1M2A2M3A1S5dS2S1S24A1M4A1S2S3fG4S3eA2A1A2SeG3S10G1G2S9G0S10S13S13S88S3eA1S3eA4SaG0A1A3SaS15A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma SK_x : ltac2:(tb__ "0|1|
S0ScSdSdS13S13A2S13A2M0A1S59S14G0S72S18S2S3fS1S24A1S3eA2A1A1A4S6fS22SaS14A1A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_xb : ltac2:(tb__ "0|0|
S0SbS73S9S15S6bSaS15A1A3S1aS2S3fS1S24A1S3eA2A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XF_x : ltac2:(tb__ "0|0|
S74S15S6bS1aS2S3fS1S24A1S3eA2A1A1A3").
Proof. exact (inclb_incl _ _ XF_xb F_sp_high (or_introl eq_refl)). Qed.
Lemma XX_x : ltac2:(tb__ "0|1|
S0ScSdS13S13A2M0A1S5S3fS1S24A1S3eA2A1SaG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NX_x : ltac2:(tb__ "0|0|
S0SbS55Pf0S16S2S3fS1S24A1S3eA2A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma IC_x : ltac2:(tb__ "0|0|
S0SfS5bA1S82S4eS1fS2S3fS1S24A1S3eA2A1A1A2SeS5bS5cA2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R17_x : ltac2:(tb__ "0|0|
S0S13S1cS2S3fS1S24A1S3eA2A1Z11A2S17ZdeA1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R10_x : ltac2:(tb__ "0|0|
S0S13S1cS2S3fS1S24A1S3eA2A1ZaA2S3eA3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R11_x : ltac2:(tb__ "0|0|
S0S13S1cS2S3fS1S24A1S3eA2A1ZbA2S17Z40000A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R12_x : ltac2:(tb__ "0|0|
S0S13S1cS2S3fS1S24A1S3eA2A1ZcA2S17Z3A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R13_x : ltac2:(tb__ "0|0|
S0S13S1cS2S3fS1S24A1S3eA2A1ZdA2S17Z32A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R14_x : ltac2:(tb__ "0|0|
S0S13S1cS2S3fS1S24A1S3eA2A1ZeA2S17ZffffffffffffffffA1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R15_x : ltac2:(tb__ "0|0|
S0S13S1cS2S3fS1S24A1S3eA2A1ZfA2S17Z0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma BEL_x : ltac2:(tb__ "0|0|
S0SbS20S16S2S3fS1S24A1S3eA2A1A1S3eA2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Definition R_m__R : option (list leafA) := ltac2:(tb__ "0|0|
S4S4eS25S9S4aZde378SaS4aA1A3S70S3fS1S24A1S3eA2S3eZ40000A3S8A5").
Local Strategy expand [R_m__R].
Definition lm := Eval vm_compute in ((fun ro4__ : option (list leafA) => (match ro4__ with Some l => l | None => [] end)) R_m__R).
Definition lm_0 := Eval vm_compute in (nth 0 lm (mkLeafA (commit_post (cX (la_state lx_0) beg2) beg2 262144) RsCut)).
Lemma R_m : ltac2:(tb__ "0|1|
S0SfScS3A1M0A1S4S4eS25S9S4aZde378SaS4aA1A3S70S3fS1S24A1S3eA2S3eZ40000A3S8A5SeG0S9S3S23SaS3A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_m__R <: R_m__R = Some [lm_0]). Qed.
Lemma LN_g : ltac2:(tb__ "0|0|
S0SbS1dS2S70S3fS1S24A1S3eA2S3eZ40000A3A1A1S12A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_g : ltac2:(tb__ "0|0|
S0SbS55Pf0S16S2S70S3fS1S24A1S3eA2S3eZ40000A3A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SK_m : ltac2:(tb__ "0|1|
S0ScSdSdS13S13A2S13A2M0A1S59S14G0S72S18S2S1S23A1A1A1A4S6fS22S9S14S76S3eA1SaS14A1A3A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_mb : ltac2:(tb__ "0|0|
S0SbS73S9S15S6bSaS15A1A3S1aS2S1S23A1A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XF_m : ltac2:(tb__ "0|0|
S74S15S6bS1aS2S1S23A1A1A1A3").
Proof. exact (inclb_incl _ _ XF_mb F_sp_high (or_introl eq_refl)). Qed.
Lemma XX_m : ltac2:(tb__ "0|1|
S0ScSdS13S13A2M0A1S5S1S23A1A1SaG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma W_mr : ltac2:(tb__ "0|0|
S0SbS19S2S51S1S23A1A1A1A1S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_mr : ltac2:(tb__ "0|5|
S0SfSdScSdS13S13A2M0A1M1ScS15A1M2A2M3A1S5dS2S1S23A1M4A1S2S51G4A1A1A2SeG3S10G1G2S9G0S10S13S13S52S3eA1S17Z8000A1A4SaG0A1A3SaS15A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma W_mc : ltac2:(tb__ "0|0|
S0SbS19S2S4fS1S23A1S3eA2A1A1S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma E_ms : ltac2:(tb__ "0|2|
S0SfScS14A1M0A1S7fS4fS1S23A1S3eA2M1S78S46G1A1A3SeG0S44G1A1A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma CHK_ms : ltac2:(tb__ "0|1|
S0SbS7eS4fS1S23A1S3eA2M0S78S46G0A1S44G0A1S59S3S6S1S79A4A5S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NF_ms : ltac2:(tb__ "0|0|
S0SbS55S81S16S2S4fS1S23A1S3eA2A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NX_ms : ltac2:(tb__ "0|0|
S0SbS55Pf0S16S2S4fS1S23A1S3eA2A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBC_ms : ltac2:(tb__ "0|1|
S0SbS75S15S1eS16S2S4fS1S23A1S3eA2A1M0A1A1S1aG0A1A3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT_ms : ltac2:(tb__ "0|1|
S0SbS75S15S1eS16S2S71S4fS1S23A1S3eA2M0S46G0A1S44G0A1A3A1A1A1S1aS2G0A1A1A3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Definition dm := Eval vm_compute in (dMSf (cMc (la_state lm_0) beg2)).
Lemma DM_eq : ltac2:(tb__ "0|0|
S0S6S50S4fS1S23A1S3eA2A1S2bA3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma ND_rb : ltac2:(tb__ "0|0|
S0SbS7bS48S2bA1A1S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NO_rb : ltac2:(tb__ "0|0|
S0SbS89U1S40S2bA1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma OB_rb : ltac2:(tb__ "0|1|
S0ScS14A1S18S2S49S2bA1A1A1M0S11S14S58S14S57S40S2bA1U2A2G0A3S9S14S76S3eA1S9S14S77S3eA1SaS14A1A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma ND_r : ltac2:(tb__ "0|0|
S0SbS7bS48S50S4fS1S23A1S3eA2A1A1A1S8A3"). Proof. rewrite DM_eq. exact ND_rb. Qed.
Lemma NO_r : ltac2:(tb__ "0|0|
S80U1S40S50S4fS1S23A1S3eA2A1A1A2"). Proof. rewrite DM_eq. apply Nat.leb_le. exact NO_rb. Qed.
Lemma OB_r : ltac2:(tb__ "0|2|
S0ScS14A1S18S2S49S50S4fS1S23A1S3eA2A1M0A1A1A1M1S11S14S58S14S57S40G0A1U2A2G1A3S9S14S76S3eA1S9S14S77S3eA1SaS14A1A3A3A3A3"). Proof. rewrite DM_eq. exact OB_rb. Qed.
Definition rl := Eval vm_compute in (relM dm).
Lemma RL_eq : ltac2:(tb__ "0|0|
S0S6S43S50S4fS1S23A1S3eA2A1A1S26A3"). Proof. rewrite DM_eq. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma SK_cb : ltac2:(tb__ "0|1|
S0ScSdSdS13S13A2S13A2M0A1S59S14G0S72S18S2S26A1A1A4S6fS22SaS14A1A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_cbb : ltac2:(tb__ "0|0|
S0SbS73S9S15S6bSaS15A1A3S1aS2S26A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XF_cb : ltac2:(tb__ "0|0|
S74S15S6bS1aS2S26A1A1A3").
Proof. exact (inclb_incl _ _ XF_cbb F_sp_high (or_introl eq_refl)). Qed.
Lemma XX_cb : ltac2:(tb__ "0|1|
S0ScSdS13S13A2M0A1S5S26A1SaG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma W_cb : ltac2:(tb__ "0|0|
S0SbS19S2S5eS22S26A2A1A1S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SK_c : ltac2:(tb__ "0|1|
S0ScSdSdS13S13A2S13A2M0A1S59S14G0S72S18S2S43S50S4fS1S23A1S3eA2A1A1A1A1A4S6fS22SaS14A1A2A3"). Proof. rewrite RL_eq. exact SK_cb. Qed.
Lemma XF_c : ltac2:(tb__ "0|0|
S74S15S6bS1aS2S43S50S4fS1S23A1S3eA2A1A1A1A1A3"). Proof. rewrite RL_eq. exact XF_cb. Qed.
Lemma XX_c : ltac2:(tb__ "0|1|
S0ScSdS13S13A2M0A1S5S43S50S4fS1S23A1S3eA2A1A1A1SaG0A1A3"). Proof. rewrite RL_eq. exact XX_cb. Qed.
Lemma W_c : ltac2:(tb__ "0|0|
S0SbS19S2S5eS22S43S50S4fS1S23A1S3eA2A1A1A2A1A1S8A3"). Proof. rewrite RL_eq. exact W_cb. Qed.
Definition R_5__R : option (list leafA) := ltac2:(tb__ "0|0|
S4S4eS25S9S4aZ3f440SaS4aA1A3S5eS22S26A2S8A5").
Local Strategy expand [R_5__R].
Definition l5 := Eval vm_compute in ((fun ro7__ : option (list leafA) => (match ro7__ with Some l => l | None => [] end)) R_5__R).
Definition l5_0 := Eval vm_compute in (nth 0 l5 (mkLeafA (cCD N rl) RsCut)).
Definition l5_1 := Eval vm_compute in (nth 1 l5 (mkLeafA (cCD N rl) RsCut)).
Definition R_b0__R : option (list leafA) := ltac2:(tb__ "0|0|
S4S4eS25S9S4aZ3ede4SaS4aA1A3S4bS1S28A1U16A2S8A5").
Local Strategy expand [R_b0__R].
Definition l60 := Eval vm_compute in ((fun ro5__ : option (list leafA) => (match ro5__ with Some l => l | None => [] end)) R_b0__R).
Definition l60_0 := Eval vm_compute in (nth 0 l60 (mkLeafA (rstD (la_state l5_0) 22) RsCut)).
Definition l60_1 := Eval vm_compute in (nth 1 l60 (mkLeafA (rstD (la_state l5_0) 22) RsCut)).
Definition l60_2 := Eval vm_compute in (nth 2 l60 (mkLeafA (rstD (la_state l5_0) 22) RsCut)).
Definition cr_00 := Eval vm_compute in (ob_cells (nth (nobj (la_state l60_0) - 2) (ss_objs (ax_S (la_state l60_0))) O_pcc0)).
Definition s_00 := Eval vm_compute in (infer_sub NXD (ax_S (la_state l60_0)) (ax_S (L_dh_g N))).
Lemma XX_00 : ltac2:(tb__ "0|1|
S0ScSdS13S13A2M0A1S5S1S2cA1A1SaG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_00 : ltac2:(tb__ "0|2|
S0ScS14A1S18S2S1S2cA1M0A1A1M1S11S14S58S14S57S40G0A1U3A2G1A3S9S14S64S22A1S9S14S4cS32A1S9S14S65S22S66S22A1A2SaS14A1A3A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_00 : ltac2:(tb__ "0|0|
S0SbS4dS22S1bS5aS41S17Z40000A1A3S32A3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_00 : ltac2:(tb__ "0|0|
S0SbS7S1S2cA1S69S22A1S38A3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_00 : ltac2:(tb__ "0|0|
S0SbS6eS38S63A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma k_00 : ltac2:(tb__ "0|0|
S53S22S1S2cA1A2").
Proof. exists cr_00, s_00. exact (conj XX_00 (conj OB_00 (conj RI_00 (conj ENT_00 SID_00)))). Qed.
Definition cr_01 := Eval vm_compute in (ob_cells (nth (nobj (la_state l60_1) - 2) (ss_objs (ax_S (la_state l60_1))) O_pcc0)).
Definition s_01 := Eval vm_compute in (infer_sub NXD (ax_S (la_state l60_1)) (ax_S (L_dh_g N))).
Lemma XX_01 : ltac2:(tb__ "0|1|
S0ScSdS13S13A2M0A1S5S1S2dA1A1SaG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_01 : ltac2:(tb__ "0|2|
S0ScS14A1S18S2S1S2dA1M0A1A1M1S11S14S58S14S57S40G0A1U3A2G1A3S9S14S64S22A1S9S14S4cS33A1S9S14S65S22S66S22A1A2SaS14A1A3A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_01 : ltac2:(tb__ "0|0|
S0SbS4dS22S1bS5aS41S17Z40000A1A3S33A3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_01 : ltac2:(tb__ "0|0|
S0SbS7S1S2dA1S69S22A1S39A3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_01 : ltac2:(tb__ "0|0|
S0SbS6eS39S63A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma k_01 : ltac2:(tb__ "0|0|
S53S22S1S2dA1A2").
Proof. exists cr_01, s_01. exact (conj XX_01 (conj OB_01 (conj RI_01 (conj ENT_01 SID_01)))). Qed.
Definition cr_02 := Eval vm_compute in (ob_cells (nth (nobj (la_state l60_2) - 2) (ss_objs (ax_S (la_state l60_2))) O_pcc0)).
Definition s_02 := Eval vm_compute in (infer_sub NXD (ax_S (la_state l60_2)) (ax_S (L_dh_g N))).
Lemma XX_02 : ltac2:(tb__ "0|1|
S0ScSdS13S13A2M0A1S5S1S2eA1A1SaG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_02 : ltac2:(tb__ "0|2|
S0ScS14A1S18S2S1S2eA1M0A1A1M1S11S14S58S14S57S40G0A1U3A2G1A3S9S14S64S22A1S9S14S4cS34A1S9S14S65S22S66S22A1A2SaS14A1A3A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_02 : ltac2:(tb__ "0|0|
S0SbS4dS22S1bS5aS41S17Z40000A1A3S34A3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_02 : ltac2:(tb__ "0|0|
S0SbS7S1S2eA1S69S22A1S3aA3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_02 : ltac2:(tb__ "0|0|
S0SbS6eS3aS63A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma k_02 : ltac2:(tb__ "0|0|
S53S22S1S2eA1A2").
Proof. exists cr_02, s_02. exact (conj XX_02 (conj OB_02 (conj RI_02 (conj ENT_02 SID_02)))). Qed.
Lemma W_b0 : ltac2:(tb__ "0|0|
S0SbS19S2S4bS1S28A1U16A2A1A1S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_b0 : ltac2:(tb__ "0|5|
S0SfSdScSdS13S13A2M0A1M1ScS15A1M2A2M3A1S5dS2S1S28A1M4A1S2S4bG4U16A2A1A2SeG3S10G1G2S9G0S10S13S13S45S47A4SaG0A1A3SaS15A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_b0 : ltac2:(tb__ "0|1|
S0SbS56S16S2S4bS1S28A1M0U16A2A1A1S16S2G0A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma LN_b0 : ltac2:(tb__ "0|0|
S0SbS1dS2S4bS1S28A1U16A2A1A1S12A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NL_b0 : ltac2:(tb__ "0|0|
S0SbS55Pf0S16S2S4bS1S28A1U16A2A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_b0 : ltac2:(tb__ "0|1|
S0SfScS3A1M0A1S4S4eS25S9S4aZ3ede4SaS4aA1A3S4bS1S28A1U16A2S8A5SeG0S9S3S2cS9S3S2dS9S3S2eSaS3A1A3A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_b0__R <: R_b0__R = Some [l60_0; l60_1; l60_2]). Qed.
Lemma m_b0 : ltac2:(tb__ "0|0|
S60S25U16S9S4aZ3ede4SaS4aA1A3S53S22A1S1S28A1A5").
Proof.
  split; [exact W_b0|]. split; [exact D_b0|]. split; [exact NXe_b0|]. split; [exact LN_b0|]. split; [exact NL_b0|].
  exists [l60_0; l60_1; l60_2]. split; [exact R_b0|]. intros L' HIn. repeat (destruct HIn as [<-|HIn]); [exact k_00 | exact k_01 | exact k_02 | destruct HIn].
Qed.
Definition R_b1__R : option (list leafA) := ltac2:(tb__ "0|0|
S4S4eS25S9S4aZ3ede4SaS4aA1A3S4bS1S29A1U16A2S8A5").
Local Strategy expand [R_b1__R].
Definition l61 := Eval vm_compute in ((fun ro6__ : option (list leafA) => (match ro6__ with Some l => l | None => [] end)) R_b1__R).
Definition l61_0 := Eval vm_compute in (nth 0 l61 (mkLeafA (rstD (la_state l5_1) 22) RsCut)).
Definition l61_1 := Eval vm_compute in (nth 1 l61 (mkLeafA (rstD (la_state l5_1) 22) RsCut)).
Definition l61_2 := Eval vm_compute in (nth 2 l61 (mkLeafA (rstD (la_state l5_1) 22) RsCut)).
Definition cr_10 := Eval vm_compute in (ob_cells (nth (nobj (la_state l61_0) - 2) (ss_objs (ax_S (la_state l61_0))) O_pcc0)).
Definition s_10 := Eval vm_compute in (infer_sub NXD (ax_S (la_state l61_0)) (ax_S (L_dh_g N))).
Lemma XX_10 : ltac2:(tb__ "0|1|
S0ScSdS13S13A2M0A1S5S1S2fA1A1SaG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_10 : ltac2:(tb__ "0|2|
S0ScS14A1S18S2S1S2fA1M0A1A1M1S11S14S58S14S57S40G0A1U3A2G1A3S9S14S64S22A1S9S14S4cS35A1S9S14S65S22S66S22A1A2SaS14A1A3A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_10 : ltac2:(tb__ "0|0|
S0SbS4dS22S1bS5aS41S17Z40000A1A3S35A3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_10 : ltac2:(tb__ "0|0|
S0SbS7S1S2fA1S69S22A1S3bA3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_10 : ltac2:(tb__ "0|0|
S0SbS6eS3bS63A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma k_10 : ltac2:(tb__ "0|0|
S53S22S1S2fA1A2").
Proof. exists cr_10, s_10. exact (conj XX_10 (conj OB_10 (conj RI_10 (conj ENT_10 SID_10)))). Qed.
Definition cr_11 := Eval vm_compute in (ob_cells (nth (nobj (la_state l61_1) - 2) (ss_objs (ax_S (la_state l61_1))) O_pcc0)).
Definition s_11 := Eval vm_compute in (infer_sub NXD (ax_S (la_state l61_1)) (ax_S (L_dh_g N))).
Lemma XX_11 : ltac2:(tb__ "0|1|
S0ScSdS13S13A2M0A1S5S1S30A1A1SaG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_11 : ltac2:(tb__ "0|2|
S0ScS14A1S18S2S1S30A1M0A1A1M1S11S14S58S14S57S40G0A1U3A2G1A3S9S14S64S22A1S9S14S4cS36A1S9S14S65S22S66S22A1A2SaS14A1A3A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_11 : ltac2:(tb__ "0|0|
S0SbS4dS22S1bS5aS41S17Z40000A1A3S36A3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_11 : ltac2:(tb__ "0|0|
S0SbS7S1S30A1S69S22A1S3cA3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_11 : ltac2:(tb__ "0|0|
S0SbS6eS3cS63A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma k_11 : ltac2:(tb__ "0|0|
S53S22S1S30A1A2").
Proof. exists cr_11, s_11. exact (conj XX_11 (conj OB_11 (conj RI_11 (conj ENT_11 SID_11)))). Qed.
Definition cr_12 := Eval vm_compute in (ob_cells (nth (nobj (la_state l61_2) - 2) (ss_objs (ax_S (la_state l61_2))) O_pcc0)).
Definition s_12 := Eval vm_compute in (infer_sub NXD (ax_S (la_state l61_2)) (ax_S (L_dh_g N))).
Lemma XX_12 : ltac2:(tb__ "0|1|
S0ScSdS13S13A2M0A1S5S1S31A1A1SaG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_12 : ltac2:(tb__ "0|2|
S0ScS14A1S18S2S1S31A1M0A1A1M1S11S14S58S14S57S40G0A1U3A2G1A3S9S14S64S22A1S9S14S4cS37A1S9S14S65S22S66S22A1A2SaS14A1A3A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_12 : ltac2:(tb__ "0|0|
S0SbS4dS22S1bS5aS41S17Z40000A1A3S37A3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_12 : ltac2:(tb__ "0|0|
S0SbS7S1S31A1S69S22A1S3dA3S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_12 : ltac2:(tb__ "0|0|
S0SbS6eS3dS63A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma k_12 : ltac2:(tb__ "0|0|
S53S22S1S31A1A2").
Proof. exists cr_12, s_12. exact (conj XX_12 (conj OB_12 (conj RI_12 (conj ENT_12 SID_12)))). Qed.
Lemma W_b1 : ltac2:(tb__ "0|0|
S0SbS19S2S4bS1S29A1U16A2A1A1S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_b1 : ltac2:(tb__ "0|5|
S0SfSdScSdS13S13A2M0A1M1ScS15A1M2A2M3A1S5dS2S1S29A1M4A1S2S4bG4U16A2A1A2SeG3S10G1G2S9G0S10S13S13S45S47A4SaG0A1A3SaS15A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_b1 : ltac2:(tb__ "0|1|
S0SbS56S16S2S4bS1S29A1M0U16A2A1A1S16S2G0A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma LN_b1 : ltac2:(tb__ "0|0|
S0SbS1dS2S4bS1S29A1U16A2A1A1S12A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NL_b1 : ltac2:(tb__ "0|0|
S0SbS55Pf0S16S2S4bS1S29A1U16A2A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_b1 : ltac2:(tb__ "0|1|
S0SfScS3A1M0A1S4S4eS25S9S4aZ3ede4SaS4aA1A3S4bS1S29A1U16A2S8A5SeG0S9S3S2fS9S3S30S9S3S31SaS3A1A3A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_b1__R <: R_b1__R = Some [l61_0; l61_1; l61_2]). Qed.
Lemma m_b1 : ltac2:(tb__ "0|0|
S60S25U16S9S4aZ3ede4SaS4aA1A3S53S22A1S1S29A1A5").
Proof.
  split; [exact W_b1|]. split; [exact D_b1|]. split; [exact NXe_b1|]. split; [exact LN_b1|]. split; [exact NL_b1|].
  exists [l61_0; l61_1; l61_2]. split; [exact R_b1|]. intros L' HIn. repeat (destruct HIn as [<-|HIn]); [exact k_10 | exact k_11 | exact k_12 | destruct HIn].
Qed.
Lemma R_5 : ltac2:(tb__ "0|1|
S0SfScS3A1M0A1S4S4eS25S9S4aZ3f440SaS4aA1A3S5eS22S26A2S8A5SeG0S9S3S28S9S3S29SaS3A1A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_5__R <: R_5__R = Some [l5_0; l5_1]). Qed.
Lemma LN_5 : ltac2:(tb__ "0|0|
S0SbS1dS2S5eS22S26A2A1A1S12A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NL_5 : ltac2:(tb__ "0|0|
S0SbS55Pf0S16S2S5eS22S26A2A1A1A2S8A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma T_5 : ltac2:(tb__ "0|1|
S54S25S9S4aZ3f440SaS4aA1M0A3S60S25U16S9S4aZ3ede4G0A3S53S22A1A4S5eS22S43S50S4fS1S23A1S3eA2A1A1A2A4").
Proof.
  rewrite RL_eq. split; [exact LN_5|]. split; [exact NL_5|]. exists [l5_0; l5_1]. split; [exact R_5|].
  intros L' HIn. repeat (destruct HIn as [<-|HIn]); [exact m_b0 | exact m_b1 | destruct HIn].
Qed.

Theorem drain_g_2 : ltac2:(tb__ "0|1|
S6cS7aS7aOF_;F_;S85R2R1A2S6dR3A1S86S4aS21ScS8bQ40A1A1S8aS87R4A1S84A2R8S83S4eS67S22S8R5R9R4A5S6aS22A1R3R2A5S7dS4eS63R3R2S9SdS6S7cA2M0S10S6S7cS69S22A1S68R5R9R4A3A4SaG0A1A3A5A2F_;Ftp;Frho;Fc;FA;FHKc;FKIT;FTR;FKc;").
Proof.
  apply (drain_g N). intros A Kc c rb tp0 md0 TR KIT HKc HE.
  exact (drain_growth_chain N A Kc c rb tp0 md0 TR KIT HKc HE FUEL l1_0 l2_0 lx_0 lm_0 W_0 D_0 R_1 LN_1 m_a W_fm D_fm R_x LN_0 NX_0 W_x D_x SK_x XF_x XX_x NX_x IC_x
           R17_x R10_x BEL_x R11_x R12_x R13_x R14_x R15_x R_m LN_g NX_g SK_m XF_m XX_m W_mr D_mr W_mc E_ms CHK_ms NF_ms NX_ms FBC_ms FBT_ms ND_r NO_r OB_r
           SK_c XF_c XX_c W_c T_5).
Qed.
End DrainIg2.

(* [comment removed for export] *)
Module SpineCallocRp0.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "iff"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "la_state"; "leafA"; "sym_runA"; "entailsA"; "ax_X"; "axst"; "@Corelib.Init.Datatypes"; "cons"; "true"; "bool"; "nil"; "list"; "prod"; "Some"; "option"; "pair"; "app"; "false"; "length"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "sprop"; "ss_next"; "SLit"; "ss_facts"; "swf"; "ss_lenient"; "ss_objs"; "SAlu"; "SVar"; "reg_sv"; "SPNot"; "valuation"; "sprop_below"; "SPBranch"; "SPUle"; "rm"; "ss_pc"; "sv_below"; "rw"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSR"; "factsR"; "cX"; "GR"; "beg1"; "beg2"; "cE1"; "cE2"; "keepn"; "cP2"; "cXL"; "O_pcm"; "PV4"; "LV0"; "O_ri"; "cL1"; "cT1"; "cD"; "cPa"; "cPb"; "LV2"; "PV6"; "cE3"; "nobj"; "rMS"; "sMS"; "LV3"; "cE3b"; "vMU"; "cFm"; "vK"; "F_x"; "HINT_au"; "HINT_k"; "HINT_map"; "LNX"; "O_pccK"; "PNX"; "cE3a"; "idx_rot"; "k_e"; "relM"; "ri_has"; "rotM"; "vAU"; "vMFA"; "F_new"; "vNEW"; "vNF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bn.SpineCallocRi0"; "e3r"; "FUEL"; "icc"; "W0"; "r_2_0"; "nob"; "e3p"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3"; "inclb"; "skel"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "eqb"; "@Corelib.Lists.ListDef"; "map"; "firstn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLe"; "KcA"; "Kc_ok"; "mem_keptA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cb.SpineCallocRp0"; "r_xF_0"; "r_xU_0"; "cmcF"; "cmcU"; "r_9M_0"; "r_9P_0"; "cl0M"; "cl0P"; "cp2c"; "ct0M"; "ct0P"; "nobFM"; "nobFP"; "r_lM_1"; "r_lP_1"; "r_p1_0"; "r_p1_1"; "r_d_0"; "r_f_0"; "cfm"; "r_f_1"; "r_h_0"; "r_mF_0"; "r_mU_0"; "rf1"; "ru1"; "dmF"; "dmU"; "r_jM_0"; "r_jP_0"; "r_p2a_0"; "r_p2a_1"; "r_p2b_0"; "r_p2b_1"; "s_fbkM"; "s_fbkP"; "s_finM"; "s_finP"; "r_lM_0"; "r_lP_0"; "r_t1M_0"; "r_t1P_0"; "s_bkM"; "s_bkP"; "s_inM"; "s_inP"; "xlM"; "xlP"; "r_t1M_1"; "r_t1P_1"; "cellsfM"; "cellsfP"; "r_flM_0"; "r_flP_0"; "r_t0M_0"; "r_t0P_0"; "r_zM_0"; "r_zP_0"; "sa0"; "sa1"; "sb0"; "sb1"; "s_xM"; "s_xP"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_NE"; "instr"; "ALU_SLL"; "ALU_XOR"; "Ecall"; "BC_LTU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP"; "O_pcc0"; "O_st"; "V_SIZE"; "pc_base"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineCallocR2"; "BASEF"; "BASEO"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR"; "commit_post"; "memset_post"; "TRok"; "@Stdlib.Lists.List"; "forallb"; "nth_error"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CRefillJ"; "phase"; "JR"; "entryR"; "gh_new"; "ph0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bl.SpineCallocR10";
"cMr"; "a2_e"; "cMc"; "dMSf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bm.SpineCallocR13"; "F_lt"; "O_fcell"; "faend_e"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SpineCallocR3"; "O_dstc"; "O_srcc"; "e_end"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SpineCallocR7"; "F_mu0"; "F_hi"; "x19_e0"; "x19_e1"; "popfacts"; "size_e_hi"; "size_e_lo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bk.SpineCallocR9"; "O_piece"; "O_shp"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_cache_inited"; "class_state"; "cs_free_array"; "cs_mapped_free_array"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "nodupN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "instr_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "call_checkA"; "entails_frA"; "jpostA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b6.SpineCallocR11"; "a0_e"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.SpineCallocR12"; "F_geu"; "new_e"; "rup_e"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bn.SpineCallocR14"; "e16P"; "e32P"; "e48P"; "e_srcP"; "e24M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bq.SpineCallocR15"; "fillT"; "phUF3"; "pieceT"; "fmT"; "headT"; "midT"; "phFin"; "phU3"; "runT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b6.SpineCallocR4"; "O_rif"; "@Stdlib.Arith.PeanoNat.Nat"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.CRefillJP"; "PF"; "PU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel"; "kchunks"; "refillA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.SpineCallocR5"; "posts_conv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "cls_of"; "cst_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1"; "JG"; "@Stdlib.ZArith.BinInt.Z"; "add"; "lt"; "mul"; "of_nat"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocSP SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillTR CRefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ba.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bm.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bq.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aq.SpineCallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CRefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.CRefillJP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b3.SpineCallocR1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineCallocR2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SpineCallocR3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b6.SpineCallocR4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.SpineCallocR5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bm.SpineCallocR6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SpineCallocR7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bk.SpineCallocR9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bl.SpineCallocR10 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b6.SpineCallocR11 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.SpineCallocR12 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bm.SpineCallocR13 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bn.SpineCallocR14 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bq.SpineCallocR15 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bn.SpineCallocRi0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition R_p1__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ415c0SbS2cZ41600SeS2cA1A3A3S5S62A1ScA5").
Local Strategy expand [R_p1__R].
Definition r_p1 := Eval vm_compute in ((fun ro1__ : option (list leafA) => (match ro1__ with Some l => l | None => [] end)) R_p1__R).
Definition r_p1_0 := Eval vm_compute in (nth 0 r_p1 (mkLeafA (la_state r_2_0) RsCut)).
Definition r_p1_1 := Eval vm_compute in (nth 1 r_p1 (mkLeafA (la_state r_2_0) RsCut)).
Definition R_p2a__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ41630SeS2cA1A3S3fS2eS5eA1S5S80A1A2ScA5").
Local Strategy expand [R_p2a__R].
Definition r_p2a := Eval vm_compute in ((fun ro2__ : option (list leafA) => (match ro2__ with Some l => l | None => [] end)) R_p2a__R).
Definition r_p2a_0 := Eval vm_compute in (nth 0 r_p2a (mkLeafA (cPa (factsR e3r) (la_state r_p1_0)) RsCut)).
Definition r_p2a_1 := Eval vm_compute in (nth 1 r_p2a (mkLeafA (cPa (factsR e3r) (la_state r_p1_0)) RsCut)).
Definition R_p2b__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ41630SeS2cA1A3S40S2eS5eA1S5S81A1A2ScA5").
Local Strategy expand [R_p2b__R].
Definition r_p2b := Eval vm_compute in ((fun ro3__ : option (list leafA) => (match ro3__ with Some l => l | None => [] end)) R_p2b__R).
Definition r_p2b_0 := Eval vm_compute in (nth 0 r_p2b (mkLeafA (cPb (factsR e3r) (la_state r_p1_1)) RsCut)).
Definition r_p2b_1 := Eval vm_compute in (nth 1 r_p2b (mkLeafA (cPb (factsR e3r) (la_state r_p1_1)) RsCut)).
Definition cp2c := Eval vm_compute in (cP2c (factsR e3r) (la_state r_p2a_1)).
Lemma FP_inb : ltac2:(tb__ "0|0|
S0SdS65SbS19S26Sb7S5dS4bA3SeS19A1A3S1cS4S5S62A1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_p1 : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ415c0SbS2cZ41600SeS2cA1A3A3S5S62A1ScA5S11G0SbS6S80SbS6S81SeS6A1A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_p1__R <: R_p1__R = Some [r_p1_0; r_p1_1]). Qed.
Lemma LN_p1 : ltac2:(tb__ "0|0|
S0SdS1eS4S5S62A1A1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_p1 : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4S5S62A1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma Fa_inb : ltac2:(tb__ "0|0|
S0SdS65SbS19Sd8SeS19A1A3S1cS4S5S80A1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma Fb_inb : ltac2:(tb__ "0|0|
S0SdS65SbS19S23Sd8A1SeS19A1A3S1cS4S5S81A1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_pa : ltac2:(tb__ "0|0|
S0SdS1dS4S3fS2eS5eA1S5S80A1A2A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_pa : ltac2:(tb__ "0|5|
S0S12S10SfS10S18S18A2M0A1M1SfS19A1M2A2M3A1Sb8S4S5S80A1M4A1S4S3fS2eS5eA1G4A2A1A2S11G3S13G1G2SbG0S13S18S18SdcS21SbbA1A4SeG0A1A3SbS19S4fSbS19S27S49S1bZdffc0000A1A2SeS19A1A3A3A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_pa : ltac2:(tb__ "0|1|
S0SdS68S1aS4S3fS2eS5eA1S5S80A1M0A2A1A1S1aS4G0A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_pb : ltac2:(tb__ "0|0|
S0SdS1dS4S40S2eS5eA1S5S81A1A2A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_pb : ltac2:(tb__ "0|5|
S0S12S10SfS10S18S18A2M0A1M1SfS19A1M2A2M3A1Sb8S4S5S81A1M4A1S4S40S2eS5eA1G4A2A1A2S11G3S13G1G2SbG0S13S18S18SddS21SbbA1A4SeG0A1A3SbS19S4fSbS19S27S49S1bZdffc0000A1A2SeS19A1A3A3A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_pb : ltac2:(tb__ "0|1|
S0SdS68S1aS4S40S2eS5eA1S5S81A1M0A2A1A1S1aS4G0A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_p2a : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ41630SeS2cA1A3S3fS2eS5eA1S5S80A1A2ScA5S11G0SbS6S8fSbS6S90SeS6A1A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_p2a__R <: R_p2a__R = Some [r_p2a_0; r_p2a_1]). Qed.
Lemma LN_p2a : ltac2:(tb__ "0|0|
S0SdS1eS4S3fS2eS5eA1S5S80A1A2A1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_p2a : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4S3fS2eS5eA1S5S80A1A2A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_p2b : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ41630SeS2cA1A3S40S2eS5eA1S5S81A1A2ScA5S11G0SbS6S91SbS6S92SeS6A1A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_p2b__R <: R_p2b__R = Some [r_p2b_0; r_p2b_1]). Qed.
Lemma LN_p2b : ltac2:(tb__ "0|0|
S0SdS1eS4S40S2eS5eA1S5S81A1A2A1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_p2b : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4S40S2eS5eA1S5S81A1A2A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma Fa0_inb : ltac2:(tb__ "0|0|
S0SdS65SbS19Sd7SeS19A1A3S1cS4S5S8fA1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_a0 : ltac2:(tb__ "0|0|
S0SdS1dS4S36S2eS5eA1S5S8fA1A2A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_a0 : ltac2:(tb__ "0|5|
S0S12S10SfS10S18S18A2M0A1M1SfS19A1M2A2M3A1Sb8S4S5S8fA1M4A1S4S36S2eS5eA1G4A2A1A2S11G3S13G1G2SbG0S13S18S18Sd9S1bZ40000A1A4SbG0S13S18S18S1bZ0A1S49A4SeG0A1A3A3SeS19A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_a0 : ltac2:(tb__ "0|1|
S0SdS68S1aS4S36S2eS5eA1S5S8fA1M0A2A1A1S1aS4G0A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sa0 := Eval vm_compute in (infer_sub GR (ax_S (cP2 (factsR e3r) (la_state r_p2a_0))) (ax_S cp2c)).
Lemma ENT_a0 : ltac2:(tb__ "0|0|
S0SdS8S36S2eS5eA1S5S8fA1A2S79SabA3ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_a0 : ltac2:(tb__ "0|0|
S0SdS6cSabS30A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma Fa1_inb : ltac2:(tb__ "0|0|
S0SdS65SbS19S23Sd7A1SeS19A1A3S1cS4S5S90A1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_a1 : ltac2:(tb__ "0|0|
S0SdS1dS4S36S2eS5eA1S5S90A1A2A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_a1 : ltac2:(tb__ "0|5|
S0S12S10SfS10S18S18A2M0A1M1SfS19A1M2A2M3A1Sb8S4S5S90A1M4A1S4S36S2eS5eA1G4A2A1A2S11G3S13G1G2SbG0S13S18S18SdaS1bZ40000A1A4SeG0A1A3SeS19A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_a1 : ltac2:(tb__ "0|1|
S0SdS68S1aS4S36S2eS5eA1S5S90A1M0A2A1A1S1aS4G0A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sa1 := Eval vm_compute in (infer_sub GR (ax_S (cP2 (factsR e3r) (la_state r_p2a_1))) (ax_S cp2c)).
Lemma ENT_a1 : ltac2:(tb__ "0|0|
S0SdS8S36S2eS5eA1S5S90A1A2S79SacA3ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_a1 : ltac2:(tb__ "0|0|
S0SdS6cSacS30A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma Fb0_inb : ltac2:(tb__ "0|0|
S0SdS65SbS19Sd7SeS19A1A3S1cS4S5S91A1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_b0 : ltac2:(tb__ "0|0|
S0SdS1dS4S36S2eS5eA1S5S91A1A2A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_b0 : ltac2:(tb__ "0|5|
S0S12S10SfS10S18S18A2M0A1M1SfS19A1M2A2M3A1Sb8S4S5S91A1M4A1S4S36S2eS5eA1G4A2A1A2S11G3S13G1G2SbG0S13S18S18Sd9S1bZ40000A1A4SbG0S13S18S18S1bZ0A1S49A4SeG0A1A3A3SeS19A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_b0 : ltac2:(tb__ "0|1|
S0SdS68S1aS4S36S2eS5eA1S5S91A1M0A2A1A1S1aS4G0A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sb0 := Eval vm_compute in (infer_sub GR (ax_S (cP2 (factsR e3r) (la_state r_p2b_0))) (ax_S cp2c)).
Lemma ENT_b0 : ltac2:(tb__ "0|0|
S0SdS8S36S2eS5eA1S5S91A1A2S79SadA3ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_b0 : ltac2:(tb__ "0|0|
S0SdS6cSadS30A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma Fb1_inb : ltac2:(tb__ "0|0|
S0SdS65SbS19S23Sd7A1SeS19A1A3S1cS4S5S92A1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_b1 : ltac2:(tb__ "0|0|
S0SdS1dS4S36S2eS5eA1S5S92A1A2A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_b1 : ltac2:(tb__ "0|5|
S0S12S10SfS10S18S18A2M0A1M1SfS19A1M2A2M3A1Sb8S4S5S92A1M4A1S4S36S2eS5eA1G4A2A1A2S11G3S13G1G2SbG0S13S18S18SdaS1bZ40000A1A4SeG0A1A3SeS19A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_b1 : ltac2:(tb__ "0|1|
S0SdS68S1aS4S36S2eS5eA1S5S92A1M0A2A1A1S1aS4G0A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sb1 := Eval vm_compute in (infer_sub GR (ax_S (cP2 (factsR e3r) (la_state r_p2b_1))) (ax_S cp2c)).
Lemma ENT_b1 : ltac2:(tb__ "0|0|
S0SdS8S36S2eS5eA1S5S92A1A2S79SaeA3ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_b1 : ltac2:(tb__ "0|0|
S0SdS6cSaeS30A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma head_i : ltac2:(tb__ "0|0|
SfcS61S6dS5S62A1S79A4").
Proof.
  intros A Kc rb tp0 md0 TR KIT HKc rho r tp Q HE HC.
  exact (populate_head A Kc rb tp0 md0 TR KIT HKc W0 UStopLe rho HE FUEL e3r (la_state r_2_0) r_p1_0 r_p1_1 r_p2a_0 r_p2a_1 r_p2b_0 r_p2b_1 cp2c sa0 sa1 sb0 sb1
           (In_of_inclb _ _ FP_inb) R_p1 LN_p1 NX_p1 (In_of_inclb _ _ Fa_inb) (In_of_inclb _ _ Fb_inb) W_pa D_pa NXe_pa W_pb D_pb NXe_pb R_p2a LN_p2a NX_p2a R_p2b LN_p2b NX_p2b
           (In_of_inclb _ _ Fa0_inb) (In_of_inclb _ _ Fa1_inb) (In_of_inclb _ _ Fb0_inb) (In_of_inclb _ _ Fb1_inb) W_a0 W_a1 W_b0 W_b1 D_a0 D_a1 D_b0 D_b1 NXe_a0 NXe_a1 NXe_b0 NXe_b1
           ENT_a0 ENT_a1 ENT_b0 ENT_b1 SID_a0 SID_a1 SID_b0 SID_b1 r tp Q HC).
Qed.
Definition R_xU__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ7050cSeS2cA1A3S79ScA5").
Local Strategy expand [R_xU__R].
Definition r_xU := Eval vm_compute in ((fun ro4__ : option (list leafA) => (match ro4__ with Some l => l | None => [] end)) R_xU__R).
Definition r_xU_0 := Eval vm_compute in (nth 0 r_xU (mkLeafA cp2c RsCut)).
Definition R_mU__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZde378SeS2cA1A3SbfS2fS5S72A1S31A2S31Z40000A3ScA5").
Local Strategy expand [R_mU__R].
Definition r_mU := Eval vm_compute in ((fun ro5__ : option (list leafA) => (match ro5__ with Some l => l | None => [] end)) R_mU__R).
Definition r_mU_0 := Eval vm_compute in (nth 0 r_mU (mkLeafA (commit_post (cX (la_state r_xU_0) beg1) beg1 262144) RsCut)).
Definition cmcU := Eval vm_compute in (cMc (la_state r_mU_0) beg1).
Lemma CMCU_eq : ltac2:(tb__ "0|0|
S0SaScfS5S88A1S31A2S74A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Definition dmU := Eval vm_compute in (dMSf cmcU).
Lemma DMU_eq : ltac2:(tb__ "0|0|
S0SaSd0S74A1S8cA3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Definition ru1 := Eval vm_compute in (relM dmU).
Lemma RU1_eq : ltac2:(tb__ "0|0|
S0SaS56S8cA1S8aA3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R_xU : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ7050cSeS2cA1A3S79ScA5S11G0SbS6S72SeS6A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_xU__R <: R_xU__R = Some [r_xU_0]). Qed.
Lemma LN_xU : ltac2:(tb__ "0|0|
S0SdS1eS4S79A1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_xU : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4S79A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_xU : ltac2:(tb__ "0|0|
S0SdS1dS4S2fS5S72A1S31A2A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_xU : ltac2:(tb__ "0|5|
S0S12S10SfS10S18S18A2M0A1M1SfS19A1M2A2M3A1Sb8S4S5S72A1M4A1S4S2fG4S31A2A1A2S11G3S13G1G2SbG0S13S18S18SefS31A1S31A4SeG0A1A3SeS19A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma SK_xU : ltac2:(tb__ "0|1|
S0SfS10S10S18S18A2S18A2M0A1S69S17G0S66S1fS4S2fS5S72A1S31A2A1A1A4S69S17G0S66S14S17SbeS61A1SbS17Sb9SbS17SbaSbS17S38SbS17S3bSeS17A1A3A3A3A3A3A4A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_xUb : ltac2:(tb__ "0|0|
S0SdS65SbdS61S6dA2S1cS4S2fS5S72A1S31A2A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XX_xU : ltac2:(tb__ "0|1|
S0SfS10S18S18A2M0A1S9S2fS5S72A1S31A2A1SeG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXc_xU : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4S2fS5S72A1S31A2A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma IC_xU : ltac2:(tb__ "0|0|
S0S12Sb3A1Se9S2dS29S4S2fS5S72A1S31A2A1A1A2S11Sb3Sb6A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R17_xU : ltac2:(tb__ "0|0|
S0S18S22S4S2fS5S72A1S31A2A1Z11A2S1bZdeA1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R10_xU : ltac2:(tb__ "0|0|
S0S18S22S4S2fS5S72A1S31A2A1ZaA2S31A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R11_xU : ltac2:(tb__ "0|0|
S0S18S22S4S2fS5S72A1S31A2A1ZbA2S1bZ40000A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R12_xU : ltac2:(tb__ "0|0|
S0S18S22S4S2fS5S72A1S31A2A1ZcA2S1bZ3A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R13_xU : ltac2:(tb__ "0|0|
S0S18S22S4S2fS5S72A1S31A2A1ZdA2S1bZ32A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R14_xU : ltac2:(tb__ "0|0|
S0S18S22S4S2fS5S72A1S31A2A1ZeA2S1bZffffffffffffffffA1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R15_xU : ltac2:(tb__ "0|0|
S0S18S22S4S2fS5S72A1S31A2A1ZfA2S1bZ0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma BEL_xU : ltac2:(tb__ "0|0|
S0SdS2aS1aS4S2fS5S72A1S31A2A1A1S31A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_mU : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZde378SeS2cA1A3SbfS2fS5S72A1S31A2S31Z40000A3ScA5S11G0SbS6S88SeS6A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_mU__R <: R_mU__R = Some [r_mU_0]). Qed.
Lemma LN_mU : ltac2:(tb__ "0|0|
S0SdS1eS4SbfS2fS5S72A1S31A2S31Z40000A3A1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_mU : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4SbfS2fS5S72A1S31A2S31Z40000A3A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SK_mU : ltac2:(tb__ "0|1|
S0SfS10S10S18S18A2S18A2M0A1S69S17G0S66S1fS4S5S88A1A1A1A4S69S17G0S66S14S17SbeS61A1SbS17Sb9SbS17SbaSbS17S38SbS17S3bSbS17SdeS31A1SeS17A1A3A3A3A3A3A3A4A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_mUb : ltac2:(tb__ "0|0|
S0SdS65SbdS61S6dA2S1cS4S5S88A1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XX_mU : ltac2:(tb__ "0|1|
S0SfS10S18S18A2M0A1S9S5S88A1A1SeG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma W_mrU : ltac2:(tb__ "0|0|
S0SdS1dS4ScdS5S88A1A1A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_mrU : ltac2:(tb__ "0|5|
S0S12S10SfS10S18S18A2M0A1M1SfS19A1M2A2M3A1Sb8S4S5S88A1M4A1S4ScdG4A1A1A2S11G3S13G1G2SbG0S13S18S18SceS31A1S1bZ8000A1A4SeG0A1A3SeS19A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma W_mcU : ltac2:(tb__ "0|0|
S0SdS1dS4S74A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma E_msU : ltac2:(tb__ "0|1|
S0S12SfS17A1M0A1SedS74Sc5S46S74A1A3S11G0S45S74A1A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma CHK_msU : ltac2:(tb__ "0|0|
S0SdSecS74Sc5S46S74A1S45S74A1S69S6SaS5Sc6A4A5ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NF_msU : ltac2:(tb__ "0|0|
S0SdS67Sc7S1aS4S74A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NX_msU : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4S74A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBC_msU : ltac2:(tb__ "0|1|
S0SdSc2S19S25S1aS4S74A1M0A1A1S1cG0A1A3ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT_msU : ltac2:(tb__ "0|0|
S0SdSc2S19S25S1aS4Sc0S74S46S74A1S45S74A1A3A1A1A1S1cS4S74A1A1A3ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ND_rU : ltac2:(tb__ "0|0|
S0SdSe8S54S8cA1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NO_rUb : ltac2:(tb__ "0|0|
S0SdS102U1S44S8cA1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma OB_rU : ltac2:(tb__ "0|1|
S0SfS17A1S1fS4S58S8cA1A1A1M0S14S17S6aS17Sc4S44S8cA1U2A2G0A3SbS17SdeS31A1SbS17SdfS31A1SeS17A1A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma pieceU_i : ltac2:(tb__ "0|0|
SfaS61S6dS104S31S79S8aA6").
Proof.
  rewrite <- RU1_eq, <- DMU_eq, <- CMCU_eq.
  intros A Kc rb tp0 md0 TR KIT HKc rho HE ph PH0 PORD PQ HBv HBn HRc HRr r tp Q HC.
  refine (piece_full A Kc rb tp0 md0 TR KIT HKc W0 UStopLe rho HW0 HE PU beg1 ph PH0 PORD PQ HBv HBn HRc HRr FUEL cp2c r_xU_0 r_mU_0
           R_xU LN_xU NX_xU W_xU D_xU SK_xU (inclb_incl _ _ XF_xUb) XX_xU NXc_xU IC_xU R17_xU R10_xU BEL_xU R11_xU R12_xU R13_xU R14_xU R15_xU
           R_mU LN_mU NX_mU SK_mU (inclb_incl _ _ XF_mUb) XX_mU W_mrU D_mrU _ _ _ _ _ _ _ _ _ _ r tp Q HC);
    rewrite ?CMCU_eq, ?DMU_eq; [exact W_mcU | exact E_msU | exact CHK_msU | exact NF_msU | exact NX_msU | exact FBC_msU | exact FBT_msU | exact ND_rU | apply Nat.leb_le; exact NO_rUb | exact OB_rU].
Qed.
Definition R_d__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ416f0SeS2cA1A3S8aScA5").
Local Strategy expand [R_d__R].
Definition r_d := Eval vm_compute in ((fun ro6__ : option (list leafA) => (match ro6__ with Some l => l | None => [] end)) R_d__R).
Definition r_d_0 := Eval vm_compute in (nth 0 r_d (mkLeafA ru1 RsCut)).
Definition R_f__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ3f270SbS2cZ4172cSeS2cA1A3A3S3eS2eS5eA1S5S82A1A2ScA5").
Local Strategy expand [R_f__R].
Definition r_f := Eval vm_compute in ((fun ro7__ : option (list leafA) => (match ro7__ with Some l => l | None => [] end)) R_f__R).
Definition r_f_0 := Eval vm_compute in (nth 0 r_f (mkLeafA (cD (factsR e3r) (la_state r_d_0)) RsCut)).
Definition r_f_1 := Eval vm_compute in (nth 1 r_f (mkLeafA (cD (factsR e3r) (la_state r_d_0)) RsCut)).
Lemma R_d : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ416f0SeS2cA1A3S8aScA5S11G0SbS6S82SeS6A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_d__R <: R_d__R = Some [r_d_0]). Qed.
Lemma LN_d : ltac2:(tb__ "0|0|
S0SdS1eS4S8aA1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_d : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4S8aA1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_d : ltac2:(tb__ "0|0|
S0SdS1dS4S3eS2eS5eA1S5S82A1A2A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_d : ltac2:(tb__ "0|5|
S0S12S10SfS10S18S18A2M0A1M1SfS19A1M2A2M3A1Sb8S4S5S82A1M4A1S4S3eS2eS5eA1G4A2A1A2S11G3S13G1G2SbG0S13S18S18Sf1S5cA4SeG0A1A3S5bA4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_d : ltac2:(tb__ "0|1|
S0SdS68S1aS4S3eS2eS5eA1S5S82A1M0A2A1A1S1aS4G0A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_f : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ3f270SbS2cZ4172cSeS2cA1A3A3S3eS2eS5eA1S5S82A1A2ScA5S11G0SbS6S83SbS6S85SeS6A1A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_f__R <: R_f__R = Some [r_f_0; r_f_1]). Qed.
Lemma LN_f : ltac2:(tb__ "0|0|
S0SdS1eS4S3eS2eS5eA1S5S82A1A2A1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_f : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4S3eS2eS5eA1S5S82A1A2A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma F0_inb : ltac2:(tb__ "0|0|
S0SdS65SbS19Sf0SeS19A1A3S1cS4S5S83A1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma Fm_inb : ltac2:(tb__ "0|0|
S0SdS65SbS19S23Sf0A1SeS19A1A3S1cS4S5S85A1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma mid_i : ltac2:(tb__ "0|0|
SfdS61S6dS8aS5S83A1S5S85A1A5").
Proof.
  intros A Kc rb tp0 md0 TR KIT HKc rho HE PF ph r tp Q. cbn zeta.
  exact (populate_mid A Kc rb tp0 md0 TR KIT HKc W0 UStopLe rho HE PF ph FUEL e3r ru1 r_d_0 r_f_0 r_f_1 R_d LN_d NX_d W_d D_d NXe_d R_f LN_f NX_f (In_of_inclb _ _ F0_inb) (In_of_inclb _ _ Fm_inb) r tp Q).
Qed.
Definition cfm := Eval vm_compute in (cFm (la_state r_f_1)).
Lemma CFM_eq : ltac2:(tb__ "0|0|
S0SaS4aS5S85A1A1S84A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma W_fm : ltac2:(tb__ "0|0|
S0SdS1dS4S4aS5S85A1A1A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_fm : ltac2:(tb__ "0|5|
S0S12S10SfS10S18S18A2M0A1M1SfS19A1M2A2M3A1Sb8S4S5S85A1M4A1S4S4aG4A1A1A2S11G3S13G1G2SbG0S13S18S18Sf2S20Sb1S5aS1bZ40000A1A3A4SeG0A1A3SeS19A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma fm_i : ltac2:(tb__ "0|0|
SfbS61S6dS5S85A1S84A4").
Proof.
  rewrite <- CFM_eq. intros A Kc rb tp0 md0 TR KIT HKc rho HE PF ph r tp Q. cbn zeta.
  exact (famap_restate A Kc rb tp0 md0 TR KIT W0 UStopLe rho HE PF (la_state r_f_1) W_fm D_fm ph r tp Q).
Qed.
Definition R_xF__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ7050cSeS2cA1A3S84ScA5").
Local Strategy expand [R_xF__R].
Definition r_xF := Eval vm_compute in ((fun ro8__ : option (list leafA) => (match ro8__ with Some l => l | None => [] end)) R_xF__R).
Definition r_xF_0 := Eval vm_compute in (nth 0 r_xF (mkLeafA cfm RsCut)).
Definition R_mF__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZde378SeS2cA1A3SbfS2fS5S71A1S32A2S32Z40000A3ScA5").
Local Strategy expand [R_mF__R].
Definition r_mF := Eval vm_compute in ((fun ro9__ : option (list leafA) => (match ro9__ with Some l => l | None => [] end)) R_mF__R).
Definition r_mF_0 := Eval vm_compute in (nth 0 r_mF (mkLeafA (commit_post (cX (la_state r_xF_0) beg2) beg2 262144) RsCut)).
Definition cmcF := Eval vm_compute in (cMc (la_state r_mF_0) beg2).
Lemma CMCF_eq : ltac2:(tb__ "0|0|
S0SaScfS5S87A1S32A2S73A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Definition dmF := Eval vm_compute in (dMSf cmcF).
Lemma DMF_eq : ltac2:(tb__ "0|0|
S0SaSd0S73A1S8bA3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Definition rf1 := Eval vm_compute in (relM dmF).
Lemma RF1_eq : ltac2:(tb__ "0|0|
S0SaS56S8bA1S89A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R_xF : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ7050cSeS2cA1A3S84ScA5S11G0SbS6S71SeS6A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_xF__R <: R_xF__R = Some [r_xF_0]). Qed.
Lemma LN_xF : ltac2:(tb__ "0|0|
S0SdS1eS4S84A1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_xF : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4S84A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_xF : ltac2:(tb__ "0|0|
S0SdS1dS4S2fS5S71A1S32A2A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_xF : ltac2:(tb__ "0|5|
S0S12S10SfS10S18S18A2M0A1M1SfS19A1M2A2M3A1Sb8S4S5S71A1M4A1S4S2fG4S32A2A1A2S11G3S13G1G2SbG0S13S18S18SefS32A1S32A4SeG0A1A3SeS19A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma SK_xF : ltac2:(tb__ "0|1|
S0SfS10S10S18S18A2S18A2M0A1S69S17G0S66S1fS4S2fS5S71A1S32A2A1A1A4S69S17G0S66S14S17SbeS61A1SbS17Sb9SbS17SbaSbS17S38SbS17S3bSeS17A1A3A3A3A3A3A4A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_xFb : ltac2:(tb__ "0|0|
S0SdS65SbdS61S6dA2S1cS4S2fS5S71A1S32A2A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XX_xF : ltac2:(tb__ "0|1|
S0SfS10S18S18A2M0A1S9S2fS5S71A1S32A2A1SeG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXc_xF : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4S2fS5S71A1S32A2A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma IC_xF : ltac2:(tb__ "0|0|
S0S12Sb3A1Se9S2dS29S4S2fS5S71A1S32A2A1A1A2S11Sb3Sb6A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R17_xF : ltac2:(tb__ "0|0|
S0S18S22S4S2fS5S71A1S32A2A1Z11A2S1bZdeA1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R10_xF : ltac2:(tb__ "0|0|
S0S18S22S4S2fS5S71A1S32A2A1ZaA2S32A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R11_xF : ltac2:(tb__ "0|0|
S0S18S22S4S2fS5S71A1S32A2A1ZbA2S1bZ40000A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R12_xF : ltac2:(tb__ "0|0|
S0S18S22S4S2fS5S71A1S32A2A1ZcA2S1bZ3A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R13_xF : ltac2:(tb__ "0|0|
S0S18S22S4S2fS5S71A1S32A2A1ZdA2S1bZ32A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R14_xF : ltac2:(tb__ "0|0|
S0S18S22S4S2fS5S71A1S32A2A1ZeA2S1bZffffffffffffffffA1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R15_xF : ltac2:(tb__ "0|0|
S0S18S22S4S2fS5S71A1S32A2A1ZfA2S1bZ0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma BEL_xF : ltac2:(tb__ "0|0|
S0SdS2aS1aS4S2fS5S71A1S32A2A1A1S32A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_mF : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZde378SeS2cA1A3SbfS2fS5S71A1S32A2S32Z40000A3ScA5S11G0SbS6S87SeS6A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_mF__R <: R_mF__R = Some [r_mF_0]). Qed.
Lemma LN_mF : ltac2:(tb__ "0|0|
S0SdS1eS4SbfS2fS5S71A1S32A2S32Z40000A3A1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_mF : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4SbfS2fS5S71A1S32A2S32Z40000A3A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SK_mF : ltac2:(tb__ "0|1|
S0SfS10S10S18S18A2S18A2M0A1S69S17G0S66S1fS4S5S87A1A1A1A4S69S17G0S66S14S17SbeS61A1SbS17Sb9SbS17SbaSbS17S38SbS17S3bSbS17SdeS32A1SeS17A1A3A3A3A3A3A3A4A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_mFb : ltac2:(tb__ "0|0|
S0SdS65SbdS61S6dA2S1cS4S5S87A1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XX_mF : ltac2:(tb__ "0|1|
S0SfS10S18S18A2M0A1S9S5S87A1A1SeG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma W_mrF : ltac2:(tb__ "0|0|
S0SdS1dS4ScdS5S87A1A1A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_mrF : ltac2:(tb__ "0|5|
S0S12S10SfS10S18S18A2M0A1M1SfS19A1M2A2M3A1Sb8S4S5S87A1M4A1S4ScdG4A1A1A2S11G3S13G1G2SbG0S13S18S18SceS32A1S1bZ8000A1A4SeG0A1A3SeS19A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma W_mcF : ltac2:(tb__ "0|0|
S0SdS1dS4S73A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma E_msF : ltac2:(tb__ "0|1|
S0S12SfS17A1M0A1SedS73Sc5S46S73A1A3S11G0S45S73A1A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma CHK_msF : ltac2:(tb__ "0|0|
S0SdSecS73Sc5S46S73A1S45S73A1S69S6SaS5Sc6A4A5ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NF_msF : ltac2:(tb__ "0|0|
S0SdS67Sc7S1aS4S73A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NX_msF : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4S73A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBC_msF : ltac2:(tb__ "0|1|
S0SdSc2S19S25S1aS4S73A1M0A1A1S1cG0A1A3ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT_msF : ltac2:(tb__ "0|0|
S0SdSc2S19S25S1aS4Sc0S73S46S73A1S45S73A1A3A1A1A1S1cS4S73A1A1A3ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ND_rF : ltac2:(tb__ "0|0|
S0SdSe8S54S8bA1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NO_rFb : ltac2:(tb__ "0|0|
S0SdS102U1S44S8bA1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma OB_rF : ltac2:(tb__ "0|1|
S0SfS17A1S1fS4S58S8bA1A1A1M0S14S17S6aS17Sc4S44S8bA1U2A2G0A3SbS17SdeS32A1SbS17SdfS32A1SeS17A1A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma pieceF_i : ltac2:(tb__ "0|0|
SfaS61S6dS103S32S84S89A6").
Proof.
  rewrite <- RF1_eq, <- DMF_eq, <- CMCF_eq.
  intros A Kc rb tp0 md0 TR KIT HKc rho HE ph PH0 PORD PQ HBv HBn HRc HRr r tp Q HC.
  refine (piece_full A Kc rb tp0 md0 TR KIT HKc W0 UStopLe rho HW0 HE OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.CRefillJP.PF beg2 ph PH0 PORD PQ HBv HBn HRc HRr FUEL cfm r_xF_0 r_mF_0
           R_xF LN_xF NX_xF W_xF D_xF SK_xF (inclb_incl _ _ XF_xFb) XX_xF NXc_xF IC_xF R17_xF R10_xF BEL_xF R11_xF R12_xF R13_xF R14_xF R15_xF
           R_mF LN_mF NX_mF SK_mF (inclb_incl _ _ XF_mFb) XX_mF W_mrF D_mrF _ _ _ _ _ _ _ _ _ _ r tp Q HC);
    rewrite ?CMCF_eq, ?DMF_eq; [exact W_mcF | exact E_msF | exact CHK_msF | exact NF_msF | exact NX_msF | exact FBC_msF | exact FBT_msF | exact ND_rF | apply Nat.leb_le; exact NO_rFb | exact OB_rF].
Qed.
Definition R_h__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ4172cSeS2cA1A3S89ScA5").
Local Strategy expand [R_h__R].
Definition r_h := Eval vm_compute in ((fun ro10__ : option (list leafA) => (match ro10__ with Some l => l | None => [] end)) R_h__R).
Definition r_h_0 := Eval vm_compute in (nth 0 r_h (mkLeafA rf1 RsCut)).
Lemma R_h : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ4172cSeS2cA1A3S89ScA5S11G0SbS6S86SeS6A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_h__R <: R_h__R = Some [r_h_0]). Qed.
Lemma LN_h : ltac2:(tb__ "0|0|
S0SdS1eS4S89A1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_h : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4S89A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma run_i : ltac2:(tb__ "0|0|
S100S89S5S86A1A2").
Proof.
  intros A Kc rb tp0 md0 TR KIT HKc ph r tp Q HC.
  apply (jr_run A Kc rb tp0 md0 TR KIT HKc FUEL [0x4172c] rf1 [r_h_0] ph r tp Q R_h LN_h NX_h).
  intros L r1 [<-|[]] _. exact (HC r1).
Qed.
Definition R_fhP__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ41740SeS2cA1A3S5S83A1ScA5").
Local Strategy expand [R_fhP__R].
Definition r_flP := Eval vm_compute in ((fun ro12__ : option (list leafA) => (match ro12__ with Some l => l | None => [] end)) R_fhP__R).
Definition r_flP_0 := Eval vm_compute in (nth 0 r_flP (mkLeafA (la_state r_f_0) RsCut)).
Definition cl0P := Eval vm_compute in (cL0 (factsR e3r) (la_state r_flP_0)).
Definition R_l1P__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ41740SbS2cZ4174cSeS2cA1A3A3S3cS78A1ScA5").
Local Strategy expand [R_l1P__R].
Definition r_lP := Eval vm_compute in ((fun ro11__ : option (list leafA) => (match ro11__ with Some l => l | None => [] end)) R_l1P__R).
Definition r_lP_0 := Eval vm_compute in (nth 0 r_lP (mkLeafA (cL1 cl0P) RsCut)).
Definition r_lP_1 := Eval vm_compute in (nth 1 r_lP (mkLeafA (cL1 cl0P) RsCut)).
Definition nobFP := Eval vm_compute in (length (ss_objs (ax_S cl0P))).
Definition s_fbkP := Eval vm_compute in (infer_sub GR (ax_S (keepn (la_state r_lP_0) nobFP)) (ax_S cl0P)).
Definition s_finP := Eval vm_compute in (infer_sub GR (ax_S (la_state r_flP_0)) (ax_S cl0P)).
Definition R_fjP__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ413ccSeS2cA1A3S37S2eS5eA1S35S5S7fA1S7dA2A2ScA5").
Local Strategy expand [R_fjP__R].
Definition r_jP := Eval vm_compute in ((fun ro13__ : option (list leafA) => (match ro13__ with Some l => l | None => [] end)) R_fjP__R).
Definition r_jP_0 := Eval vm_compute in (nth 0 r_jP (mkLeafA (cXL (factsR e3r) (keepn (la_state r_lP_1) nobFP)) RsCut)).
Lemma SK_lP : ltac2:(tb__ "0|1|
S0SfS10S10S18S18A2S18A2M0A1S69S17G0S66S1fS4S78A1A1A4S69S17G0S66S14S17SbeS61A1SbS17Sb9SbS17SbaSbS17S38SbS17S3bSeS17A1A3A3A3A3A3A4A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XX_lP : ltac2:(tb__ "0|1|
S0SfS10S18S18A2M0A1S9S78A1SeG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_lPb : ltac2:(tb__ "0|0|
S0SdS65SbdS61S6dA2S1cS4S78A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NX_lP : ltac2:(tb__ "0|0|
S0SdS68S1aS4S78A1A1S50A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_l1P : ltac2:(tb__ "0|0|
S0SdS1dS4S3cS78A1A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_l1P : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ41740SbS2cZ4174cSeS2cA1A3A3S3cS78A1ScA5S11G0SbS6S98SbS6S7fSeS6A1A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_l1P__R <: R_l1P__R = Some [r_lP_0; r_lP_1]). Qed.
Lemma LN_l1P : ltac2:(tb__ "0|0|
S0SdS1eS4S3cS78A1A1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma OB_fbP : ltac2:(tb__ "0|1|
S0SfS17A1S1fS4S5S98A1A1A1M0S14S17S6aS17S7dG0A3SbS17Sd2SeS17A1A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_fxP : ltac2:(tb__ "0|1|
S0SfS17A1S1fS4S5S7fA1A1A1M0S14S17S6aS17S7dG0A3SbS17Sd2SeS17A1A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma ENT_fbkP : ltac2:(tb__ "0|0|
S0SdS8S35S5S98A1S7dA2S78S94A3ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_fbkP : ltac2:(tb__ "0|0|
S0SdS6cS94S30A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma S_bk0P : ltac2:(tb__ "0|0|
S0S18S6bS94S3aA2S20Sb1S21S3aA1S1bZ1A1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S_bk2P : ltac2:(tb__ "0|0|
S0S18S6bS94S41A2S20Sb1S21S41A1S21SbbA1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S_bk3P : ltac2:(tb__ "0|0|
S0S18S6bS94S47A2S20Sb1Sd3S20Sb4S20Sb5S21S3aA1S1bZffffffffffffffffA1A3S1bZ2A1A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma FB_fbPb : ltac2:(tb__ "0|0|
S0SdS65SbS19Sd1SeS19A1A3S1cS4S5S98A1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FB_fxPb : ltac2:(tb__ "0|0|
S0SdS65SbS19S23Sd1A1SeS19A1A3S1cS4S5S7fA1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_fhP : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ41740SeS2cA1A3S5S83A1ScA5S11G0SbS6Sa6SeS6A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_fhP__R <: R_fhP__R = Some [r_flP_0]). Qed.
Lemma LN_fhP : ltac2:(tb__ "0|0|
S0SdS1eS4S5S83A1A1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_fhP : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4S5S83A1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_finP : ltac2:(tb__ "0|0|
S0SdS8S5Sa6A1S78S96A3ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_finP : ltac2:(tb__ "0|0|
S0SdS6cS96S30A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma S_in0P : ltac2:(tb__ "0|0|
S0S18S6bS96S3aA2S1bZ1A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S_in2P : ltac2:(tb__ "0|0|
S0S18S6bS96S41A2S59A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S_in3P : ltac2:(tb__ "0|0|
S0S18S6bS96S47A2S20Sb1Sd3S1bN4A1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma W_xlP : ltac2:(tb__ "0|0|
S0SdS1dS4S37S2eS5eA1S35S5S7fA1S7dA2A2A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_xlP : ltac2:(tb__ "0|5|
S0S12S10SfS10S18S18A2M0A1M1SfS19A1M2A2M3A1Sb8S4S35S5S7fA1S7dA2M4A1S4S37S2eS5eA1G4A2A1A2S11G3S13G1G2SeG0A1SbS19S4dSbS19S4eSeS19A1A3A3A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_xlP : ltac2:(tb__ "0|1|
S0SdS68S1aS4S37S2eS5eA1S35S5S7fA1S7dA2M0A2A1A1S1aS4G0A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_fjP : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ413ccSeS2cA1A3S37S2eS5eA1S35S5S7fA1S7dA2A2ScA5S11G0SbS6S8eSeS6A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_fjP__R <: R_fjP__R = Some [r_jP_0]). Qed.
Lemma LN_fxlP : ltac2:(tb__ "0|0|
S0SdS1eS4S37S2eS5eA1S35S5S7fA1S7dA2A2A1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_fxlP : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4S37S2eS5eA1S35S5S7fA1S7dA2A2A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma fillP_i : ltac2:(tb__ "0|0|
Sf8S61S6dS5S83A1S5S8eA1A4").
Proof.
  intros A Kc rb tp0 md0 TR KIT HKc rho HE PF ph PQ HDEF r tp Q HC.
  exact (fill_all A Kc rb tp0 md0 TR KIT HKc W0 UStopLe rho HW0 HE PF ph PQ HDEF FUEL cl0P r_lP_0 r_lP_1 nobFP s_fbkP SK_lP XX_lP (inclb_incl _ _ XF_lPb) NX_lP W_l1P R_l1P LN_l1P
           OB_fbP OB_fxP ENT_fbkP SID_fbkP S_bk0P S_bk2P S_bk3P (In_of_inclb _ _ FB_fbPb) (In_of_inclb _ _ FB_fxPb) e3r (la_state r_f_0) r_flP_0 r_jP_0 s_finP
           R_fhP LN_fhP NX_fhP ENT_finP SID_finP S_in0P S_in2P S_in3P W_xlP D_xlP NXe_xlP R_fjP LN_fxlP NX_fxlP r tp Q HC).
Qed.
Definition R_fhM__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ41740SeS2cA1A3S5S86A1ScA5").
Local Strategy expand [R_fhM__R].
Definition r_flM := Eval vm_compute in ((fun ro15__ : option (list leafA) => (match ro15__ with Some l => l | None => [] end)) R_fhM__R).
Definition r_flM_0 := Eval vm_compute in (nth 0 r_flM (mkLeafA (la_state r_h_0) RsCut)).
Definition cl0M := Eval vm_compute in (cL0 (factsR e3r) (la_state r_flM_0)).
Definition R_l1M__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ41740SbS2cZ4174cSeS2cA1A3A3S3cS77A1ScA5").
Local Strategy expand [R_l1M__R].
Definition r_lM := Eval vm_compute in ((fun ro14__ : option (list leafA) => (match ro14__ with Some l => l | None => [] end)) R_l1M__R).
Definition r_lM_0 := Eval vm_compute in (nth 0 r_lM (mkLeafA (cL1 cl0M) RsCut)).
Definition r_lM_1 := Eval vm_compute in (nth 1 r_lM (mkLeafA (cL1 cl0M) RsCut)).
Definition nobFM := Eval vm_compute in (length (ss_objs (ax_S cl0M))).
Definition s_fbkM := Eval vm_compute in (infer_sub GR (ax_S (keepn (la_state r_lM_0) nobFM)) (ax_S cl0M)).
Definition s_finM := Eval vm_compute in (infer_sub GR (ax_S (la_state r_flM_0)) (ax_S cl0M)).
Definition R_fjM__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ413ccSeS2cA1A3S37S2eS5eA1S35S5S7eA1S7cA2A2ScA5").
Local Strategy expand [R_fjM__R].
Definition r_jM := Eval vm_compute in ((fun ro16__ : option (list leafA) => (match ro16__ with Some l => l | None => [] end)) R_fjM__R).
Definition r_jM_0 := Eval vm_compute in (nth 0 r_jM (mkLeafA (cXL (factsR e3r) (keepn (la_state r_lM_1) nobFM)) RsCut)).
Lemma SK_lM : ltac2:(tb__ "0|1|
S0SfS10S10S18S18A2S18A2M0A1S69S17G0S66S1fS4S77A1A1A4S69S17G0S66S14S17SbeS61A1SbS17Sb9SbS17SbaSbS17S38SbS17S3bSeS17A1A3A3A3A3A3A4A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XX_lM : ltac2:(tb__ "0|1|
S0SfS10S18S18A2M0A1S9S77A1SeG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_lMb : ltac2:(tb__ "0|0|
S0SdS65SbdS61S6dA2S1cS4S77A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NX_lM : ltac2:(tb__ "0|0|
S0SdS68S1aS4S77A1A1S50A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_l1M : ltac2:(tb__ "0|0|
S0SdS1dS4S3cS77A1A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_l1M : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ41740SbS2cZ4174cSeS2cA1A3A3S3cS77A1ScA5S11G0SbS6S97SbS6S7eSeS6A1A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_l1M__R <: R_l1M__R = Some [r_lM_0; r_lM_1]). Qed.
Lemma LN_l1M : ltac2:(tb__ "0|0|
S0SdS1eS4S3cS77A1A1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma OB_fbM : ltac2:(tb__ "0|1|
S0SfS17A1S1fS4S5S97A1A1A1M0S14S17S6aS17S7cG0A3SbS17Sd2SeS17A1A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_fxM : ltac2:(tb__ "0|1|
S0SfS17A1S1fS4S5S7eA1A1A1M0S14S17S6aS17S7cG0A3SbS17Sd2SeS17A1A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma ENT_fbkM : ltac2:(tb__ "0|0|
S0SdS8S35S5S97A1S7cA2S77S93A3ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_fbkM : ltac2:(tb__ "0|0|
S0SdS6cS93S30A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma S_bk0M : ltac2:(tb__ "0|0|
S0S18S6bS93S3aA2S20Sb1S21S3aA1S1bZ1A1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S_bk2M : ltac2:(tb__ "0|0|
S0S18S6bS93S41A2S20Sb1S21S41A1S21SbbA1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S_bk3M : ltac2:(tb__ "0|0|
S0S18S6bS93S47A2S20Sb1Sd3S20Sb4S20Sb5S21S3aA1S1bZffffffffffffffffA1A3S1bZ2A1A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma FB_fbMb : ltac2:(tb__ "0|0|
S0SdS65SbS19Sd1SeS19A1A3S1cS4S5S97A1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FB_fxMb : ltac2:(tb__ "0|0|
S0SdS65SbS19S23Sd1A1SeS19A1A3S1cS4S5S7eA1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_fhM : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ41740SeS2cA1A3S5S86A1ScA5S11G0SbS6Sa5SeS6A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_fhM__R <: R_fhM__R = Some [r_flM_0]). Qed.
Lemma LN_fhM : ltac2:(tb__ "0|0|
S0SdS1eS4S5S86A1A1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_fhM : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4S5S86A1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_finM : ltac2:(tb__ "0|0|
S0SdS8S5Sa5A1S77S95A3ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_finM : ltac2:(tb__ "0|0|
S0SdS6cS95S30A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma S_in0M : ltac2:(tb__ "0|0|
S0S18S6bS95S3aA2S1bZ1A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S_in2M : ltac2:(tb__ "0|0|
S0S18S6bS95S41A2S59A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S_in3M : ltac2:(tb__ "0|0|
S0S18S6bS95S47A2S20Sb1Sd3S1bN4A1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma W_xlM : ltac2:(tb__ "0|0|
S0SdS1dS4S37S2eS5eA1S35S5S7eA1S7cA2A2A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_xlM : ltac2:(tb__ "0|5|
S0S12S10SfS10S18S18A2M0A1M1SfS19A1M2A2M3A1Sb8S4S35S5S7eA1S7cA2M4A1S4S37S2eS5eA1G4A2A1A2S11G3S13G1G2SeG0A1SbS19S4dSbS19S4eSeS19A1A3A3A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_xlM : ltac2:(tb__ "0|1|
S0SdS68S1aS4S37S2eS5eA1S35S5S7eA1S7cA2M0A2A1A1S1aS4G0A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_fjM : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ413ccSeS2cA1A3S37S2eS5eA1S35S5S7eA1S7cA2A2ScA5S11G0SbS6S8dSeS6A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_fjM__R <: R_fjM__R = Some [r_jM_0]). Qed.
Lemma LN_fxlM : ltac2:(tb__ "0|0|
S0SdS1eS4S37S2eS5eA1S35S5S7eA1S7cA2A2A1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_fxlM : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4S37S2eS5eA1S35S5S7eA1S7cA2A2A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma fillM_i : ltac2:(tb__ "0|0|
Sf8S61S6dS5S86A1S5S8dA1A4").
Proof.
  intros A Kc rb tp0 md0 TR KIT HKc rho HE PF ph PQ HDEF r tp Q HC.
  exact (fill_all A Kc rb tp0 md0 TR KIT HKc W0 UStopLe rho HW0 HE PF ph PQ HDEF FUEL cl0M r_lM_0 r_lM_1 nobFM s_fbkM SK_lM XX_lM (inclb_incl _ _ XF_lMb) NX_lM W_l1M R_l1M LN_l1M
           OB_fbM OB_fxM ENT_fbkM SID_fbkM S_bk0M S_bk2M S_bk3M (In_of_inclb _ _ FB_fbMb) (In_of_inclb _ _ FB_fxMb) e3r (la_state r_h_0) r_flM_0 r_jM_0 s_finM
           R_fhM LN_fhM NX_fhM ENT_finM SID_finM S_in0M S_in2M S_in3M W_xlM D_xlM NXe_xlM R_fjM LN_fxlM NX_fxlM r tp Q HC).
Qed.
Definition R_t0P__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ413dcSbS2cZ413f0SeS2cA1A3A3S5S8eA1ScA5").
Local Strategy expand [R_t0P__R].
Definition r_t0P := Eval vm_compute in ((fun ro18__ : option (list leafA) => (match ro18__ with Some l => l | None => [] end)) R_t0P__R).
Definition r_t0P_0 := Eval vm_compute in (nth 0 r_t0P (mkLeafA (la_state r_jP_0) RsCut)).
Definition ct0P := Eval vm_compute in (cT0 (la_state r_t0P_0)).
Definition R_t1P__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ413dcSbS2cZ413f0SeS2cA1A3A3S3dS7bA1ScA5").
Local Strategy expand [R_t1P__R].
Definition r_t1P := Eval vm_compute in ((fun ro17__ : option (list leafA) => (match ro17__ with Some l => l | None => [] end)) R_t1P__R).
Definition r_t1P_0 := Eval vm_compute in (nth 0 r_t1P (mkLeafA (cT1 ct0P) RsCut)).
Definition r_t1P_1 := Eval vm_compute in (nth 1 r_t1P (mkLeafA (cT1 ct0P) RsCut)).
Definition s_inP := Eval vm_compute in (infer_sub GR (ax_S (la_state r_t0P_0)) (ax_S ct0P)).
Definition s_bkP := Eval vm_compute in (infer_sub GR (ax_S (keepn (la_state r_t1P_0) nob)) (ax_S ct0P)).
Lemma SK_tP : ltac2:(tb__ "0|1|
S0SfS10S10S18S18A2S18A2M0A1S69S17G0S66S1fS4S7bA1A1A4S69S17G0S66S14S17SbeS61A1SbS17Sb9SbS17SbaSbS17S38SbS17S3bSeS17A1A3A3A3A3A3A4A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XX_tP : ltac2:(tb__ "0|1|
S0SfS10S18S18A2M0A1S9S7bA1SeG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_tPb : ltac2:(tb__ "0|0|
S0SdS65SbdS61S6dA2S1cS4S7bA1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NX_tP : ltac2:(tb__ "0|0|
S0SdS68S1aS4S7bA1A1S52A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_t1P : ltac2:(tb__ "0|0|
S0SdS1dS4S3dS7bA1A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_t1P : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ413dcSbS2cZ413f0SeS2cA1A3A3S3dS7bA1ScA5S11G0SbS6S9aSbS6Sa2SeS6A1A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_t1P__R <: R_t1P__R = Some [r_t1P_0; r_t1P_1]). Qed.
Lemma LN_t1P : ltac2:(tb__ "0|0|
S0SdS1eS4S3dS7bA1A1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma OB_bP : ltac2:(tb__ "0|1|
S0SfS17A1S1fS4S5S9aA1A1A1M0S14S17S6aS17S63G0A3SbS17Sd5SbS17Sd4SeS17A1A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_xP : ltac2:(tb__ "0|1|
S0SfS17A1S1fS4S5Sa2A1A1A1M0S14S17S6aS17S63G0A3SbS17Sd5SbS17Sd4SeS17A1A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma ENT_bkP : ltac2:(tb__ "0|0|
S0SdS8S35S5S9aA1S63A2S7bS9cA3ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_bkP : ltac2:(tb__ "0|0|
S0SdS6cS9cS30A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma S_bk4P : ltac2:(tb__ "0|0|
S0S18S6bS9cS39A2S20Sb1S21S39A1S1bZ4A1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S_bk6P : ltac2:(tb__ "0|0|
S0S18S6bS9cS42A2S20Sb1S21S42A1S1bZ4A1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma FB_bPb : ltac2:(tb__ "0|0|
S0SdS65SbS19S26Sb2S20Sb1S21S39A1S1bZ4A1A3Sd6A3SeS19A1A3S1cS4S5S9aA1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FB_xPb : ltac2:(tb__ "0|0|
S0SdS65SbS19S23S26Sb2S20Sb1S21S39A1S1bZ4A1A3Sd6A3A1SeS19A1A3S1cS4S5Sa2A1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_t0P : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ413dcSbS2cZ413f0SeS2cA1A3A3S5S8eA1ScA5S11G0SbS6Sa8SeS6A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_t0P__R <: R_t0P__R = Some [r_t0P_0]). Qed.
Lemma LN_t0P : ltac2:(tb__ "0|0|
S0SdS1eS4S5S8eA1A1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_t0P : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4S5S8eA1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_inP : ltac2:(tb__ "0|0|
S0SdS8S5Sa8A1S7bS9eA3ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_inP : ltac2:(tb__ "0|0|
S0SdS6cS9eS30A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma S_in4P : ltac2:(tb__ "0|0|
S0S18S6bS9eS39A2S20Sb1SbcS1bZ10A1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S_in6P : ltac2:(tb__ "0|0|
S0S18S6bS9eS42A2Sf6A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Definition xlP := Eval vm_compute in (keepn (la_state r_t1P_1) nob).
Definition R_9P__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ40cc8SeS2cA1A3Sa0ScA5").
Local Strategy expand [R_9P__R].
Definition r_9P := Eval vm_compute in ((fun ro19__ : option (list leafA) => (match ro19__ with Some l => l | None => [] end)) R_9P__R).
Definition r_9P_0 := Eval vm_compute in (nth 0 r_9P (mkLeafA xlP RsCut)).
Definition cellsfP := Eval vm_compute in (ob_cells (last (ss_objs (ax_S (cE1 (la_state r_9P_0) icc))) O_ri)).
Definition x3P := Eval vm_compute in (cE3 (cE2 (cE1 (la_state r_9P_0) icc))).
Definition r_zP := Eval vm_compute in (match sym_runA segsA FUEL [0x3c480] x3P true with Some l => l | None => [] end).
Definition r_zP_0 := Eval vm_compute in (nth 0 r_zP (mkLeafA x3P RsCut)).
Lemma R_9P : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ40cc8SeS2cA1A3Sa0ScA5S11G0SbS6S76SeS6A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_9P__R <: R_9P__R = Some [r_9P_0]). Qed.
Lemma LN_9P : ltac2:(tb__ "0|0|
S0SdS1eS4Sa0A1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_9P : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4Sa0A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_x1P : ltac2:(tb__ "0|0|
S0SdS1dS4S33S5S76A1S60A2A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_x1P : ltac2:(tb__ "0|5|
S0S12S10SfS10S18S18A2M0A1M1SfS19A1M2A2M3A1Sb8S4S5S76A1M4A1S4S33G4S60A2A1A2S11G3S13G1G2SbG0S13S18S18S55S4bA4SeG0A1A3SeS19A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NX_x1P : ltac2:(tb__ "0|1|
S0SdS68S1aS4S33S5S76A1M0S60A2A1A1S1aS4G0A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XX_1P : ltac2:(tb__ "0|1|
S0SfS10S18S18A2M0A1S9S33S5S76A1S60A2A1SeG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma IC_1P : ltac2:(tb__ "0|0|
S0S12S17A1Sc3S17S1fS4S33S5S76A1S60A2A1A1S60A3S11S17S51A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_1P : ltac2:(tb__ "0|2|
S0SfS17A1S1fS4S33S5S76A1S60A2M0A1A1M1S14S17S6aS17Sc4S44G0A1U2A2G1A3SbS17S38SbS17S101Sa4A1SeS17A1A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_1P : ltac2:(tb__ "0|0|
S0SdS57Sa4Sf3S5aSf4Sf5A5ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SK_2P : ltac2:(tb__ "0|1|
S0SfS10S10S18S18A2S18A2M0A1S69S17G0S66S1fS4S34S33S5S76A1S60A2A1A1A1A4S69S17G0S66S14S17SbeS61A1SbS17Sb9SbS17SbaSeS17A1A3A3A3A4A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XX_2P : ltac2:(tb__ "0|1|
S0SfS10S18S18A2M0A1S9S34S33S5S76A1S60A2A1A1SeG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_2Pb : ltac2:(tb__ "0|0|
S0SdS65SbdS61S6dA2S1cS4S34S33S5S76A1S60A2A1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_3aP : ltac2:(tb__ "0|0|
S0SdS1dS4S53S34S33S5S76A1S60A2A1A1A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_3bP : ltac2:(tb__ "0|0|
S0SdS1dS4S48S34S33S5S76A1S60A2A1A1A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FB_3P : ltac2:(tb__ "0|1|
S0SdSc2S19S25S1aS4S48S34S33S5S76A1S60A2A1A1A1M0A1A1S14S19S4cS1cG0A1A3A3ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_zP : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ3c480SeS2cA1A3S43S34S33S5S76A1S60A2A1A1ScA5S11G0SbS6SaaSeS6A1A3A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma LN_zP : ltac2:(tb__ "0|0|
S0SdS1eS4S43S34S33S5S76A1S60A2A1A1A1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_zP : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4S43S34S33S5S76A1S60A2A1A1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Definition s_xP := Eval vm_compute in (s_exit (la_state r_zP_0) e3p).
Lemma ENT_xP : ltac2:(tb__ "0|0|
S0SdS8S5SaaA1S64Sb0A3ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SX_xP : sx_okb s_xP = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma S149_xP : wsub_get s_xP 149%positive = vK.
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S159_xP : wsub_get s_xP 159%positive = vCHX.
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Definition pop_P A Kc rb tp0 md0 TR KIT HKc rho HE ph PH0 faP HSRC HKF HNFP HFILLR HIDS HCACHE :=
  pop_all A Kc rb tp0 md0 TR KIT HKc W0 UStopLe rho HW0 HE ph PH0 faP HSRC HKF HNFP HFILLR HIDS HCACHE FUEL ct0P r_t1P_0 r_t1P_1 nob s_bkP
    SK_tP XX_tP (inclb_incl _ _ XF_tPb) NX_tP W_t1P R_t1P LN_t1P OB_bP OB_xP ENT_bkP SID_bkP S_bk4P S_bk6P (In_of_inclb _ _ FB_bPb) (In_of_inclb _ _ FB_xPb)
    (la_state r_jP_0) r_t0P_0 s_inP e_srcP R_t0P LN_t0P NX_t0P ENT_inP SID_inP S_in4P S_in6P.
Definition exit_P A Kc rb tp0 md0 TR KIT HKc rho HE phX PHX HFILLX Hini HRIv HLEN HIDC :=
  exit_steps A Kc rb tp0 md0 TR KIT HKc W0 UStopLe rho HW0 HE phX PHX HFILLX Hini e16P vMFA e32P e48P HRIv HLEN HIDC FUEL xlP r_9P_0 r_zP_0 icc cellsfP
    R_9P LN_9P NX_9P W_x1P D_x1P NX_x1P XX_1P IC_1P OB_1P RI_1P SK_2P XX_2P (inclb_incl _ _ XF_2Pb) W_3aP W_3bP FB_3P R_zP LN_zP NX_zP.
Definition back_P CST XGL PFam HPF A Kc rb tp0 md0 TR KIT rho HW HE phF HREB HMK HLEN HPOP :=
  refill_back CST XGL PFam HPF A Kc rb tp0 md0 TR KIT W0 UStopLe rho HW HE phF HREB HMK HLEN e3p (la_state r_zP_0) s_xP ENT_xP SX_xP S149_xP S159_xP HPOP.
Definition R_t0M__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ413dcSbS2cZ413f0SeS2cA1A3A3S5S8dA1ScA5").
Local Strategy expand [R_t0M__R].
Definition r_t0M := Eval vm_compute in ((fun ro21__ : option (list leafA) => (match ro21__ with Some l => l | None => [] end)) R_t0M__R).
Definition r_t0M_0 := Eval vm_compute in (nth 0 r_t0M (mkLeafA (la_state r_jM_0) RsCut)).
Definition ct0M := Eval vm_compute in (cT0 (la_state r_t0M_0)).
Definition R_t1M__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ413dcSbS2cZ413f0SeS2cA1A3A3S3dS7aA1ScA5").
Local Strategy expand [R_t1M__R].
Definition r_t1M := Eval vm_compute in ((fun ro20__ : option (list leafA) => (match ro20__ with Some l => l | None => [] end)) R_t1M__R).
Definition r_t1M_0 := Eval vm_compute in (nth 0 r_t1M (mkLeafA (cT1 ct0M) RsCut)).
Definition r_t1M_1 := Eval vm_compute in (nth 1 r_t1M (mkLeafA (cT1 ct0M) RsCut)).
Definition s_inM := Eval vm_compute in (infer_sub GR (ax_S (la_state r_t0M_0)) (ax_S ct0M)).
Definition s_bkM := Eval vm_compute in (infer_sub GR (ax_S (keepn (la_state r_t1M_0) nob)) (ax_S ct0M)).
Lemma SK_tM : ltac2:(tb__ "0|1|
S0SfS10S10S18S18A2S18A2M0A1S69S17G0S66S1fS4S7aA1A1A4S69S17G0S66S14S17SbeS61A1SbS17Sb9SbS17SbaSbS17S38SbS17S3bSeS17A1A3A3A3A3A3A4A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XX_tM : ltac2:(tb__ "0|1|
S0SfS10S18S18A2M0A1S9S7aA1SeG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_tMb : ltac2:(tb__ "0|0|
S0SdS65SbdS61S6dA2S1cS4S7aA1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NX_tM : ltac2:(tb__ "0|0|
S0SdS68S1aS4S7aA1A1S52A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_t1M : ltac2:(tb__ "0|0|
S0SdS1dS4S3dS7aA1A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_t1M : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ413dcSbS2cZ413f0SeS2cA1A3A3S3dS7aA1ScA5S11G0SbS6S99SbS6Sa1SeS6A1A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_t1M__R <: R_t1M__R = Some [r_t1M_0; r_t1M_1]). Qed.
Lemma LN_t1M : ltac2:(tb__ "0|0|
S0SdS1eS4S3dS7aA1A1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma OB_bM : ltac2:(tb__ "0|1|
S0SfS17A1S1fS4S5S99A1A1A1M0S14S17S6aS17S63G0A3SbS17Sd5SbS17Sd4SeS17A1A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_xM : ltac2:(tb__ "0|1|
S0SfS17A1S1fS4S5Sa1A1A1A1M0S14S17S6aS17S63G0A3SbS17Sd5SbS17Sd4SeS17A1A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma ENT_bkM : ltac2:(tb__ "0|0|
S0SdS8S35S5S99A1S63A2S7aS9bA3ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_bkM : ltac2:(tb__ "0|0|
S0SdS6cS9bS30A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma S_bk4M : ltac2:(tb__ "0|0|
S0S18S6bS9bS39A2S20Sb1S21S39A1S1bZ4A1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S_bk6M : ltac2:(tb__ "0|0|
S0S18S6bS9bS42A2S20Sb1S21S42A1S1bZ4A1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma FB_bMb : ltac2:(tb__ "0|0|
S0SdS65SbS19S26Sb2S20Sb1S21S39A1S1bZ4A1A3Sd6A3SeS19A1A3S1cS4S5S99A1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FB_xMb : ltac2:(tb__ "0|0|
S0SdS65SbS19S23S26Sb2S20Sb1S21S39A1S1bZ4A1A3Sd6A3A1SeS19A1A3S1cS4S5Sa1A1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_t0M : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ413dcSbS2cZ413f0SeS2cA1A3A3S5S8dA1ScA5S11G0SbS6Sa7SeS6A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_t0M__R <: R_t0M__R = Some [r_t0M_0]). Qed.
Lemma LN_t0M : ltac2:(tb__ "0|0|
S0SdS1eS4S5S8dA1A1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_t0M : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4S5S8dA1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_inM : ltac2:(tb__ "0|0|
S0SdS8S5Sa7A1S7aS9dA3ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_inM : ltac2:(tb__ "0|0|
S0SdS6cS9dS30A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma S_in4M : ltac2:(tb__ "0|0|
S0S18S6bS9dS39A2S20Sb1SbcS1bZ10A1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S_in6M : ltac2:(tb__ "0|0|
S0S18S6bS9dS42A2Sf6A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Definition xlM := Eval vm_compute in (keepn (la_state r_t1M_1) nob).
Definition R_9M__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ40cc8SeS2cA1A3S9fScA5").
Local Strategy expand [R_9M__R].
Definition r_9M := Eval vm_compute in ((fun ro22__ : option (list leafA) => (match ro22__ with Some l => l | None => [] end)) R_9M__R).
Definition r_9M_0 := Eval vm_compute in (nth 0 r_9M (mkLeafA xlM RsCut)).
Definition cellsfM := Eval vm_compute in (ob_cells (last (ss_objs (ax_S (cE1 (la_state r_9M_0) icc))) O_ri)).
Definition x3M := Eval vm_compute in (cE3 (cE2 (cE1 (la_state r_9M_0) icc))).
Definition r_zM := Eval vm_compute in (match sym_runA segsA FUEL [0x3c480] x3M true with Some l => l | None => [] end).
Definition r_zM_0 := Eval vm_compute in (nth 0 r_zM (mkLeafA x3M RsCut)).
Lemma R_9M : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ40cc8SeS2cA1A3S9fScA5S11G0SbS6S75SeS6A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_9M__R <: R_9M__R = Some [r_9M_0]). Qed.
Lemma LN_9M : ltac2:(tb__ "0|0|
S0SdS1eS4S9fA1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_9M : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4S9fA1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_x1M : ltac2:(tb__ "0|0|
S0SdS1dS4S33S5S75A1S60A2A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_x1M : ltac2:(tb__ "0|5|
S0S12S10SfS10S18S18A2M0A1M1SfS19A1M2A2M3A1Sb8S4S5S75A1M4A1S4S33G4S60A2A1A2S11G3S13G1G2SbG0S13S18S18S55S4bA4SeG0A1A3SeS19A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NX_x1M : ltac2:(tb__ "0|1|
S0SdS68S1aS4S33S5S75A1M0S60A2A1A1S1aS4G0A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XX_1M : ltac2:(tb__ "0|1|
S0SfS10S18S18A2M0A1S9S33S5S75A1S60A2A1SeG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma IC_1M : ltac2:(tb__ "0|0|
S0S12S17A1Sc3S17S1fS4S33S5S75A1S60A2A1A1S60A3S11S17S51A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_1M : ltac2:(tb__ "0|2|
S0SfS17A1S1fS4S33S5S75A1S60A2M0A1A1M1S14S17S6aS17Sc4S44G0A1U2A2G1A3SbS17S38SbS17S101Sa3A1SeS17A1A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_1M : ltac2:(tb__ "0|0|
S0SdS57Sa3Sf3Sf7Sf4Sf5A5ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SK_2M : ltac2:(tb__ "0|1|
S0SfS10S10S18S18A2S18A2M0A1S69S17G0S66S1fS4S34S33S5S75A1S60A2A1A1A1A4S69S17G0S66S14S17SbeS61A1SbS17Sb9SbS17SbaSeS17A1A3A3A3A4A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XX_2M : ltac2:(tb__ "0|1|
S0SfS10S18S18A2M0A1S9S34S33S5S75A1S60A2A1A1SeG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_2Mb : ltac2:(tb__ "0|0|
S0SdS65SbdS61S6dA2S1cS4S34S33S5S75A1S60A2A1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_3aM : ltac2:(tb__ "0|0|
S0SdS1dS4S53S34S33S5S75A1S60A2A1A1A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_3bM : ltac2:(tb__ "0|0|
S0SdS1dS4S48S34S33S5S75A1S60A2A1A1A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FB_3M : ltac2:(tb__ "0|1|
S0SdSc2S19S25S1aS4S48S34S33S5S75A1S60A2A1A1A1M0A1A1S14S19S4cS1cG0A1A3A3ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_zM : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ3c480SeS2cA1A3S43S34S33S5S75A1S60A2A1A1ScA5S11G0SbS6Sa9SeS6A1A3A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma LN_zM : ltac2:(tb__ "0|0|
S0SdS1eS4S43S34S33S5S75A1S60A2A1A1A1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_zM : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4S43S34S33S5S75A1S60A2A1A1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Definition s_xM := Eval vm_compute in (s_exit (la_state r_zM_0) e3p).
Lemma ENT_xM : ltac2:(tb__ "0|0|
S0SdS8S5Sa9A1S64SafA3ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SX_xM : sx_okb s_xM = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma S149_xM : wsub_get s_xM 149%positive = vK.
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S159_xM : wsub_get s_xM 159%positive = vCHX.
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Definition pop_M A Kc rb tp0 md0 TR KIT HKc rho HE ph PH0 faP HSRC HKF HNFP HFILLR HIDS HCACHE :=
  pop_all A Kc rb tp0 md0 TR KIT HKc W0 UStopLe rho HW0 HE ph PH0 faP HSRC HKF HNFP HFILLR HIDS HCACHE FUEL ct0M r_t1M_0 r_t1M_1 nob s_bkM
    SK_tM XX_tM (inclb_incl _ _ XF_tMb) NX_tM W_t1M R_t1M LN_t1M OB_bM OB_xM ENT_bkM SID_bkM S_bk4M S_bk6M (In_of_inclb _ _ FB_bMb) (In_of_inclb _ _ FB_xMb)
    (la_state r_jM_0) r_t0M_0 s_inM e_srcP R_t0M LN_t0M NX_t0M ENT_inM SID_inM S_in4M S_in6M.
Definition exit_M A Kc rb tp0 md0 TR KIT HKc rho HE phX PHX HFILLX Hini HRIv HLEN HIDC :=
  exit_steps A Kc rb tp0 md0 TR KIT HKc W0 UStopLe rho HW0 HE phX PHX HFILLX Hini e16P e24M e32P e48P HRIv HLEN HIDC FUEL xlM r_9M_0 r_zM_0 icc cellsfM
    R_9M LN_9M NX_9M W_x1M D_x1M NX_x1M XX_1M IC_1M OB_1M RI_1M SK_2M XX_2M (inclb_incl _ _ XF_2Mb) W_3aM W_3bM FB_3M R_zM LN_zM NX_zM.
Definition back_M CST XGL PFam HPF A Kc rb tp0 md0 TR KIT rho HW HE phF HREB HMK HLEN HPOP :=
  refill_back CST XGL PFam HPF A Kc rb tp0 md0 TR KIT W0 UStopLe rho HW HE phF HREB HMK HLEN e3p (la_state r_zM_0) s_xM ENT_xM SX_xM S149_xM S159_xM HPOP.

Theorem refill_populate_i : ltac2:(tb__ "0|4|
SfS10S2cS2cA2A1M0G0Se3S6eSfS10SaSeeA2A1F_;F_;S108R3R2R1A3SaS0SaR1S64A3Se3S6eS24SfS110Q40M1A1A1M2Se2Se2OF_;F_;Sc1R4R1A2S6fR5A1S0SdSe4R7A1ScA3SebS2dSc7R6R5RcR8R7A2A5Se2S24Se0ScaRbR2R8R1S61S6dR9A7SdbRcR3A2Sc8S3S0Sc8R1SffA3S0Sc8R1Sf9A3A2S111G1S2bR6PcA2A2S2cS109R1A1S2cS10aR11R2A2Se5S2S0Sc8R5Sf9A3S10dSe7R1A1S10eZ4S10cS10fS16S2cSe6R1A1A2A1ScbR12R9A2A2A2A2A2S24G2SfSe1A1Se0Sc9R17R16ReR14RdSfeRaScbR17ReA2S106R7A1A3R4R3R2R1AaS1S105S2dS107R18R8A2M3R5R4R2A5S70R1eR1dR18G3S28RfA1S28R5A1A6A2F_;Fmd;Ftr;Ftp';Fr;F_;Tcs;Tc;Tnv;F_;FphX;FPF;FHE;Fmd0;Frb;Se3S24G2S24RaSeaS2dS10bS61S6dR4RdR3A5R10R1R2A5SebS2dSc7R3R2R12R4RdA2A5A2FrX;Ftp';Frho';FA';S24Se0S24ScaReR3RbR2S61S6dRcA7RbSeaS2dSc9RfReR4RcR3SccA6S5S62A1R2RcA5R7A2F_;Fr';Fmd0;Frb;F_;F_;TQ;F_;FHKc;FKIT;FTR;Ftp;Frho;FKc;FA;F_;FE3P;FHPF;FPFam;FXGL;FCST;").
Proof.
  intros CST XGL PFam HPF E3P ->.
  apply (refill_populate CST XGL PFam W0 UStopLe (la_state r_2_0) cp2c ru1 (la_state r_f_0) (la_state r_f_1) cfm rf1 (la_state r_h_0)
           (la_state r_jP_0) xlP (la_state r_zP_0) (la_state r_jM_0) xlM (la_state r_zM_0) e3p head_i pieceU_i mid_i fm_i pieceF_i run_i fillP_i fillM_i).
  - intros A Kc rb tp0 md0 TR KIT HKc rho HE ph PH0 faP. exact (pop_P A Kc rb tp0 md0 TR KIT HKc rho HE ph PH0 faP).
  - intros A Kc rb tp0 md0 TR KIT HKc rho HE ph PH0 faP. exact (pop_M A Kc rb tp0 md0 TR KIT HKc rho HE ph PH0 faP).
  - intros A Kc rb tp0 md0 TR KIT HKc rho HE phX. exact (exit_P A Kc rb tp0 md0 TR KIT HKc rho HE phX).
  - intros A Kc rb tp0 md0 TR KIT HKc rho HE phX. exact (exit_M A Kc rb tp0 md0 TR KIT HKc rho HE phX).
  - intros A Kc rb tp0 md0 TR KIT rho HE phF. exact (back_P CST XGL PFam HPF A Kc rb tp0 md0 TR KIT rho HW0 HE phF).
  - intros A Kc rb tp0 md0 TR KIT rho HE phF. exact (back_M CST XGL PFam HPF A Kc rb tp0 md0 TR KIT rho HW0 HE phF).
Qed.
End SpineCallocRp0.

(* [comment removed for export] *)
Module SpineCallocRp0u.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "iff"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "la_state"; "leafA"; "sym_runA"; "entailsA"; "ax_X"; "axst"; "@Corelib.Init.Datatypes"; "cons"; "true"; "bool"; "nil"; "list"; "prod"; "Some"; "option"; "pair"; "app"; "false"; "length"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "sprop"; "ss_next"; "SLit"; "ss_facts"; "swf"; "ss_lenient"; "ss_objs"; "SAlu"; "SVar"; "reg_sv"; "SPNot"; "valuation"; "sprop_below"; "SPBranch"; "SPUle"; "rm"; "ss_pc"; "sv_below"; "rw"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSR"; "factsR"; "cX"; "GR"; "beg1"; "beg2"; "cE1"; "cE2"; "keepn"; "cP2"; "cXL"; "O_pcm"; "PV4"; "LV0"; "O_ri"; "cL1"; "cT1"; "cD"; "cPa"; "cPb"; "LV2"; "PV6"; "cE3"; "nobj"; "rMS"; "sMS"; "LV3"; "cE3b"; "vMU"; "cFm"; "vK"; "F_x"; "HINT_au"; "HINT_k"; "HINT_map"; "LNX"; "O_pccK"; "PNX"; "cE3a"; "idx_rot"; "k_e"; "relM"; "ri_has"; "rotM"; "vAU"; "vMFA"; "F_new"; "vNEW"; "vNF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c2.SpineCallocRi0u"; "e3r"; "FUEL"; "icc"; "W0"; "r_2_0"; "nob"; "e3p"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3"; "inclb"; "skel"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "eqb"; "@Corelib.Lists.ListDef"; "map"; "firstn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLe"; "KcA"; "Kc_ok"; "mem_keptA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cb.SpineCallocRp0u"; "r_xF_0"; "r_xU_0"; "cmcF"; "cmcU"; "r_9M_0"; "r_9P_0"; "cl0M"; "cl0P"; "cp2c"; "ct0M"; "ct0P"; "nobFM"; "nobFP"; "r_lM_1"; "r_lP_1"; "r_p1_0"; "r_p1_1"; "r_d_0"; "r_f_0"; "cfm"; "r_f_1"; "r_h_0"; "r_mF_0"; "r_mU_0"; "rf1"; "ru1"; "dmF"; "dmU"; "r_jM_0"; "r_jP_0"; "r_p2a_0"; "r_p2a_1"; "r_p2b_0"; "r_p2b_1"; "s_fbkM"; "s_fbkP"; "s_finM"; "s_finP"; "r_lM_0"; "r_lP_0"; "r_t1M_0"; "r_t1P_0"; "s_bkM"; "s_bkP"; "s_inM"; "s_inP"; "xlM"; "xlP"; "r_t1M_1"; "r_t1P_1"; "cellsfM"; "cellsfP"; "r_flM_0"; "r_flP_0"; "r_t0M_0"; "r_t0P_0"; "r_zM_0"; "r_zP_0"; "sa0"; "sa1"; "sb0"; "sb1"; "s_xM"; "s_xP"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_NE"; "instr"; "ALU_SLL"; "ALU_XOR"; "Ecall"; "BC_LTU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP"; "O_pcc0"; "O_st"; "V_SIZE"; "pc_base"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineCallocR2"; "BASEF"; "BASEO"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR"; "commit_post"; "memset_post"; "TRok"; "@Stdlib.Lists.List"; "forallb"; "nth_error"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CRefillJ"; "phase"; "JR"; "entryR"; "gh_new"; "ph0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bl.SpineCallocR10";
"cMr"; "a2_e"; "cMc"; "dMSf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bm.SpineCallocR13"; "F_lt"; "O_fcell"; "faend_e"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SpineCallocR3"; "O_dstc"; "O_srcc"; "e_end"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SpineCallocR7"; "F_mu0"; "F_hi"; "x19_e0"; "x19_e1"; "popfacts"; "size_e_hi"; "size_e_lo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bk.SpineCallocR9"; "O_piece"; "O_shp"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_cache_inited"; "class_state"; "cs_free_array"; "cs_mapped_free_array"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "nodupN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "instr_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "call_checkA"; "entails_frA"; "jpostA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b6.SpineCallocR11"; "a0_e"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.SpineCallocR12"; "F_geu"; "new_e"; "rup_e"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bn.SpineCallocR14"; "e16P"; "e32P"; "e48P"; "e_srcP"; "e24M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bq.SpineCallocR15"; "fillT"; "phUF3"; "pieceT"; "fmT"; "headT"; "midT"; "phFin"; "phU3"; "runT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b6.SpineCallocR4"; "O_rif"; "@Stdlib.Arith.PeanoNat.Nat"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.CRefillJP"; "PF"; "PU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel"; "kchunks"; "refillA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.SpineCallocR5"; "posts_conv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "cls_of"; "cst_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1"; "JG"; "@Stdlib.ZArith.BinInt.Z"; "add"; "lt"; "mul"; "of_nat"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocSP SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillTR CRefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ba.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bm.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aq.SpineCallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CRefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.CRefillJP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b3.SpineCallocR1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineCallocR2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SpineCallocR3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b6.SpineCallocR4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.SpineCallocR5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bm.SpineCallocR6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SpineCallocR7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bk.SpineCallocR9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bl.SpineCallocR10 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b6.SpineCallocR11 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.SpineCallocR12 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bm.SpineCallocR13 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bn.SpineCallocR14 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bq.SpineCallocR15 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c2.SpineCallocRi0u.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition R_p1__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ415c0SbS2cZ41600SeS2cA1A3A3S5S62A1ScA5").
Local Strategy expand [R_p1__R].
Definition r_p1 := Eval vm_compute in ((fun ro1__ : option (list leafA) => (match ro1__ with Some l => l | None => [] end)) R_p1__R).
Definition r_p1_0 := Eval vm_compute in (nth 0 r_p1 (mkLeafA (la_state r_2_0) RsCut)).
Definition r_p1_1 := Eval vm_compute in (nth 1 r_p1 (mkLeafA (la_state r_2_0) RsCut)).
Definition R_p2a__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ41630SeS2cA1A3S3fS2eS5eA1S5S80A1A2ScA5").
Local Strategy expand [R_p2a__R].
Definition r_p2a := Eval vm_compute in ((fun ro2__ : option (list leafA) => (match ro2__ with Some l => l | None => [] end)) R_p2a__R).
Definition r_p2a_0 := Eval vm_compute in (nth 0 r_p2a (mkLeafA (cPa (factsR e3r) (la_state r_p1_0)) RsCut)).
Definition r_p2a_1 := Eval vm_compute in (nth 1 r_p2a (mkLeafA (cPa (factsR e3r) (la_state r_p1_0)) RsCut)).
Definition R_p2b__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ41630SeS2cA1A3S40S2eS5eA1S5S81A1A2ScA5").
Local Strategy expand [R_p2b__R].
Definition r_p2b := Eval vm_compute in ((fun ro3__ : option (list leafA) => (match ro3__ with Some l => l | None => [] end)) R_p2b__R).
Definition r_p2b_0 := Eval vm_compute in (nth 0 r_p2b (mkLeafA (cPb (factsR e3r) (la_state r_p1_1)) RsCut)).
Definition r_p2b_1 := Eval vm_compute in (nth 1 r_p2b (mkLeafA (cPb (factsR e3r) (la_state r_p1_1)) RsCut)).
Definition cp2c := Eval vm_compute in (cP2c (factsR e3r) (la_state r_p2a_1)).
Lemma FP_inb : ltac2:(tb__ "0|0|
S0SdS65SbS19S26Sb7S5dS4bA3SeS19A1A3S1cS4S5S62A1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_p1 : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ415c0SbS2cZ41600SeS2cA1A3A3S5S62A1ScA5S11G0SbS6S80SbS6S81SeS6A1A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_p1__R <: R_p1__R = Some [r_p1_0; r_p1_1]). Qed.
Lemma LN_p1 : ltac2:(tb__ "0|0|
S0SdS1eS4S5S62A1A1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_p1 : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4S5S62A1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma Fa_inb : ltac2:(tb__ "0|0|
S0SdS65SbS19Sd8SeS19A1A3S1cS4S5S80A1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma Fb_inb : ltac2:(tb__ "0|0|
S0SdS65SbS19S23Sd8A1SeS19A1A3S1cS4S5S81A1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_pa : ltac2:(tb__ "0|0|
S0SdS1dS4S3fS2eS5eA1S5S80A1A2A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_pa : ltac2:(tb__ "0|5|
S0S12S10SfS10S18S18A2M0A1M1SfS19A1M2A2M3A1Sb8S4S5S80A1M4A1S4S3fS2eS5eA1G4A2A1A2S11G3S13G1G2SbG0S13S18S18SdcS21SbbA1A4SeG0A1A3SbS19S4fSbS19S27S49S1bZdffc0000A1A2SeS19A1A3A3A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_pa : ltac2:(tb__ "0|1|
S0SdS68S1aS4S3fS2eS5eA1S5S80A1M0A2A1A1S1aS4G0A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_pb : ltac2:(tb__ "0|0|
S0SdS1dS4S40S2eS5eA1S5S81A1A2A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_pb : ltac2:(tb__ "0|5|
S0S12S10SfS10S18S18A2M0A1M1SfS19A1M2A2M3A1Sb8S4S5S81A1M4A1S4S40S2eS5eA1G4A2A1A2S11G3S13G1G2SbG0S13S18S18SddS21SbbA1A4SeG0A1A3SbS19S4fSbS19S27S49S1bZdffc0000A1A2SeS19A1A3A3A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_pb : ltac2:(tb__ "0|1|
S0SdS68S1aS4S40S2eS5eA1S5S81A1M0A2A1A1S1aS4G0A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_p2a : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ41630SeS2cA1A3S3fS2eS5eA1S5S80A1A2ScA5S11G0SbS6S8fSbS6S90SeS6A1A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_p2a__R <: R_p2a__R = Some [r_p2a_0; r_p2a_1]). Qed.
Lemma LN_p2a : ltac2:(tb__ "0|0|
S0SdS1eS4S3fS2eS5eA1S5S80A1A2A1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_p2a : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4S3fS2eS5eA1S5S80A1A2A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_p2b : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ41630SeS2cA1A3S40S2eS5eA1S5S81A1A2ScA5S11G0SbS6S91SbS6S92SeS6A1A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_p2b__R <: R_p2b__R = Some [r_p2b_0; r_p2b_1]). Qed.
Lemma LN_p2b : ltac2:(tb__ "0|0|
S0SdS1eS4S40S2eS5eA1S5S81A1A2A1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_p2b : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4S40S2eS5eA1S5S81A1A2A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma Fa0_inb : ltac2:(tb__ "0|0|
S0SdS65SbS19Sd7SeS19A1A3S1cS4S5S8fA1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_a0 : ltac2:(tb__ "0|0|
S0SdS1dS4S36S2eS5eA1S5S8fA1A2A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_a0 : ltac2:(tb__ "0|5|
S0S12S10SfS10S18S18A2M0A1M1SfS19A1M2A2M3A1Sb8S4S5S8fA1M4A1S4S36S2eS5eA1G4A2A1A2S11G3S13G1G2SbG0S13S18S18Sd9S1bZ40000A1A4SbG0S13S18S18S1bZ0A1S49A4SeG0A1A3A3SeS19A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_a0 : ltac2:(tb__ "0|1|
S0SdS68S1aS4S36S2eS5eA1S5S8fA1M0A2A1A1S1aS4G0A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sa0 := Eval vm_compute in (infer_sub GR (ax_S (cP2 (factsR e3r) (la_state r_p2a_0))) (ax_S cp2c)).
Lemma ENT_a0 : ltac2:(tb__ "0|0|
S0SdS8S36S2eS5eA1S5S8fA1A2S79SabA3ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_a0 : ltac2:(tb__ "0|0|
S0SdS6cSabS30A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma Fa1_inb : ltac2:(tb__ "0|0|
S0SdS65SbS19S23Sd7A1SeS19A1A3S1cS4S5S90A1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_a1 : ltac2:(tb__ "0|0|
S0SdS1dS4S36S2eS5eA1S5S90A1A2A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_a1 : ltac2:(tb__ "0|5|
S0S12S10SfS10S18S18A2M0A1M1SfS19A1M2A2M3A1Sb8S4S5S90A1M4A1S4S36S2eS5eA1G4A2A1A2S11G3S13G1G2SbG0S13S18S18SdaS1bZ40000A1A4SeG0A1A3SeS19A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_a1 : ltac2:(tb__ "0|1|
S0SdS68S1aS4S36S2eS5eA1S5S90A1M0A2A1A1S1aS4G0A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sa1 := Eval vm_compute in (infer_sub GR (ax_S (cP2 (factsR e3r) (la_state r_p2a_1))) (ax_S cp2c)).
Lemma ENT_a1 : ltac2:(tb__ "0|0|
S0SdS8S36S2eS5eA1S5S90A1A2S79SacA3ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_a1 : ltac2:(tb__ "0|0|
S0SdS6cSacS30A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma Fb0_inb : ltac2:(tb__ "0|0|
S0SdS65SbS19Sd7SeS19A1A3S1cS4S5S91A1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_b0 : ltac2:(tb__ "0|0|
S0SdS1dS4S36S2eS5eA1S5S91A1A2A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_b0 : ltac2:(tb__ "0|5|
S0S12S10SfS10S18S18A2M0A1M1SfS19A1M2A2M3A1Sb8S4S5S91A1M4A1S4S36S2eS5eA1G4A2A1A2S11G3S13G1G2SbG0S13S18S18Sd9S1bZ40000A1A4SbG0S13S18S18S1bZ0A1S49A4SeG0A1A3A3SeS19A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_b0 : ltac2:(tb__ "0|1|
S0SdS68S1aS4S36S2eS5eA1S5S91A1M0A2A1A1S1aS4G0A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sb0 := Eval vm_compute in (infer_sub GR (ax_S (cP2 (factsR e3r) (la_state r_p2b_0))) (ax_S cp2c)).
Lemma ENT_b0 : ltac2:(tb__ "0|0|
S0SdS8S36S2eS5eA1S5S91A1A2S79SadA3ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_b0 : ltac2:(tb__ "0|0|
S0SdS6cSadS30A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma Fb1_inb : ltac2:(tb__ "0|0|
S0SdS65SbS19S23Sd7A1SeS19A1A3S1cS4S5S92A1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_b1 : ltac2:(tb__ "0|0|
S0SdS1dS4S36S2eS5eA1S5S92A1A2A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_b1 : ltac2:(tb__ "0|5|
S0S12S10SfS10S18S18A2M0A1M1SfS19A1M2A2M3A1Sb8S4S5S92A1M4A1S4S36S2eS5eA1G4A2A1A2S11G3S13G1G2SbG0S13S18S18SdaS1bZ40000A1A4SeG0A1A3SeS19A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_b1 : ltac2:(tb__ "0|1|
S0SdS68S1aS4S36S2eS5eA1S5S92A1M0A2A1A1S1aS4G0A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sb1 := Eval vm_compute in (infer_sub GR (ax_S (cP2 (factsR e3r) (la_state r_p2b_1))) (ax_S cp2c)).
Lemma ENT_b1 : ltac2:(tb__ "0|0|
S0SdS8S36S2eS5eA1S5S92A1A2S79SaeA3ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_b1 : ltac2:(tb__ "0|0|
S0SdS6cSaeS30A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma head_i : ltac2:(tb__ "0|0|
SfcS61S6dS5S62A1S79A4").
Proof.
  intros A Kc rb tp0 md0 TR KIT HKc rho r tp Q HE HC.
  exact (populate_head A Kc rb tp0 md0 TR KIT HKc W0 UStopLe rho HE FUEL e3r (la_state r_2_0) r_p1_0 r_p1_1 r_p2a_0 r_p2a_1 r_p2b_0 r_p2b_1 cp2c sa0 sa1 sb0 sb1
           (In_of_inclb _ _ FP_inb) R_p1 LN_p1 NX_p1 (In_of_inclb _ _ Fa_inb) (In_of_inclb _ _ Fb_inb) W_pa D_pa NXe_pa W_pb D_pb NXe_pb R_p2a LN_p2a NX_p2a R_p2b LN_p2b NX_p2b
           (In_of_inclb _ _ Fa0_inb) (In_of_inclb _ _ Fa1_inb) (In_of_inclb _ _ Fb0_inb) (In_of_inclb _ _ Fb1_inb) W_a0 W_a1 W_b0 W_b1 D_a0 D_a1 D_b0 D_b1 NXe_a0 NXe_a1 NXe_b0 NXe_b1
           ENT_a0 ENT_a1 ENT_b0 ENT_b1 SID_a0 SID_a1 SID_b0 SID_b1 r tp Q HC).
Qed.
Definition R_xU__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ7050cSeS2cA1A3S79ScA5").
Local Strategy expand [R_xU__R].
Definition r_xU := Eval vm_compute in ((fun ro4__ : option (list leafA) => (match ro4__ with Some l => l | None => [] end)) R_xU__R).
Definition r_xU_0 := Eval vm_compute in (nth 0 r_xU (mkLeafA cp2c RsCut)).
Definition R_mU__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZde378SeS2cA1A3SbfS2fS5S72A1S31A2S31Z40000A3ScA5").
Local Strategy expand [R_mU__R].
Definition r_mU := Eval vm_compute in ((fun ro5__ : option (list leafA) => (match ro5__ with Some l => l | None => [] end)) R_mU__R).
Definition r_mU_0 := Eval vm_compute in (nth 0 r_mU (mkLeafA (commit_post (cX (la_state r_xU_0) beg1) beg1 262144) RsCut)).
Definition cmcU := Eval vm_compute in (cMc (la_state r_mU_0) beg1).
Lemma CMCU_eq : ltac2:(tb__ "0|0|
S0SaScfS5S88A1S31A2S74A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Definition dmU := Eval vm_compute in (dMSf cmcU).
Lemma DMU_eq : ltac2:(tb__ "0|0|
S0SaSd0S74A1S8cA3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Definition ru1 := Eval vm_compute in (relM dmU).
Lemma RU1_eq : ltac2:(tb__ "0|0|
S0SaS56S8cA1S8aA3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R_xU : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ7050cSeS2cA1A3S79ScA5S11G0SbS6S72SeS6A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_xU__R <: R_xU__R = Some [r_xU_0]). Qed.
Lemma LN_xU : ltac2:(tb__ "0|0|
S0SdS1eS4S79A1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_xU : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4S79A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_xU : ltac2:(tb__ "0|0|
S0SdS1dS4S2fS5S72A1S31A2A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_xU : ltac2:(tb__ "0|5|
S0S12S10SfS10S18S18A2M0A1M1SfS19A1M2A2M3A1Sb8S4S5S72A1M4A1S4S2fG4S31A2A1A2S11G3S13G1G2SbG0S13S18S18SefS31A1S31A4SeG0A1A3SeS19A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma SK_xU : ltac2:(tb__ "0|1|
S0SfS10S10S18S18A2S18A2M0A1S69S17G0S66S1fS4S2fS5S72A1S31A2A1A1A4S69S17G0S66S14S17SbeS61A1SbS17Sb9SbS17SbaSbS17S38SbS17S3bSeS17A1A3A3A3A3A3A4A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_xUb : ltac2:(tb__ "0|0|
S0SdS65SbdS61S6dA2S1cS4S2fS5S72A1S31A2A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XX_xU : ltac2:(tb__ "0|1|
S0SfS10S18S18A2M0A1S9S2fS5S72A1S31A2A1SeG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXc_xU : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4S2fS5S72A1S31A2A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma IC_xU : ltac2:(tb__ "0|0|
S0S12Sb3A1Se9S2dS29S4S2fS5S72A1S31A2A1A1A2S11Sb3Sb6A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R17_xU : ltac2:(tb__ "0|0|
S0S18S22S4S2fS5S72A1S31A2A1Z11A2S1bZdeA1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R10_xU : ltac2:(tb__ "0|0|
S0S18S22S4S2fS5S72A1S31A2A1ZaA2S31A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R11_xU : ltac2:(tb__ "0|0|
S0S18S22S4S2fS5S72A1S31A2A1ZbA2S1bZ40000A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R12_xU : ltac2:(tb__ "0|0|
S0S18S22S4S2fS5S72A1S31A2A1ZcA2S1bZ3A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R13_xU : ltac2:(tb__ "0|0|
S0S18S22S4S2fS5S72A1S31A2A1ZdA2S1bZ32A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R14_xU : ltac2:(tb__ "0|0|
S0S18S22S4S2fS5S72A1S31A2A1ZeA2S1bZffffffffffffffffA1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R15_xU : ltac2:(tb__ "0|0|
S0S18S22S4S2fS5S72A1S31A2A1ZfA2S1bZ0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma BEL_xU : ltac2:(tb__ "0|0|
S0SdS2aS1aS4S2fS5S72A1S31A2A1A1S31A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_mU : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZde378SeS2cA1A3SbfS2fS5S72A1S31A2S31Z40000A3ScA5S11G0SbS6S88SeS6A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_mU__R <: R_mU__R = Some [r_mU_0]). Qed.
Lemma LN_mU : ltac2:(tb__ "0|0|
S0SdS1eS4SbfS2fS5S72A1S31A2S31Z40000A3A1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_mU : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4SbfS2fS5S72A1S31A2S31Z40000A3A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SK_mU : ltac2:(tb__ "0|1|
S0SfS10S10S18S18A2S18A2M0A1S69S17G0S66S1fS4S5S88A1A1A1A4S69S17G0S66S14S17SbeS61A1SbS17Sb9SbS17SbaSbS17S38SbS17S3bSbS17SdeS31A1SeS17A1A3A3A3A3A3A3A4A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_mUb : ltac2:(tb__ "0|0|
S0SdS65SbdS61S6dA2S1cS4S5S88A1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XX_mU : ltac2:(tb__ "0|1|
S0SfS10S18S18A2M0A1S9S5S88A1A1SeG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma W_mrU : ltac2:(tb__ "0|0|
S0SdS1dS4ScdS5S88A1A1A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_mrU : ltac2:(tb__ "0|5|
S0S12S10SfS10S18S18A2M0A1M1SfS19A1M2A2M3A1Sb8S4S5S88A1M4A1S4ScdG4A1A1A2S11G3S13G1G2SbG0S13S18S18SceS31A1S1bZ8000A1A4SeG0A1A3SeS19A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma W_mcU : ltac2:(tb__ "0|0|
S0SdS1dS4S74A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma E_msU : ltac2:(tb__ "0|1|
S0S12SfS17A1M0A1SedS74Sc5S46S74A1A3S11G0S45S74A1A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma CHK_msU : ltac2:(tb__ "0|0|
S0SdSecS74Sc5S46S74A1S45S74A1S69S6SaS5Sc6A4A5ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NF_msU : ltac2:(tb__ "0|0|
S0SdS67Sc7S1aS4S74A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NX_msU : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4S74A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBC_msU : ltac2:(tb__ "0|1|
S0SdSc2S19S25S1aS4S74A1M0A1A1S1cG0A1A3ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT_msU : ltac2:(tb__ "0|0|
S0SdSc2S19S25S1aS4Sc0S74S46S74A1S45S74A1A3A1A1A1S1cS4S74A1A1A3ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ND_rU : ltac2:(tb__ "0|0|
S0SdSe8S54S8cA1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NO_rUb : ltac2:(tb__ "0|0|
S0SdS102U1S44S8cA1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma OB_rU : ltac2:(tb__ "0|1|
S0SfS17A1S1fS4S58S8cA1A1A1M0S14S17S6aS17Sc4S44S8cA1U2A2G0A3SbS17SdeS31A1SbS17SdfS31A1SeS17A1A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma pieceU_i : ltac2:(tb__ "0|0|
SfaS61S6dS104S31S79S8aA6").
Proof.
  rewrite <- RU1_eq, <- DMU_eq, <- CMCU_eq.
  intros A Kc rb tp0 md0 TR KIT HKc rho HE ph PH0 PORD PQ HBv HBn HRc HRr r tp Q HC.
  refine (piece_full A Kc rb tp0 md0 TR KIT HKc W0 UStopLe rho HW0 HE PU beg1 ph PH0 PORD PQ HBv HBn HRc HRr FUEL cp2c r_xU_0 r_mU_0
           R_xU LN_xU NX_xU W_xU D_xU SK_xU (inclb_incl _ _ XF_xUb) XX_xU NXc_xU IC_xU R17_xU R10_xU BEL_xU R11_xU R12_xU R13_xU R14_xU R15_xU
           R_mU LN_mU NX_mU SK_mU (inclb_incl _ _ XF_mUb) XX_mU W_mrU D_mrU _ _ _ _ _ _ _ _ _ _ r tp Q HC);
    rewrite ?CMCU_eq, ?DMU_eq; [exact W_mcU | exact E_msU | exact CHK_msU | exact NF_msU | exact NX_msU | exact FBC_msU | exact FBT_msU | exact ND_rU | apply Nat.leb_le; exact NO_rUb | exact OB_rU].
Qed.
Definition R_d__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ416f0SeS2cA1A3S8aScA5").
Local Strategy expand [R_d__R].
Definition r_d := Eval vm_compute in ((fun ro6__ : option (list leafA) => (match ro6__ with Some l => l | None => [] end)) R_d__R).
Definition r_d_0 := Eval vm_compute in (nth 0 r_d (mkLeafA ru1 RsCut)).
Definition R_f__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ3f270SbS2cZ4172cSeS2cA1A3A3S3eS2eS5eA1S5S82A1A2ScA5").
Local Strategy expand [R_f__R].
Definition r_f := Eval vm_compute in ((fun ro7__ : option (list leafA) => (match ro7__ with Some l => l | None => [] end)) R_f__R).
Definition r_f_0 := Eval vm_compute in (nth 0 r_f (mkLeafA (cD (factsR e3r) (la_state r_d_0)) RsCut)).
Definition r_f_1 := Eval vm_compute in (nth 1 r_f (mkLeafA (cD (factsR e3r) (la_state r_d_0)) RsCut)).
Lemma R_d : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ416f0SeS2cA1A3S8aScA5S11G0SbS6S82SeS6A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_d__R <: R_d__R = Some [r_d_0]). Qed.
Lemma LN_d : ltac2:(tb__ "0|0|
S0SdS1eS4S8aA1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_d : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4S8aA1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_d : ltac2:(tb__ "0|0|
S0SdS1dS4S3eS2eS5eA1S5S82A1A2A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_d : ltac2:(tb__ "0|5|
S0S12S10SfS10S18S18A2M0A1M1SfS19A1M2A2M3A1Sb8S4S5S82A1M4A1S4S3eS2eS5eA1G4A2A1A2S11G3S13G1G2SbG0S13S18S18Sf1S5cA4SeG0A1A3S5bA4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_d : ltac2:(tb__ "0|1|
S0SdS68S1aS4S3eS2eS5eA1S5S82A1M0A2A1A1S1aS4G0A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_f : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ3f270SbS2cZ4172cSeS2cA1A3A3S3eS2eS5eA1S5S82A1A2ScA5S11G0SbS6S83SbS6S85SeS6A1A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_f__R <: R_f__R = Some [r_f_0; r_f_1]). Qed.
Lemma LN_f : ltac2:(tb__ "0|0|
S0SdS1eS4S3eS2eS5eA1S5S82A1A2A1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_f : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4S3eS2eS5eA1S5S82A1A2A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma F0_inb : ltac2:(tb__ "0|0|
S0SdS65SbS19Sf0SeS19A1A3S1cS4S5S83A1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma Fm_inb : ltac2:(tb__ "0|0|
S0SdS65SbS19S23Sf0A1SeS19A1A3S1cS4S5S85A1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma mid_i : ltac2:(tb__ "0|0|
SfdS61S6dS8aS5S83A1S5S85A1A5").
Proof.
  intros A Kc rb tp0 md0 TR KIT HKc rho HE PF ph r tp Q. cbn zeta.
  exact (populate_mid A Kc rb tp0 md0 TR KIT HKc W0 UStopLe rho HE PF ph FUEL e3r ru1 r_d_0 r_f_0 r_f_1 R_d LN_d NX_d W_d D_d NXe_d R_f LN_f NX_f (In_of_inclb _ _ F0_inb) (In_of_inclb _ _ Fm_inb) r tp Q).
Qed.
Definition cfm := Eval vm_compute in (cFm (la_state r_f_1)).
Lemma CFM_eq : ltac2:(tb__ "0|0|
S0SaS4aS5S85A1A1S84A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma W_fm : ltac2:(tb__ "0|0|
S0SdS1dS4S4aS5S85A1A1A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_fm : ltac2:(tb__ "0|5|
S0S12S10SfS10S18S18A2M0A1M1SfS19A1M2A2M3A1Sb8S4S5S85A1M4A1S4S4aG4A1A1A2S11G3S13G1G2SbG0S13S18S18Sf2S20Sb1S5aS1bZ40000A1A3A4SeG0A1A3SeS19A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma fm_i : ltac2:(tb__ "0|0|
SfbS61S6dS5S85A1S84A4").
Proof.
  rewrite <- CFM_eq. intros A Kc rb tp0 md0 TR KIT HKc rho HE PF ph r tp Q. cbn zeta.
  exact (famap_restate A Kc rb tp0 md0 TR KIT W0 UStopLe rho HE PF (la_state r_f_1) W_fm D_fm ph r tp Q).
Qed.
Definition R_xF__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ7050cSeS2cA1A3S84ScA5").
Local Strategy expand [R_xF__R].
Definition r_xF := Eval vm_compute in ((fun ro8__ : option (list leafA) => (match ro8__ with Some l => l | None => [] end)) R_xF__R).
Definition r_xF_0 := Eval vm_compute in (nth 0 r_xF (mkLeafA cfm RsCut)).
Definition R_mF__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZde378SeS2cA1A3SbfS2fS5S71A1S32A2S32Z40000A3ScA5").
Local Strategy expand [R_mF__R].
Definition r_mF := Eval vm_compute in ((fun ro9__ : option (list leafA) => (match ro9__ with Some l => l | None => [] end)) R_mF__R).
Definition r_mF_0 := Eval vm_compute in (nth 0 r_mF (mkLeafA (commit_post (cX (la_state r_xF_0) beg2) beg2 262144) RsCut)).
Definition cmcF := Eval vm_compute in (cMc (la_state r_mF_0) beg2).
Lemma CMCF_eq : ltac2:(tb__ "0|0|
S0SaScfS5S87A1S32A2S73A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Definition dmF := Eval vm_compute in (dMSf cmcF).
Lemma DMF_eq : ltac2:(tb__ "0|0|
S0SaSd0S73A1S8bA3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Definition rf1 := Eval vm_compute in (relM dmF).
Lemma RF1_eq : ltac2:(tb__ "0|0|
S0SaS56S8bA1S89A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R_xF : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ7050cSeS2cA1A3S84ScA5S11G0SbS6S71SeS6A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_xF__R <: R_xF__R = Some [r_xF_0]). Qed.
Lemma LN_xF : ltac2:(tb__ "0|0|
S0SdS1eS4S84A1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_xF : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4S84A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_xF : ltac2:(tb__ "0|0|
S0SdS1dS4S2fS5S71A1S32A2A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_xF : ltac2:(tb__ "0|5|
S0S12S10SfS10S18S18A2M0A1M1SfS19A1M2A2M3A1Sb8S4S5S71A1M4A1S4S2fG4S32A2A1A2S11G3S13G1G2SbG0S13S18S18SefS32A1S32A4SeG0A1A3SeS19A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma SK_xF : ltac2:(tb__ "0|1|
S0SfS10S10S18S18A2S18A2M0A1S69S17G0S66S1fS4S2fS5S71A1S32A2A1A1A4S69S17G0S66S14S17SbeS61A1SbS17Sb9SbS17SbaSbS17S38SbS17S3bSeS17A1A3A3A3A3A3A4A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_xFb : ltac2:(tb__ "0|0|
S0SdS65SbdS61S6dA2S1cS4S2fS5S71A1S32A2A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XX_xF : ltac2:(tb__ "0|1|
S0SfS10S18S18A2M0A1S9S2fS5S71A1S32A2A1SeG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXc_xF : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4S2fS5S71A1S32A2A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma IC_xF : ltac2:(tb__ "0|0|
S0S12Sb3A1Se9S2dS29S4S2fS5S71A1S32A2A1A1A2S11Sb3Sb6A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R17_xF : ltac2:(tb__ "0|0|
S0S18S22S4S2fS5S71A1S32A2A1Z11A2S1bZdeA1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R10_xF : ltac2:(tb__ "0|0|
S0S18S22S4S2fS5S71A1S32A2A1ZaA2S32A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R11_xF : ltac2:(tb__ "0|0|
S0S18S22S4S2fS5S71A1S32A2A1ZbA2S1bZ40000A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R12_xF : ltac2:(tb__ "0|0|
S0S18S22S4S2fS5S71A1S32A2A1ZcA2S1bZ3A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R13_xF : ltac2:(tb__ "0|0|
S0S18S22S4S2fS5S71A1S32A2A1ZdA2S1bZ32A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R14_xF : ltac2:(tb__ "0|0|
S0S18S22S4S2fS5S71A1S32A2A1ZeA2S1bZffffffffffffffffA1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R15_xF : ltac2:(tb__ "0|0|
S0S18S22S4S2fS5S71A1S32A2A1ZfA2S1bZ0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma BEL_xF : ltac2:(tb__ "0|0|
S0SdS2aS1aS4S2fS5S71A1S32A2A1A1S32A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_mF : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZde378SeS2cA1A3SbfS2fS5S71A1S32A2S32Z40000A3ScA5S11G0SbS6S87SeS6A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_mF__R <: R_mF__R = Some [r_mF_0]). Qed.
Lemma LN_mF : ltac2:(tb__ "0|0|
S0SdS1eS4SbfS2fS5S71A1S32A2S32Z40000A3A1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_mF : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4SbfS2fS5S71A1S32A2S32Z40000A3A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SK_mF : ltac2:(tb__ "0|1|
S0SfS10S10S18S18A2S18A2M0A1S69S17G0S66S1fS4S5S87A1A1A1A4S69S17G0S66S14S17SbeS61A1SbS17Sb9SbS17SbaSbS17S38SbS17S3bSbS17SdeS32A1SeS17A1A3A3A3A3A3A3A4A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_mFb : ltac2:(tb__ "0|0|
S0SdS65SbdS61S6dA2S1cS4S5S87A1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XX_mF : ltac2:(tb__ "0|1|
S0SfS10S18S18A2M0A1S9S5S87A1A1SeG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma W_mrF : ltac2:(tb__ "0|0|
S0SdS1dS4ScdS5S87A1A1A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_mrF : ltac2:(tb__ "0|5|
S0S12S10SfS10S18S18A2M0A1M1SfS19A1M2A2M3A1Sb8S4S5S87A1M4A1S4ScdG4A1A1A2S11G3S13G1G2SbG0S13S18S18SceS32A1S1bZ8000A1A4SeG0A1A3SeS19A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma W_mcF : ltac2:(tb__ "0|0|
S0SdS1dS4S73A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma E_msF : ltac2:(tb__ "0|1|
S0S12SfS17A1M0A1SedS73Sc5S46S73A1A3S11G0S45S73A1A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma CHK_msF : ltac2:(tb__ "0|0|
S0SdSecS73Sc5S46S73A1S45S73A1S69S6SaS5Sc6A4A5ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NF_msF : ltac2:(tb__ "0|0|
S0SdS67Sc7S1aS4S73A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NX_msF : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4S73A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBC_msF : ltac2:(tb__ "0|1|
S0SdSc2S19S25S1aS4S73A1M0A1A1S1cG0A1A3ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT_msF : ltac2:(tb__ "0|0|
S0SdSc2S19S25S1aS4Sc0S73S46S73A1S45S73A1A3A1A1A1S1cS4S73A1A1A3ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ND_rF : ltac2:(tb__ "0|0|
S0SdSe8S54S8bA1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NO_rFb : ltac2:(tb__ "0|0|
S0SdS102U1S44S8bA1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma OB_rF : ltac2:(tb__ "0|1|
S0SfS17A1S1fS4S58S8bA1A1A1M0S14S17S6aS17Sc4S44S8bA1U2A2G0A3SbS17SdeS32A1SbS17SdfS32A1SeS17A1A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma pieceF_i : ltac2:(tb__ "0|0|
SfaS61S6dS103S32S84S89A6").
Proof.
  rewrite <- RF1_eq, <- DMF_eq, <- CMCF_eq.
  intros A Kc rb tp0 md0 TR KIT HKc rho HE ph PH0 PORD PQ HBv HBn HRc HRr r tp Q HC.
  refine (piece_full A Kc rb tp0 md0 TR KIT HKc W0 UStopLe rho HW0 HE OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.CRefillJP.PF beg2 ph PH0 PORD PQ HBv HBn HRc HRr FUEL cfm r_xF_0 r_mF_0
           R_xF LN_xF NX_xF W_xF D_xF SK_xF (inclb_incl _ _ XF_xFb) XX_xF NXc_xF IC_xF R17_xF R10_xF BEL_xF R11_xF R12_xF R13_xF R14_xF R15_xF
           R_mF LN_mF NX_mF SK_mF (inclb_incl _ _ XF_mFb) XX_mF W_mrF D_mrF _ _ _ _ _ _ _ _ _ _ r tp Q HC);
    rewrite ?CMCF_eq, ?DMF_eq; [exact W_mcF | exact E_msF | exact CHK_msF | exact NF_msF | exact NX_msF | exact FBC_msF | exact FBT_msF | exact ND_rF | apply Nat.leb_le; exact NO_rFb | exact OB_rF].
Qed.
Definition R_h__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ4172cSeS2cA1A3S89ScA5").
Local Strategy expand [R_h__R].
Definition r_h := Eval vm_compute in ((fun ro10__ : option (list leafA) => (match ro10__ with Some l => l | None => [] end)) R_h__R).
Definition r_h_0 := Eval vm_compute in (nth 0 r_h (mkLeafA rf1 RsCut)).
Lemma R_h : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ4172cSeS2cA1A3S89ScA5S11G0SbS6S86SeS6A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_h__R <: R_h__R = Some [r_h_0]). Qed.
Lemma LN_h : ltac2:(tb__ "0|0|
S0SdS1eS4S89A1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_h : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4S89A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma run_i : ltac2:(tb__ "0|0|
S100S89S5S86A1A2").
Proof.
  intros A Kc rb tp0 md0 TR KIT HKc ph r tp Q HC.
  apply (jr_run A Kc rb tp0 md0 TR KIT HKc FUEL [0x4172c] rf1 [r_h_0] ph r tp Q R_h LN_h NX_h).
  intros L r1 [<-|[]] _. exact (HC r1).
Qed.
Definition R_fhP__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ41740SeS2cA1A3S5S83A1ScA5").
Local Strategy expand [R_fhP__R].
Definition r_flP := Eval vm_compute in ((fun ro12__ : option (list leafA) => (match ro12__ with Some l => l | None => [] end)) R_fhP__R).
Definition r_flP_0 := Eval vm_compute in (nth 0 r_flP (mkLeafA (la_state r_f_0) RsCut)).
Definition cl0P := Eval vm_compute in (cL0 (factsR e3r) (la_state r_flP_0)).
Definition R_l1P__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ41740SbS2cZ4174cSeS2cA1A3A3S3cS78A1ScA5").
Local Strategy expand [R_l1P__R].
Definition r_lP := Eval vm_compute in ((fun ro11__ : option (list leafA) => (match ro11__ with Some l => l | None => [] end)) R_l1P__R).
Definition r_lP_0 := Eval vm_compute in (nth 0 r_lP (mkLeafA (cL1 cl0P) RsCut)).
Definition r_lP_1 := Eval vm_compute in (nth 1 r_lP (mkLeafA (cL1 cl0P) RsCut)).
Definition nobFP := Eval vm_compute in (length (ss_objs (ax_S cl0P))).
Definition s_fbkP := Eval vm_compute in (infer_sub GR (ax_S (keepn (la_state r_lP_0) nobFP)) (ax_S cl0P)).
Definition s_finP := Eval vm_compute in (infer_sub GR (ax_S (la_state r_flP_0)) (ax_S cl0P)).
Definition R_fjP__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ413ccSeS2cA1A3S37S2eS5eA1S35S5S7fA1S7dA2A2ScA5").
Local Strategy expand [R_fjP__R].
Definition r_jP := Eval vm_compute in ((fun ro13__ : option (list leafA) => (match ro13__ with Some l => l | None => [] end)) R_fjP__R).
Definition r_jP_0 := Eval vm_compute in (nth 0 r_jP (mkLeafA (cXL (factsR e3r) (keepn (la_state r_lP_1) nobFP)) RsCut)).
Lemma SK_lP : ltac2:(tb__ "0|1|
S0SfS10S10S18S18A2S18A2M0A1S69S17G0S66S1fS4S78A1A1A4S69S17G0S66S14S17SbeS61A1SbS17Sb9SbS17SbaSbS17S38SbS17S3bSeS17A1A3A3A3A3A3A4A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XX_lP : ltac2:(tb__ "0|1|
S0SfS10S18S18A2M0A1S9S78A1SeG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_lPb : ltac2:(tb__ "0|0|
S0SdS65SbdS61S6dA2S1cS4S78A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NX_lP : ltac2:(tb__ "0|0|
S0SdS68S1aS4S78A1A1S50A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_l1P : ltac2:(tb__ "0|0|
S0SdS1dS4S3cS78A1A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_l1P : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ41740SbS2cZ4174cSeS2cA1A3A3S3cS78A1ScA5S11G0SbS6S98SbS6S7fSeS6A1A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_l1P__R <: R_l1P__R = Some [r_lP_0; r_lP_1]). Qed.
Lemma LN_l1P : ltac2:(tb__ "0|0|
S0SdS1eS4S3cS78A1A1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma OB_fbP : ltac2:(tb__ "0|1|
S0SfS17A1S1fS4S5S98A1A1A1M0S14S17S6aS17S7dG0A3SbS17Sd2SeS17A1A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_fxP : ltac2:(tb__ "0|1|
S0SfS17A1S1fS4S5S7fA1A1A1M0S14S17S6aS17S7dG0A3SbS17Sd2SeS17A1A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma ENT_fbkP : ltac2:(tb__ "0|0|
S0SdS8S35S5S98A1S7dA2S78S94A3ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_fbkP : ltac2:(tb__ "0|0|
S0SdS6cS94S30A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma S_bk0P : ltac2:(tb__ "0|0|
S0S18S6bS94S3aA2S20Sb1S21S3aA1S1bZ1A1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S_bk2P : ltac2:(tb__ "0|0|
S0S18S6bS94S41A2S20Sb1S21S41A1S21SbbA1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S_bk3P : ltac2:(tb__ "0|0|
S0S18S6bS94S47A2S20Sb1Sd3S20Sb4S20Sb5S21S3aA1S1bZffffffffffffffffA1A3S1bZ2A1A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma FB_fbPb : ltac2:(tb__ "0|0|
S0SdS65SbS19Sd1SeS19A1A3S1cS4S5S98A1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FB_fxPb : ltac2:(tb__ "0|0|
S0SdS65SbS19S23Sd1A1SeS19A1A3S1cS4S5S7fA1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_fhP : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ41740SeS2cA1A3S5S83A1ScA5S11G0SbS6Sa6SeS6A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_fhP__R <: R_fhP__R = Some [r_flP_0]). Qed.
Lemma LN_fhP : ltac2:(tb__ "0|0|
S0SdS1eS4S5S83A1A1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_fhP : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4S5S83A1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_finP : ltac2:(tb__ "0|0|
S0SdS8S5Sa6A1S78S96A3ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_finP : ltac2:(tb__ "0|0|
S0SdS6cS96S30A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma S_in0P : ltac2:(tb__ "0|0|
S0S18S6bS96S3aA2S1bZ1A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S_in2P : ltac2:(tb__ "0|0|
S0S18S6bS96S41A2S59A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S_in3P : ltac2:(tb__ "0|0|
S0S18S6bS96S47A2S20Sb1Sd3S1bN4A1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma W_xlP : ltac2:(tb__ "0|0|
S0SdS1dS4S37S2eS5eA1S35S5S7fA1S7dA2A2A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_xlP : ltac2:(tb__ "0|5|
S0S12S10SfS10S18S18A2M0A1M1SfS19A1M2A2M3A1Sb8S4S35S5S7fA1S7dA2M4A1S4S37S2eS5eA1G4A2A1A2S11G3S13G1G2SeG0A1SbS19S4dSbS19S4eSeS19A1A3A3A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_xlP : ltac2:(tb__ "0|1|
S0SdS68S1aS4S37S2eS5eA1S35S5S7fA1S7dA2M0A2A1A1S1aS4G0A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_fjP : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ413ccSeS2cA1A3S37S2eS5eA1S35S5S7fA1S7dA2A2ScA5S11G0SbS6S8eSeS6A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_fjP__R <: R_fjP__R = Some [r_jP_0]). Qed.
Lemma LN_fxlP : ltac2:(tb__ "0|0|
S0SdS1eS4S37S2eS5eA1S35S5S7fA1S7dA2A2A1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_fxlP : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4S37S2eS5eA1S35S5S7fA1S7dA2A2A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma fillP_i : ltac2:(tb__ "0|0|
Sf8S61S6dS5S83A1S5S8eA1A4").
Proof.
  intros A Kc rb tp0 md0 TR KIT HKc rho HE PF ph PQ HDEF r tp Q HC.
  exact (fill_all A Kc rb tp0 md0 TR KIT HKc W0 UStopLe rho HW0 HE PF ph PQ HDEF FUEL cl0P r_lP_0 r_lP_1 nobFP s_fbkP SK_lP XX_lP (inclb_incl _ _ XF_lPb) NX_lP W_l1P R_l1P LN_l1P
           OB_fbP OB_fxP ENT_fbkP SID_fbkP S_bk0P S_bk2P S_bk3P (In_of_inclb _ _ FB_fbPb) (In_of_inclb _ _ FB_fxPb) e3r (la_state r_f_0) r_flP_0 r_jP_0 s_finP
           R_fhP LN_fhP NX_fhP ENT_finP SID_finP S_in0P S_in2P S_in3P W_xlP D_xlP NXe_xlP R_fjP LN_fxlP NX_fxlP r tp Q HC).
Qed.
Definition R_fhM__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ41740SeS2cA1A3S5S86A1ScA5").
Local Strategy expand [R_fhM__R].
Definition r_flM := Eval vm_compute in ((fun ro15__ : option (list leafA) => (match ro15__ with Some l => l | None => [] end)) R_fhM__R).
Definition r_flM_0 := Eval vm_compute in (nth 0 r_flM (mkLeafA (la_state r_h_0) RsCut)).
Definition cl0M := Eval vm_compute in (cL0 (factsR e3r) (la_state r_flM_0)).
Definition R_l1M__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ41740SbS2cZ4174cSeS2cA1A3A3S3cS77A1ScA5").
Local Strategy expand [R_l1M__R].
Definition r_lM := Eval vm_compute in ((fun ro14__ : option (list leafA) => (match ro14__ with Some l => l | None => [] end)) R_l1M__R).
Definition r_lM_0 := Eval vm_compute in (nth 0 r_lM (mkLeafA (cL1 cl0M) RsCut)).
Definition r_lM_1 := Eval vm_compute in (nth 1 r_lM (mkLeafA (cL1 cl0M) RsCut)).
Definition nobFM := Eval vm_compute in (length (ss_objs (ax_S cl0M))).
Definition s_fbkM := Eval vm_compute in (infer_sub GR (ax_S (keepn (la_state r_lM_0) nobFM)) (ax_S cl0M)).
Definition s_finM := Eval vm_compute in (infer_sub GR (ax_S (la_state r_flM_0)) (ax_S cl0M)).
Definition R_fjM__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ413ccSeS2cA1A3S37S2eS5eA1S35S5S7eA1S7cA2A2ScA5").
Local Strategy expand [R_fjM__R].
Definition r_jM := Eval vm_compute in ((fun ro16__ : option (list leafA) => (match ro16__ with Some l => l | None => [] end)) R_fjM__R).
Definition r_jM_0 := Eval vm_compute in (nth 0 r_jM (mkLeafA (cXL (factsR e3r) (keepn (la_state r_lM_1) nobFM)) RsCut)).
Lemma SK_lM : ltac2:(tb__ "0|1|
S0SfS10S10S18S18A2S18A2M0A1S69S17G0S66S1fS4S77A1A1A4S69S17G0S66S14S17SbeS61A1SbS17Sb9SbS17SbaSbS17S38SbS17S3bSeS17A1A3A3A3A3A3A4A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XX_lM : ltac2:(tb__ "0|1|
S0SfS10S18S18A2M0A1S9S77A1SeG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_lMb : ltac2:(tb__ "0|0|
S0SdS65SbdS61S6dA2S1cS4S77A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NX_lM : ltac2:(tb__ "0|0|
S0SdS68S1aS4S77A1A1S50A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_l1M : ltac2:(tb__ "0|0|
S0SdS1dS4S3cS77A1A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_l1M : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ41740SbS2cZ4174cSeS2cA1A3A3S3cS77A1ScA5S11G0SbS6S97SbS6S7eSeS6A1A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_l1M__R <: R_l1M__R = Some [r_lM_0; r_lM_1]). Qed.
Lemma LN_l1M : ltac2:(tb__ "0|0|
S0SdS1eS4S3cS77A1A1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma OB_fbM : ltac2:(tb__ "0|1|
S0SfS17A1S1fS4S5S97A1A1A1M0S14S17S6aS17S7cG0A3SbS17Sd2SeS17A1A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_fxM : ltac2:(tb__ "0|1|
S0SfS17A1S1fS4S5S7eA1A1A1M0S14S17S6aS17S7cG0A3SbS17Sd2SeS17A1A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma ENT_fbkM : ltac2:(tb__ "0|0|
S0SdS8S35S5S97A1S7cA2S77S93A3ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_fbkM : ltac2:(tb__ "0|0|
S0SdS6cS93S30A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma S_bk0M : ltac2:(tb__ "0|0|
S0S18S6bS93S3aA2S20Sb1S21S3aA1S1bZ1A1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S_bk2M : ltac2:(tb__ "0|0|
S0S18S6bS93S41A2S20Sb1S21S41A1S21SbbA1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S_bk3M : ltac2:(tb__ "0|0|
S0S18S6bS93S47A2S20Sb1Sd3S20Sb4S20Sb5S21S3aA1S1bZffffffffffffffffA1A3S1bZ2A1A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma FB_fbMb : ltac2:(tb__ "0|0|
S0SdS65SbS19Sd1SeS19A1A3S1cS4S5S97A1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FB_fxMb : ltac2:(tb__ "0|0|
S0SdS65SbS19S23Sd1A1SeS19A1A3S1cS4S5S7eA1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_fhM : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ41740SeS2cA1A3S5S86A1ScA5S11G0SbS6Sa5SeS6A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_fhM__R <: R_fhM__R = Some [r_flM_0]). Qed.
Lemma LN_fhM : ltac2:(tb__ "0|0|
S0SdS1eS4S5S86A1A1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_fhM : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4S5S86A1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_finM : ltac2:(tb__ "0|0|
S0SdS8S5Sa5A1S77S95A3ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_finM : ltac2:(tb__ "0|0|
S0SdS6cS95S30A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma S_in0M : ltac2:(tb__ "0|0|
S0S18S6bS95S3aA2S1bZ1A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S_in2M : ltac2:(tb__ "0|0|
S0S18S6bS95S41A2S59A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S_in3M : ltac2:(tb__ "0|0|
S0S18S6bS95S47A2S20Sb1Sd3S1bN4A1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma W_xlM : ltac2:(tb__ "0|0|
S0SdS1dS4S37S2eS5eA1S35S5S7eA1S7cA2A2A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_xlM : ltac2:(tb__ "0|5|
S0S12S10SfS10S18S18A2M0A1M1SfS19A1M2A2M3A1Sb8S4S35S5S7eA1S7cA2M4A1S4S37S2eS5eA1G4A2A1A2S11G3S13G1G2SeG0A1SbS19S4dSbS19S4eSeS19A1A3A3A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_xlM : ltac2:(tb__ "0|1|
S0SdS68S1aS4S37S2eS5eA1S35S5S7eA1S7cA2M0A2A1A1S1aS4G0A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_fjM : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ413ccSeS2cA1A3S37S2eS5eA1S35S5S7eA1S7cA2A2ScA5S11G0SbS6S8dSeS6A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_fjM__R <: R_fjM__R = Some [r_jM_0]). Qed.
Lemma LN_fxlM : ltac2:(tb__ "0|0|
S0SdS1eS4S37S2eS5eA1S35S5S7eA1S7cA2A2A1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_fxlM : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4S37S2eS5eA1S35S5S7eA1S7cA2A2A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma fillM_i : ltac2:(tb__ "0|0|
Sf8S61S6dS5S86A1S5S8dA1A4").
Proof.
  intros A Kc rb tp0 md0 TR KIT HKc rho HE PF ph PQ HDEF r tp Q HC.
  exact (fill_all A Kc rb tp0 md0 TR KIT HKc W0 UStopLe rho HW0 HE PF ph PQ HDEF FUEL cl0M r_lM_0 r_lM_1 nobFM s_fbkM SK_lM XX_lM (inclb_incl _ _ XF_lMb) NX_lM W_l1M R_l1M LN_l1M
           OB_fbM OB_fxM ENT_fbkM SID_fbkM S_bk0M S_bk2M S_bk3M (In_of_inclb _ _ FB_fbMb) (In_of_inclb _ _ FB_fxMb) e3r (la_state r_h_0) r_flM_0 r_jM_0 s_finM
           R_fhM LN_fhM NX_fhM ENT_finM SID_finM S_in0M S_in2M S_in3M W_xlM D_xlM NXe_xlM R_fjM LN_fxlM NX_fxlM r tp Q HC).
Qed.
Definition R_t0P__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ413dcSbS2cZ413f0SeS2cA1A3A3S5S8eA1ScA5").
Local Strategy expand [R_t0P__R].
Definition r_t0P := Eval vm_compute in ((fun ro18__ : option (list leafA) => (match ro18__ with Some l => l | None => [] end)) R_t0P__R).
Definition r_t0P_0 := Eval vm_compute in (nth 0 r_t0P (mkLeafA (la_state r_jP_0) RsCut)).
Definition ct0P := Eval vm_compute in (cT0 (la_state r_t0P_0)).
Definition R_t1P__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ413dcSbS2cZ413f0SeS2cA1A3A3S3dS7bA1ScA5").
Local Strategy expand [R_t1P__R].
Definition r_t1P := Eval vm_compute in ((fun ro17__ : option (list leafA) => (match ro17__ with Some l => l | None => [] end)) R_t1P__R).
Definition r_t1P_0 := Eval vm_compute in (nth 0 r_t1P (mkLeafA (cT1 ct0P) RsCut)).
Definition r_t1P_1 := Eval vm_compute in (nth 1 r_t1P (mkLeafA (cT1 ct0P) RsCut)).
Definition s_inP := Eval vm_compute in (infer_sub GR (ax_S (la_state r_t0P_0)) (ax_S ct0P)).
Definition s_bkP := Eval vm_compute in (infer_sub GR (ax_S (keepn (la_state r_t1P_0) nob)) (ax_S ct0P)).
Lemma SK_tP : ltac2:(tb__ "0|1|
S0SfS10S10S18S18A2S18A2M0A1S69S17G0S66S1fS4S7bA1A1A4S69S17G0S66S14S17SbeS61A1SbS17Sb9SbS17SbaSbS17S38SbS17S3bSeS17A1A3A3A3A3A3A4A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XX_tP : ltac2:(tb__ "0|1|
S0SfS10S18S18A2M0A1S9S7bA1SeG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_tPb : ltac2:(tb__ "0|0|
S0SdS65SbdS61S6dA2S1cS4S7bA1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NX_tP : ltac2:(tb__ "0|0|
S0SdS68S1aS4S7bA1A1S52A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_t1P : ltac2:(tb__ "0|0|
S0SdS1dS4S3dS7bA1A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_t1P : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ413dcSbS2cZ413f0SeS2cA1A3A3S3dS7bA1ScA5S11G0SbS6S9aSbS6Sa2SeS6A1A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_t1P__R <: R_t1P__R = Some [r_t1P_0; r_t1P_1]). Qed.
Lemma LN_t1P : ltac2:(tb__ "0|0|
S0SdS1eS4S3dS7bA1A1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma OB_bP : ltac2:(tb__ "0|1|
S0SfS17A1S1fS4S5S9aA1A1A1M0S14S17S6aS17S63G0A3SbS17Sd5SbS17Sd4SeS17A1A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_xP : ltac2:(tb__ "0|1|
S0SfS17A1S1fS4S5Sa2A1A1A1M0S14S17S6aS17S63G0A3SbS17Sd5SbS17Sd4SeS17A1A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma ENT_bkP : ltac2:(tb__ "0|0|
S0SdS8S35S5S9aA1S63A2S7bS9cA3ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_bkP : ltac2:(tb__ "0|0|
S0SdS6cS9cS30A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma S_bk4P : ltac2:(tb__ "0|0|
S0S18S6bS9cS39A2S20Sb1S21S39A1S1bZ4A1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S_bk6P : ltac2:(tb__ "0|0|
S0S18S6bS9cS42A2S20Sb1S21S42A1S1bZ4A1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma FB_bPb : ltac2:(tb__ "0|0|
S0SdS65SbS19S26Sb2S20Sb1S21S39A1S1bZ4A1A3Sd6A3SeS19A1A3S1cS4S5S9aA1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FB_xPb : ltac2:(tb__ "0|0|
S0SdS65SbS19S23S26Sb2S20Sb1S21S39A1S1bZ4A1A3Sd6A3A1SeS19A1A3S1cS4S5Sa2A1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_t0P : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ413dcSbS2cZ413f0SeS2cA1A3A3S5S8eA1ScA5S11G0SbS6Sa8SeS6A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_t0P__R <: R_t0P__R = Some [r_t0P_0]). Qed.
Lemma LN_t0P : ltac2:(tb__ "0|0|
S0SdS1eS4S5S8eA1A1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_t0P : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4S5S8eA1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_inP : ltac2:(tb__ "0|0|
S0SdS8S5Sa8A1S7bS9eA3ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_inP : ltac2:(tb__ "0|0|
S0SdS6cS9eS30A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma S_in4P : ltac2:(tb__ "0|0|
S0S18S6bS9eS39A2S20Sb1SbcS1bZ10A1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S_in6P : ltac2:(tb__ "0|0|
S0S18S6bS9eS42A2Sf6A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Definition xlP := Eval vm_compute in (keepn (la_state r_t1P_1) nob).
Definition R_9P__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ40cc8SeS2cA1A3Sa0ScA5").
Local Strategy expand [R_9P__R].
Definition r_9P := Eval vm_compute in ((fun ro19__ : option (list leafA) => (match ro19__ with Some l => l | None => [] end)) R_9P__R).
Definition r_9P_0 := Eval vm_compute in (nth 0 r_9P (mkLeafA xlP RsCut)).
Definition cellsfP := Eval vm_compute in (ob_cells (last (ss_objs (ax_S (cE1 (la_state r_9P_0) icc))) O_ri)).
Definition x3P := Eval vm_compute in (cE3 (cE2 (cE1 (la_state r_9P_0) icc))).
Definition r_zP := Eval vm_compute in (match sym_runA segsA FUEL [0x3c480] x3P true with Some l => l | None => [] end).
Definition r_zP_0 := Eval vm_compute in (nth 0 r_zP (mkLeafA x3P RsCut)).
Lemma R_9P : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ40cc8SeS2cA1A3Sa0ScA5S11G0SbS6S76SeS6A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_9P__R <: R_9P__R = Some [r_9P_0]). Qed.
Lemma LN_9P : ltac2:(tb__ "0|0|
S0SdS1eS4Sa0A1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_9P : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4Sa0A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_x1P : ltac2:(tb__ "0|0|
S0SdS1dS4S33S5S76A1S60A2A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_x1P : ltac2:(tb__ "0|5|
S0S12S10SfS10S18S18A2M0A1M1SfS19A1M2A2M3A1Sb8S4S5S76A1M4A1S4S33G4S60A2A1A2S11G3S13G1G2SbG0S13S18S18S55S4bA4SeG0A1A3SeS19A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NX_x1P : ltac2:(tb__ "0|1|
S0SdS68S1aS4S33S5S76A1M0S60A2A1A1S1aS4G0A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XX_1P : ltac2:(tb__ "0|1|
S0SfS10S18S18A2M0A1S9S33S5S76A1S60A2A1SeG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma IC_1P : ltac2:(tb__ "0|0|
S0S12S17A1Sc3S17S1fS4S33S5S76A1S60A2A1A1S60A3S11S17S51A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_1P : ltac2:(tb__ "0|2|
S0SfS17A1S1fS4S33S5S76A1S60A2M0A1A1M1S14S17S6aS17Sc4S44G0A1U2A2G1A3SbS17S38SbS17S101Sa4A1SeS17A1A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_1P : ltac2:(tb__ "0|0|
S0SdS57Sa4Sf3S5aSf4Sf5A5ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SK_2P : ltac2:(tb__ "0|1|
S0SfS10S10S18S18A2S18A2M0A1S69S17G0S66S1fS4S34S33S5S76A1S60A2A1A1A1A4S69S17G0S66S14S17SbeS61A1SbS17Sb9SbS17SbaSeS17A1A3A3A3A4A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XX_2P : ltac2:(tb__ "0|1|
S0SfS10S18S18A2M0A1S9S34S33S5S76A1S60A2A1A1SeG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_2Pb : ltac2:(tb__ "0|0|
S0SdS65SbdS61S6dA2S1cS4S34S33S5S76A1S60A2A1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_3aP : ltac2:(tb__ "0|0|
S0SdS1dS4S53S34S33S5S76A1S60A2A1A1A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_3bP : ltac2:(tb__ "0|0|
S0SdS1dS4S48S34S33S5S76A1S60A2A1A1A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FB_3P : ltac2:(tb__ "0|1|
S0SdSc2S19S25S1aS4S48S34S33S5S76A1S60A2A1A1A1M0A1A1S14S19S4cS1cG0A1A3A3ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_zP : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ3c480SeS2cA1A3S43S34S33S5S76A1S60A2A1A1ScA5S11G0SbS6SaaSeS6A1A3A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma LN_zP : ltac2:(tb__ "0|0|
S0SdS1eS4S43S34S33S5S76A1S60A2A1A1A1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_zP : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4S43S34S33S5S76A1S60A2A1A1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Definition s_xP := Eval vm_compute in (s_exit (la_state r_zP_0) e3p).
Lemma ENT_xP : ltac2:(tb__ "0|0|
S0SdS8S5SaaA1S64Sb0A3ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SX_xP : sx_okb s_xP = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma S149_xP : wsub_get s_xP 149%positive = vK.
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S159_xP : wsub_get s_xP 159%positive = vCHX.
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Definition pop_P A Kc rb tp0 md0 TR KIT HKc rho HE ph PH0 faP HSRC HKF HNFP HFILLR HIDS HCACHE :=
  pop_all A Kc rb tp0 md0 TR KIT HKc W0 UStopLe rho HW0 HE ph PH0 faP HSRC HKF HNFP HFILLR HIDS HCACHE FUEL ct0P r_t1P_0 r_t1P_1 nob s_bkP
    SK_tP XX_tP (inclb_incl _ _ XF_tPb) NX_tP W_t1P R_t1P LN_t1P OB_bP OB_xP ENT_bkP SID_bkP S_bk4P S_bk6P (In_of_inclb _ _ FB_bPb) (In_of_inclb _ _ FB_xPb)
    (la_state r_jP_0) r_t0P_0 s_inP e_srcP R_t0P LN_t0P NX_t0P ENT_inP SID_inP S_in4P S_in6P.
Definition exit_P A Kc rb tp0 md0 TR KIT HKc rho HE phX PHX HFILLX Hini HRIv HLEN HIDC :=
  exit_steps A Kc rb tp0 md0 TR KIT HKc W0 UStopLe rho HW0 HE phX PHX HFILLX Hini e16P vMFA e32P e48P HRIv HLEN HIDC FUEL xlP r_9P_0 r_zP_0 icc cellsfP
    R_9P LN_9P NX_9P W_x1P D_x1P NX_x1P XX_1P IC_1P OB_1P RI_1P SK_2P XX_2P (inclb_incl _ _ XF_2Pb) W_3aP W_3bP FB_3P R_zP LN_zP NX_zP.
Definition back_P CST XGL PFam HPF A Kc rb tp0 md0 TR KIT rho HW HE phF HREB HMK HLEN HPOP :=
  refill_back CST XGL PFam HPF A Kc rb tp0 md0 TR KIT W0 UStopLe rho HW HE phF HREB HMK HLEN e3p (la_state r_zP_0) s_xP ENT_xP SX_xP S149_xP S159_xP HPOP.
Definition R_t0M__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ413dcSbS2cZ413f0SeS2cA1A3A3S5S8dA1ScA5").
Local Strategy expand [R_t0M__R].
Definition r_t0M := Eval vm_compute in ((fun ro21__ : option (list leafA) => (match ro21__ with Some l => l | None => [] end)) R_t0M__R).
Definition r_t0M_0 := Eval vm_compute in (nth 0 r_t0M (mkLeafA (la_state r_jM_0) RsCut)).
Definition ct0M := Eval vm_compute in (cT0 (la_state r_t0M_0)).
Definition R_t1M__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ413dcSbS2cZ413f0SeS2cA1A3A3S3dS7aA1ScA5").
Local Strategy expand [R_t1M__R].
Definition r_t1M := Eval vm_compute in ((fun ro20__ : option (list leafA) => (match ro20__ with Some l => l | None => [] end)) R_t1M__R).
Definition r_t1M_0 := Eval vm_compute in (nth 0 r_t1M (mkLeafA (cT1 ct0M) RsCut)).
Definition r_t1M_1 := Eval vm_compute in (nth 1 r_t1M (mkLeafA (cT1 ct0M) RsCut)).
Definition s_inM := Eval vm_compute in (infer_sub GR (ax_S (la_state r_t0M_0)) (ax_S ct0M)).
Definition s_bkM := Eval vm_compute in (infer_sub GR (ax_S (keepn (la_state r_t1M_0) nob)) (ax_S ct0M)).
Lemma SK_tM : ltac2:(tb__ "0|1|
S0SfS10S10S18S18A2S18A2M0A1S69S17G0S66S1fS4S7aA1A1A4S69S17G0S66S14S17SbeS61A1SbS17Sb9SbS17SbaSbS17S38SbS17S3bSeS17A1A3A3A3A3A3A4A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XX_tM : ltac2:(tb__ "0|1|
S0SfS10S18S18A2M0A1S9S7aA1SeG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_tMb : ltac2:(tb__ "0|0|
S0SdS65SbdS61S6dA2S1cS4S7aA1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NX_tM : ltac2:(tb__ "0|0|
S0SdS68S1aS4S7aA1A1S52A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_t1M : ltac2:(tb__ "0|0|
S0SdS1dS4S3dS7aA1A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_t1M : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ413dcSbS2cZ413f0SeS2cA1A3A3S3dS7aA1ScA5S11G0SbS6S99SbS6Sa1SeS6A1A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_t1M__R <: R_t1M__R = Some [r_t1M_0; r_t1M_1]). Qed.
Lemma LN_t1M : ltac2:(tb__ "0|0|
S0SdS1eS4S3dS7aA1A1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma OB_bM : ltac2:(tb__ "0|1|
S0SfS17A1S1fS4S5S99A1A1A1M0S14S17S6aS17S63G0A3SbS17Sd5SbS17Sd4SeS17A1A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_xM : ltac2:(tb__ "0|1|
S0SfS17A1S1fS4S5Sa1A1A1A1M0S14S17S6aS17S63G0A3SbS17Sd5SbS17Sd4SeS17A1A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma ENT_bkM : ltac2:(tb__ "0|0|
S0SdS8S35S5S99A1S63A2S7aS9bA3ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_bkM : ltac2:(tb__ "0|0|
S0SdS6cS9bS30A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma S_bk4M : ltac2:(tb__ "0|0|
S0S18S6bS9bS39A2S20Sb1S21S39A1S1bZ4A1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S_bk6M : ltac2:(tb__ "0|0|
S0S18S6bS9bS42A2S20Sb1S21S42A1S1bZ4A1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma FB_bMb : ltac2:(tb__ "0|0|
S0SdS65SbS19S26Sb2S20Sb1S21S39A1S1bZ4A1A3Sd6A3SeS19A1A3S1cS4S5S99A1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FB_xMb : ltac2:(tb__ "0|0|
S0SdS65SbS19S23S26Sb2S20Sb1S21S39A1S1bZ4A1A3Sd6A3A1SeS19A1A3S1cS4S5Sa1A1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_t0M : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ413dcSbS2cZ413f0SeS2cA1A3A3S5S8dA1ScA5S11G0SbS6Sa7SeS6A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_t0M__R <: R_t0M__R = Some [r_t0M_0]). Qed.
Lemma LN_t0M : ltac2:(tb__ "0|0|
S0SdS1eS4S5S8dA1A1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_t0M : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4S5S8dA1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_inM : ltac2:(tb__ "0|0|
S0SdS8S5Sa7A1S7aS9dA3ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_inM : ltac2:(tb__ "0|0|
S0SdS6cS9dS30A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma S_in4M : ltac2:(tb__ "0|0|
S0S18S6bS9dS39A2S20Sb1SbcS1bZ10A1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S_in6M : ltac2:(tb__ "0|0|
S0S18S6bS9dS42A2Sf6A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Definition xlM := Eval vm_compute in (keepn (la_state r_t1M_1) nob).
Definition R_9M__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ40cc8SeS2cA1A3S9fScA5").
Local Strategy expand [R_9M__R].
Definition r_9M := Eval vm_compute in ((fun ro22__ : option (list leafA) => (match ro22__ with Some l => l | None => [] end)) R_9M__R).
Definition r_9M_0 := Eval vm_compute in (nth 0 r_9M (mkLeafA xlM RsCut)).
Definition cellsfM := Eval vm_compute in (ob_cells (last (ss_objs (ax_S (cE1 (la_state r_9M_0) icc))) O_ri)).
Definition x3M := Eval vm_compute in (cE3 (cE2 (cE1 (la_state r_9M_0) icc))).
Definition r_zM := Eval vm_compute in (match sym_runA segsA FUEL [0x3c480] x3M true with Some l => l | None => [] end).
Definition r_zM_0 := Eval vm_compute in (nth 0 r_zM (mkLeafA x3M RsCut)).
Lemma R_9M : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ40cc8SeS2cA1A3S9fScA5S11G0SbS6S75SeS6A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_9M__R <: R_9M__R = Some [r_9M_0]). Qed.
Lemma LN_9M : ltac2:(tb__ "0|0|
S0SdS1eS4S9fA1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_9M : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4S9fA1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_x1M : ltac2:(tb__ "0|0|
S0SdS1dS4S33S5S75A1S60A2A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_x1M : ltac2:(tb__ "0|5|
S0S12S10SfS10S18S18A2M0A1M1SfS19A1M2A2M3A1Sb8S4S5S75A1M4A1S4S33G4S60A2A1A2S11G3S13G1G2SbG0S13S18S18S55S4bA4SeG0A1A3SeS19A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NX_x1M : ltac2:(tb__ "0|1|
S0SdS68S1aS4S33S5S75A1M0S60A2A1A1S1aS4G0A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XX_1M : ltac2:(tb__ "0|1|
S0SfS10S18S18A2M0A1S9S33S5S75A1S60A2A1SeG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma IC_1M : ltac2:(tb__ "0|0|
S0S12S17A1Sc3S17S1fS4S33S5S75A1S60A2A1A1S60A3S11S17S51A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_1M : ltac2:(tb__ "0|2|
S0SfS17A1S1fS4S33S5S75A1S60A2M0A1A1M1S14S17S6aS17Sc4S44G0A1U2A2G1A3SbS17S38SbS17S101Sa3A1SeS17A1A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_1M : ltac2:(tb__ "0|0|
S0SdS57Sa3Sf3Sf7Sf4Sf5A5ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SK_2M : ltac2:(tb__ "0|1|
S0SfS10S10S18S18A2S18A2M0A1S69S17G0S66S1fS4S34S33S5S75A1S60A2A1A1A1A4S69S17G0S66S14S17SbeS61A1SbS17Sb9SbS17SbaSeS17A1A3A3A3A4A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XX_2M : ltac2:(tb__ "0|1|
S0SfS10S18S18A2M0A1S9S34S33S5S75A1S60A2A1A1SeG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_2Mb : ltac2:(tb__ "0|0|
S0SdS65SbdS61S6dA2S1cS4S34S33S5S75A1S60A2A1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_3aM : ltac2:(tb__ "0|0|
S0SdS1dS4S53S34S33S5S75A1S60A2A1A1A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_3bM : ltac2:(tb__ "0|0|
S0SdS1dS4S48S34S33S5S75A1S60A2A1A1A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FB_3M : ltac2:(tb__ "0|1|
S0SdSc2S19S25S1aS4S48S34S33S5S75A1S60A2A1A1A1M0A1A1S14S19S4cS1cG0A1A3A3ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_zM : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ3c480SeS2cA1A3S43S34S33S5S75A1S60A2A1A1ScA5S11G0SbS6Sa9SeS6A1A3A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma LN_zM : ltac2:(tb__ "0|0|
S0SdS1eS4S43S34S33S5S75A1S60A2A1A1A1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_zM : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4S43S34S33S5S75A1S60A2A1A1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Definition s_xM := Eval vm_compute in (s_exit (la_state r_zM_0) e3p).
Lemma ENT_xM : ltac2:(tb__ "0|0|
S0SdS8S5Sa9A1S64SafA3ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SX_xM : sx_okb s_xM = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma S149_xM : wsub_get s_xM 149%positive = vK.
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S159_xM : wsub_get s_xM 159%positive = vCHX.
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Definition pop_M A Kc rb tp0 md0 TR KIT HKc rho HE ph PH0 faP HSRC HKF HNFP HFILLR HIDS HCACHE :=
  pop_all A Kc rb tp0 md0 TR KIT HKc W0 UStopLe rho HW0 HE ph PH0 faP HSRC HKF HNFP HFILLR HIDS HCACHE FUEL ct0M r_t1M_0 r_t1M_1 nob s_bkM
    SK_tM XX_tM (inclb_incl _ _ XF_tMb) NX_tM W_t1M R_t1M LN_t1M OB_bM OB_xM ENT_bkM SID_bkM S_bk4M S_bk6M (In_of_inclb _ _ FB_bMb) (In_of_inclb _ _ FB_xMb)
    (la_state r_jM_0) r_t0M_0 s_inM e_srcP R_t0M LN_t0M NX_t0M ENT_inM SID_inM S_in4M S_in6M.
Definition exit_M A Kc rb tp0 md0 TR KIT HKc rho HE phX PHX HFILLX Hini HRIv HLEN HIDC :=
  exit_steps A Kc rb tp0 md0 TR KIT HKc W0 UStopLe rho HW0 HE phX PHX HFILLX Hini e16P e24M e32P e48P HRIv HLEN HIDC FUEL xlM r_9M_0 r_zM_0 icc cellsfM
    R_9M LN_9M NX_9M W_x1M D_x1M NX_x1M XX_1M IC_1M OB_1M RI_1M SK_2M XX_2M (inclb_incl _ _ XF_2Mb) W_3aM W_3bM FB_3M R_zM LN_zM NX_zM.
Definition back_M CST XGL PFam HPF A Kc rb tp0 md0 TR KIT rho HW HE phF HREB HMK HLEN HPOP :=
  refill_back CST XGL PFam HPF A Kc rb tp0 md0 TR KIT W0 UStopLe rho HW HE phF HREB HMK HLEN e3p (la_state r_zM_0) s_xM ENT_xM SX_xM S149_xM S159_xM HPOP.

Theorem refill_populate_i : ltac2:(tb__ "0|4|
SfS10S2cS2cA2A1M0G0Se3S6eSfS10SaSeeA2A1F_;F_;S108R3R2R1A3SaS0SaR1S64A3Se3S6eS24SfS110Q40M1A1A1M2Se2Se2OF_;F_;Sc1R4R1A2S6fR5A1S0SdSe4R7A1ScA3SebS2dSc7R6R5RcR8R7A2A5Se2S24Se0ScaRbR2R8R1S61S6dR9A7SdbRcR3A2Sc8S3S0Sc8R1SffA3S0Sc8R1Sf9A3A2S111G1S2bR6PcA2A2S2cS109R1A1S2cS10aR11R2A2Se5S2S0Sc8R5Sf9A3S10dSe7R1A1S10eZ4S10cS10fS16S2cSe6R1A1A2A1ScbR12R9A2A2A2A2A2S24G2SfSe1A1Se0Sc9R17R16ReR14RdSfeRaScbR17ReA2S106R7A1A3R4R3R2R1AaS1S105S2dS107R18R8A2M3R5R4R2A5S70R1eR1dR18G3S28RfA1S28R5A1A6A2F_;Fmd;Ftr;Ftp';Fr;F_;Tcs;Tc;Tnv;F_;FphX;FPF;FHE;Fmd0;Frb;Se3S24G2S24RaSeaS2dS10bS61S6dR4RdR3A5R10R1R2A5SebS2dSc7R3R2R12R4RdA2A5A2FrX;Ftp';Frho';FA';S24Se0S24ScaReR3RbR2S61S6dRcA7RbSeaS2dSc9RfReR4RcR3SccA6S5S62A1R2RcA5R7A2F_;Fr';Fmd0;Frb;F_;F_;TQ;F_;FHKc;FKIT;FTR;Ftp;Frho;FKc;FA;F_;FE3P;FHPF;FPFam;FXGL;FCST;").
Proof.
  intros CST XGL PFam HPF E3P ->.
  apply (refill_populate CST XGL PFam W0 UStopLe (la_state r_2_0) cp2c ru1 (la_state r_f_0) (la_state r_f_1) cfm rf1 (la_state r_h_0)
           (la_state r_jP_0) xlP (la_state r_zP_0) (la_state r_jM_0) xlM (la_state r_zM_0) e3p head_i pieceU_i mid_i fm_i pieceF_i run_i fillP_i fillM_i).
  - intros A Kc rb tp0 md0 TR KIT HKc rho HE ph PH0 faP. exact (pop_P A Kc rb tp0 md0 TR KIT HKc rho HE ph PH0 faP).
  - intros A Kc rb tp0 md0 TR KIT HKc rho HE ph PH0 faP. exact (pop_M A Kc rb tp0 md0 TR KIT HKc rho HE ph PH0 faP).
  - intros A Kc rb tp0 md0 TR KIT HKc rho HE phX. exact (exit_P A Kc rb tp0 md0 TR KIT HKc rho HE phX).
  - intros A Kc rb tp0 md0 TR KIT HKc rho HE phX. exact (exit_M A Kc rb tp0 md0 TR KIT HKc rho HE phX).
  - intros A Kc rb tp0 md0 TR KIT rho HE phF. exact (back_P CST XGL PFam HPF A Kc rb tp0 md0 TR KIT rho HW0 HE phF).
  - intros A Kc rb tp0 md0 TR KIT rho HE phF. exact (back_M CST XGL PFam HPF A Kc rb tp0 md0 TR KIT rho HW0 HE phF).
Qed.
End SpineCallocRp0u.

(* [comment removed for export] *)
Module CRefillPlug0.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "rm"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "eq"; "False"; "and"; "iff"; "not"; "or"; "@Corelib.Init.Datatypes"; "list"; "bool"; "length"; "prod"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_cache_inited"; "class_state"; "cs_free_array"; "cs_mapped_free_array"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "mem_keptA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CRefillJ"; "phase"; "gh_new"; "JR"; "entryR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1"; "JG"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP"; "E3r"; "E3p"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "cnt_of"; "cls_of"; "cst_of"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.CallocPosts"; "PFc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bq.SpineCallocR15"; "phUF3"; "phFin"; "phU3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM"; "IMG_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel"; "kchunks"; "refillA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR"; "TRok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "dfp_static"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.SpineCallocR5"; "posts_conv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SpineCallocR7"; "popfacts"; "@Stdlib.ZArith.BinInt.Z"; "add"; "lt"; "mul"; "of_nat"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymFrame Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA GlueA SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocSP RebuildM SegD_wf SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillTR CRefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ba.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bm.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require dc.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CRefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.CRefillJP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineCallocR2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.SpineCallocR5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bm.SpineCallocR6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SpineCallocR7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bn.SpineCallocR14 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bq.SpineCallocR15 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bn.CRebuildRN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bs.CRebuildRQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.RebuildI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cf.CallocHitTail0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dc.CallocHitTail0E.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bm.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.CallocPosts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bm.SpineCallocR5c.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Local Notation segs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree.segsA.

Section PLUG0.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTM : ltac2:(tb__ "0|0|
S4S27VCST;R1A2S27S38R2A2S6F_;F_;Fa;").
Hypothesis HCSTD : ltac2:(tb__ "0|0|
S4S27VCST;R1A2S9S3cR2A1A1F_;Fa;").
Let W0 : list ulink := Wcan 0.
Let st0 : ustop := UStopLe.

Lemma hreb_Q : ltac2:(tb__ "0|3|
S10S15S1SbS23Q40M0A1A1M1S5ScS11R4A1SfA3S1S2bS21R7R2R4R1VW0;Vst0;R5A7S3eR8R3A2S1eSaS5S1eR1S34A3S5S1eR1S32A3A2S24G0S2R6PcA2A2S4S29R1A1S4S2aRdR2A2S12S8S5S1eR5S32A3S40S14R1A1S41Z4S3fS42SdS4S13R1A1A2A1S1fReR9A2A2A2A2A2S1G1SbS2cA1S2bS20R13R12ReR10RdS33RaS1fR13ReA2S39R7A1A3R4R3R2R1AaS7S37S0S3aR14R8A2M2R5R4R2A5S17VCST;VXGL;R14G2S3RfA1S3R5A1A6A2F_;Fmd;Ftr;Ftp';Fr;F_;Tcs;Tc;Tnv;F_;FphX;FPF;FHE;Fmd0;Frb;F_;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp Hini rb md0 HE PF phX [-> | ->] nv c cs HB r tp' tr md HJ.
  - rewrite phQ_P in HJ. apply (refill_rebuild_Q CST XGL HCST HXGL A Kc rb tp md0 W0 st0 rho HE PF false Hini) with (tr := tr); [|exact HJ].
    split; [discriminate|]. intros HLT. apply HB in HLT. unfold phU3, phUF3 in HLT. discriminate HLT.
  - rewrite phQ_M in HJ. apply (refill_rebuild_Q CST XGL HCST HXGL A Kc rb tp md0 W0 st0 rho HE PF true Hini) with (tr := tr); [|exact HJ].
    split; [intros _; apply HB; reflexivity | reflexivity].
Qed.

Theorem refill_core_0 : ltac2:(tb__ "0|3|
S15S2dS2dOF_;F_;S3bR2R1A2S16R3A1S10S15SbSeS35S1dA2A1F_;F_;S3dVCST;VXGL;R1A3S10S1SbS23Q40M0A1A1M1S1R9S19S0S22VW0;Vst0;R4RaR3A5S26VW0;Vst0;Z2M2A3R1R2A5S1cS0S18R3R2R6R4RaA2A5A2FrX;Ftp';Frho';FA';S10S1G1S5S4S28R3S24G0S2R2PcA2A2A2Z0A3S1RbS19S0S22VW0;Vst0;R5RcR4A5S25VW0;Vst0;G2A3R1R3A5S1cS0S18R4R3R8R5RcA2A5A2FrhoE;F_;Ftp;Frho;FA;F_;FHPF;FPFam;FHKc;FKIT;FTR;FKc;").
Proof.
  intros Kc TR KIT HKc PFam HPF HPOP A rho tp Hcnt.
  destruct (aa_cache_inited A) eqn:Hini.
  -
    apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bn.SpineCallocRi0.refill_N_i CST XGL PFam HPF (E3r W0 st0 2) (E3p W0 st0 2) OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bn.SpineCallocRi0.E3r_eq OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bn.SpineCallocRi0.E3p_eq A Kc rho tp TR KIT HKc Hini Hcnt).
    + intros rb md0 HE HNP r tp' tr md HJ. exact (refill_rebuild_N CST XGL HCST HXGL A Kc rb tp md0 W0 st0 rho HE Hini HNP r tp' tr md HJ).
    + exact HPOP.
    + exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cb.SpineCallocRp0.refill_populate_i CST XGL PFam HPF (E3p W0 st0 2) OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bn.SpineCallocRi0.E3p_eq A Kc rho tp TR KIT HKc Hini (hreb_Q A Kc rho tp Hini) HPOP).
  -
    apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bu.SpineCallocRu0.refill_uninit_i CST XGL HCST HXGL PFam HPF (E3r W0 st0 2) OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bu.SpineCallocRu0.e3u OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bn.SpineCallocRi0.E3r_eq eq_refl A Kc rho tp TR KIT HKc Hini Hcnt).
    intros rho1 rX E1.
    assert (Hcnt1 : cnt_of (initA A) (bv_unsigned (rw rho1 12%positive)) = 0) by (rewrite E1; exact Hcnt).
    assert (Hini1 : aa_cache_inited (initA A) = true) by reflexivity.
    apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c2.SpineCallocRi0u.refill_N_i CST XGL PFam HPF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bu.SpineCallocRu0.e3u (E3p W0 st0 2) eq_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c2.SpineCallocRi0u.E3p_eq (initA A) Kc rho1 tp TR KIT HKc Hini1 Hcnt1).
    + intros rb md0 HE HNP r tp' tr md HJ. exact (refill_rebuild_N CST XGL HCST HXGL (initA A) Kc rb tp md0 W0 st0 rho1 HE Hini1 HNP r tp' tr md HJ).
    + exact HPOP.
    + exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cb.SpineCallocRp0u.refill_populate_i CST XGL PFam HPF (E3p W0 st0 2) OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c2.SpineCallocRi0u.E3p_eq (initA A) Kc rho1 tp TR KIT HKc Hini1 (hreb_Q (initA A) Kc rho1 tp Hini1) HPOP).
Qed.

Theorem refill_all_0 : ltac2:(tb__ "0|1|
S30OF_;S10S15S1SbS23Q40M0A1A1S16R3A1S1bS0R6S1aR4A1A3S36S0R7S1aR5A1A3S5S4S28R7S24G0S2R5PcA2A2A2Z0A3S1S2fS0RaS19S0S22VW0;Vst0;R9R8R7A5S25VW0;Vst0;Z2A3R1R6A5S1cS0S18R7R6S31VCST;VXGL;VW0;Vst0;R9R8A6A5A4FrhoE;F_;F_;F_;F_;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp HKc Hokl Hokp Hcnt.
  apply (refill_core_0 Kc (triple segs ok) (TRok_triple Kc ok Hokl Hokp) HKc (PFc CST XGL W0 st0) (posts_conv_c CST XGL W0 st0)); [|exact Hcnt].
  intros A' rho' tp' rX. exact (calloc_hit_tail_0 CST XGL HCST HXGL HCSTM HCSTD ok A' Kc rho' tp' HKc Hokl Hokp rX).
Qed.

Theorem erefill_all_0 : ltac2:(tb__ "0|1|
S10S15S1SbS23Q40M0A1A1S16R3A1S5S4S28R5S24G0S2R3PcA2A2A2Z0A3S1S2eS0S19S0S22VW0;Vst0;R7R6R5A5S25VW0;Vst0;Z2A3R1R4A5S1cS0S18R5R4S31VCST;VXGL;VW0;Vst0;R7R6A6A5A3FrhoE;F_;F_;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp HKc Hcnt.
  apply (refill_core_0 Kc (etriple segs) (TRok_etriple Kc) HKc (PFc CST XGL W0 st0) (posts_conv_c CST XGL W0 st0)); [|exact Hcnt].
  intros A' rho' tp' rX. exact (ecalloc_hit_tail_0 CST XGL HCST HXGL HCSTM HCSTD A' Kc rho' tp' HKc rX).
Qed.
End PLUG0.
End CRefillPlug0.

