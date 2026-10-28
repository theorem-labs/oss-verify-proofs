(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.fhmtgen_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptRoom DwaLib.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require Import V10LeptStderr V10LeptBase.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require Import V10CL7a.
Import V10CL7a.V10LeptErr.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require Import V10CL8a.
Import V10CL8a.V10LeptPixHdr.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require Import V10LeptCmap2.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require Import V10CL9a.
Import V10CL9a.V10LeptDwa_iface.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require Import LeptArith2 GrayLib.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require Import V10_code_fhI.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require V10DwaA V10DwaB V10DwaC V10DwaD.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


(* [comment removed for export] *)
(* [comment removed for export] *)
Section RUN.
Context {fx : FPState}.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Notation "'u'" := bv_unsigned (only parsing).

  Variable M0 : word -> option byte.          (* [comment removed for export] *)
  Variable rom : word -> option byte.
  Variables w h wpls wpld PW datas datad s index : Z.
  Variables rav s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v gpv tpv : word.
  Hypothesis Hw : (1 <= w < 2 ^ 30)%Z.
  Hypothesis Hh : (1 <= h < 2 ^ 30)%Z.
  Hypothesis Hwpls : (1 <= wpls < 2 ^ 26)%Z.
  Hypothesis Hwpld : (1 <= wpld < 2 ^ 26)%Z.
  Hypothesis HPW : ((w + 31) / 2 ^ 5 = PW)%Z.
  Hypothesis Hsz : ((wpls * h) < 2 ^ 28 /\ (wpld * h) < 2 ^ 28)%Z.
  Hypothesis Hs : (2 ^ 18 <= s /\ s <= 2 ^ 63)%Z.
  Hypothesis Hidx : (0 <= index <= 9)%Z.
  Hypothesis Hret : ret_ok rav.
  #[local] Abbreviation SLO := (datas - 24 * wpls - 4)%Z (only parsing).
  #[local] Abbreviation SHI := (datas + 4 * (wpls * h) + 20 * wpls + 4 * PW + 8)%Z (only parsing).
  #[local] Abbreviation DN := (4 * (wpld * h) - 4 * wpld + 4 * PW)%Z (only parsing).
  Hypothesis Hds : (4096 <= SLO /\ SHI <= 2 ^ 62)%Z.
  Hypothesis Hdd : (4096 <= datad /\ datad + DN <= 2 ^ 62)%Z.
  Hypothesis SOKs0 : store_ok SEGS M0 (Z_to_bv 64 SLO) (Z.to_nat (SHI - SLO)) = true.
  Hypothesis SOKd0 : store_ok SEGS M0 (Z_to_bv 64 datad) (Z.to_nat DN) = true.
  Hypothesis SOKf0 : store_ok SEGS M0 (Z_to_bv 64 (s - 272)) 272 = true.
  Hypothesis FR : disj_apart datad DN (s - 272) 272.
  Hypothesis Hals : (datas mod 4 = 0)%Z.
  Hypothesis Hald : (datad mod 4 = 0)%Z.
  (* [comment removed for export] *)
  Hypothesis JT0 : rdn SEGS M0 (Z_to_bv 64 72152) 4 = Some (Z_to_le_bytes 4 93840).
  Hypothesis JT1 : rdn SEGS M0 (Z_to_bv 64 72156) 4 = Some (Z_to_le_bytes 4 98364).
  Hypothesis JT2 : rdn SEGS M0 (Z_to_bv 64 72160) 4 = Some (Z_to_le_bytes 4 96232).
  Hypothesis JT3 : rdn SEGS M0 (Z_to_bv 64 72164) 4 = Some (Z_to_le_bytes 4 96804).
  Hypothesis JT4 : rdn SEGS M0 (Z_to_bv 64 72168) 4 = Some (Z_to_le_bytes 4 94616).
  Hypothesis JT5 : rdn SEGS M0 (Z_to_bv 64 72172) 4 = Some (Z_to_le_bytes 4 98852).
  Hypothesis JT6 : rdn SEGS M0 (Z_to_bv 64 72176) 4 = Some (Z_to_le_bytes 4 99728).
  Hypothesis JT7 : rdn SEGS M0 (Z_to_bv 64 72180) 4 = Some (Z_to_le_bytes 4 97432).
  Hypothesis JT8 : rdn SEGS M0 (Z_to_bv 64 72184) 4 = Some (Z_to_le_bytes 4 100636).
  Hypothesis JT9 : rdn SEGS M0 (Z_to_bv 64 72188) 4 = Some (Z_to_le_bytes 4 95216).

  Definition ENTRY (regs : bvmap 5 word) : Prop :=
    getr regs 2 = Z_to_bv 64 s /\ getr regs 1 = rav /\ getr regs 8 = s0v /\ getr regs 9 = s1v /\ getr regs 18 = s2v /\ getr regs 19 = s3v /\ getr regs 20 = s4v /\
    getr regs 21 = s5v /\ getr regs 22 = s6v /\ getr regs 23 = s7v /\ getr regs 24 = s8v /\ getr regs 25 = s9v /\ getr regs 26 = s10v /\ getr regs 27 = s11v /\
    getr regs 3 = gpv /\ getr regs 4 = tpv /\
    getr regs 10 = Z_to_bv 64 datad /\ getr regs 11 = Z_to_bv 64 w /\ getr regs 12 = Z_to_bv 64 h /\ getr regs 13 = Z_to_bv 64 wpld /\
    getr regs 14 = Z_to_bv 64 datas /\ getr regs 15 = Z_to_bv 64 wpls.

  (* [comment removed for export] *)
  Definition MS : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes M0
      (Z_to_bv 64 (s - 272 + 264)) (word_to_le_bytes 8 rav))
      (Z_to_bv 64 (s - 272 + 256)) (word_to_le_bytes 8 s0v))
      (Z_to_bv 64 (s - 272 + 248)) (word_to_le_bytes 8 s1v))
      (Z_to_bv 64 (s - 272 + 240)) (word_to_le_bytes 8 s2v))
      (Z_to_bv 64 (s - 272 + 232)) (word_to_le_bytes 8 s3v))
      (Z_to_bv 64 (s - 272 + 224)) (word_to_le_bytes 8 s4v))
      (Z_to_bv 64 (s - 272 + 216)) (word_to_le_bytes 8 s5v))
      (Z_to_bv 64 (s - 272 + 208)) (word_to_le_bytes 8 s6v))
      (Z_to_bv 64 (s - 272 + 200)) (word_to_le_bytes 8 s7v))
      (Z_to_bv 64 (s - 272 + 192)) (word_to_le_bytes 8 s8v))
      (Z_to_bv 64 (s - 272 + 184)) (word_to_le_bytes 8 s9v))
      (Z_to_bv 64 (s - 272 + 176)) (word_to_le_bytes 8 s10v))
      (Z_to_bv 64 (s - 272 + 168)) (word_to_le_bytes 8 s11v).
  Definition M : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes MS (Z_to_bv 64 (s - 272 + 160)) (word_to_le_bytes 8 (Z_to_bv 64 datas))) (Z_to_bv 64 (s - 272 + 144)) (word_to_le_bytes 8 (Z_to_bv 64 wpld)))
      (Z_to_bv 64 (s - 272 + 88)) (word_to_le_bytes 8 (Z_to_bv 64 h))) (Z_to_bv 64 (s - 272 + 152)) (word_to_le_bytes 8 (Z_to_bv 64 datad)).
  (* [comment removed for export] *)
  Definition KEN (regs : bvmap 5 word) (Mi : word -> option byte) : Prop :=
    dwa_MInv M datad DN (s - 272) 168 Mi /\ dwa_cell SEGS (s - 272) Mi 88 (Z_to_bv 64 h) /\ dwa_cell SEGS (s - 272) Mi 144 (Z_to_bv 64 wpld) /\
    dwa_cell SEGS (s - 272) Mi 152 (Z_to_bv 64 datad) /\ dwa_cell SEGS (s - 272) Mi 160 (Z_to_bv 64 datas) /\
    getr regs 2 = Z_to_bv 64 (s - 272) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\
    getr regs 11 = Z_to_bv 64 w /\ getr regs 13 = Z_to_bv 64 wpld /\ getr regs 14 = Z_to_bv 64 datas /\ getr regs 15 = Z_to_bv 64 wpls.

  Ltac grows := repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl.
  Lemma M_grows : mem_grows M0 M.
  Proof. unfold M, MS. grows. Qed.
  Ltac stf0 F D off v :=
    stepST F D (Z_to_bv 64 (s - 272 + off)) v
      ltac:(store_ok_peel; eapply store_ok_mono; [ grows | eapply (store_ok_sub SEGS M0 (Z_to_bv 64 (s - 272)) _ 272); [ | exact SOKf0 | | ]; rewrite ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ]).
  Ltac jtpeel := repeat (rewrite rdn_wbytes_out_Z by (zlen; lia)).
  Ltac cellm :=
    unfold dwa_cell, M, MS;
    repeat (lazymatch goal with
            | |- rdn _ (wbytes _ ?a _) ?b 8 = _ => tryif constr_eq a b then fail else rewrite rdn_wbytes_out_Z by (zlen; lia)
            end);
    apply rdn_wbytes_hit8; unorm; lia.
  Ltac ken := unfold KEN; split; [unfold dwa_MInv; split; [intros; reflexivity | apply mem_grows_refl] | repeat split; first [ cellm | (gres; pin; reflexivity) ] ].

  Definition PRE (regs : bvmap 5 word) : Prop :=
    getr regs 2 = Z_to_bv 64 (s - 272) /\ getr regs 3 = gpv /\ getr regs 4 = tpv /\
    getr regs 11 = Z_to_bv 64 w /\ getr regs 13 = Z_to_bv 64 wpld /\ getr regs 14 = Z_to_bv 64 datas /\ getr regs 15 = Z_to_bv 64 wpls /\ getr regs 16 = Z_to_bv 64 index.
  Lemma dsp_pre : forall regs, ENTRY regs -> getr regs 16 = Z_to_bv 64 index ->
    exists regs', msteps SEGS (mkst regs (0x287f8 : word) M0 rom) (mkst regs' (0x2884c : word) M rom) /\ PRE regs'.
  Proof.
    intros regs HE H16. unfold ENTRY in HE. repeat (let X := fresh "HE" in destruct HE as (X & HE)). unfold M, MS. eexists. split.
    - zv F_286fc D_286fc (Z_to_bv 64 (s - 272)).
      stf0 F_28700 D_28700 264%Z rav.
      stf0 F_28704 D_28704 256%Z s0v.
      stf0 F_28708 D_28708 248%Z s1v.
      stf0 F_2870c D_2870c 240%Z s2v.
      stf0 F_28710 D_28710 232%Z s3v.
      stf0 F_28714 D_28714 224%Z s4v.
      stf0 F_28718 D_28718 216%Z s5v.
      stf0 F_2871c D_2871c 208%Z s6v.
      stf0 F_28720 D_28720 200%Z s7v.
      stf0 F_28724 D_28724 192%Z s8v.
      stf0 F_28728 D_28728 184%Z s9v.
      stf0 F_2872c D_2872c 176%Z s10v.
      stf0 F_28730 D_28730 168%Z s11v.
      stf0 F_28734 D_28734 160%Z (Z_to_bv 64 datas).
      stf0 F_28738 D_28738 144%Z (Z_to_bv 64 wpld).
      stf0 F_2873c D_2873c 88%Z (Z_to_bv 64 h).
      sn F_28740 D_28740.
      stf0 F_28744 D_28744 152%Z (Z_to_bv 64 datad).
      stepb_tk F_28748 D_28748 ltac:(condZ).
      apply mst_refl.
    - unfold PRE. repeat split; gres; pin; reflexivity.
  Qed.

  Lemma dsp_0 : forall regs, PRE regs -> index = 0%Z ->
    exists regs', msteps SEGS (mkst regs (0x2884c : word) M rom) (mkst regs' (0x28868 : word) M rom) /\ KEN regs' M.
  Proof.
    intros regs HE EI. unfold PRE in HE. repeat (let X := fresh "HE" in destruct HE as (X & HE)). rewrite EI in HE. eexists. split.
    - sn F_28750 D_28750. fixv (Z_to_bv 64 0) ltac:(rewrite zbv_slli by lia; reflexivity).
      sn F_28754 D_28754. sn F_28758 D_28758. fixv (Z_to_bv 64 0x119d8) ltac:(apply bv_eq; reflexivity).
      zv F_2875c D_2875c (Z_to_bv 64 72152).
      stepLD F_28760 D_28760 (Z_to_le_bytes 4 93840) (Z_to_bv 64 93840) ltac:(addr_norm; rewrite ?Z.add_0_r; unfold M, MS; jtpeel; exact JT0) ltac:(apply W2Lib.lez4; lia).
      change (v_lw (Z_to_bv 64 93840)) with (Z_to_bv 64 93840).
      zv F_28764 D_28764 (Z_to_bv 64 165992).
      stepret F_28768 D_28768 (0x28868 : word) ltac:(bveq).
      apply mst_refl.
    - ken.
  Qed.

  Lemma dsp_1 : forall regs, PRE regs -> index = 1%Z ->
    exists regs', msteps SEGS (mkst regs (0x2884c : word) M rom) (mkst regs' (0x29a14 : word) M rom) /\ KEN regs' M.
  Proof.
    intros regs HE EI. unfold PRE in HE. repeat (let X := fresh "HE" in destruct HE as (X & HE)). rewrite EI in HE. eexists. split.
    - sn F_28750 D_28750. fixv (Z_to_bv 64 4) ltac:(rewrite zbv_slli by lia; reflexivity).
      sn F_28754 D_28754. sn F_28758 D_28758. fixv (Z_to_bv 64 0x119d8) ltac:(apply bv_eq; reflexivity).
      zv F_2875c D_2875c (Z_to_bv 64 72156).
      stepLD F_28760 D_28760 (Z_to_le_bytes 4 98364) (Z_to_bv 64 98364) ltac:(addr_norm; rewrite ?Z.add_0_r; unfold M, MS; jtpeel; exact JT1) ltac:(apply W2Lib.lez4; lia).
      change (v_lw (Z_to_bv 64 98364)) with (Z_to_bv 64 98364).
      zv F_28764 D_28764 (Z_to_bv 64 170516).
      stepret F_28768 D_28768 (0x29a14 : word) ltac:(bveq).
      apply mst_refl.
    - ken.
  Qed.

  Lemma dsp_2 : forall regs, PRE regs -> index = 2%Z ->
    exists regs', msteps SEGS (mkst regs (0x2884c : word) M rom) (mkst regs' (0x291c0 : word) M rom) /\ KEN regs' M.
  Proof.
    intros regs HE EI. unfold PRE in HE. repeat (let X := fresh "HE" in destruct HE as (X & HE)). rewrite EI in HE. eexists. split.
    - sn F_28750 D_28750. fixv (Z_to_bv 64 8) ltac:(rewrite zbv_slli by lia; reflexivity).
      sn F_28754 D_28754. sn F_28758 D_28758. fixv (Z_to_bv 64 0x119d8) ltac:(apply bv_eq; reflexivity).
      zv F_2875c D_2875c (Z_to_bv 64 72160).
      stepLD F_28760 D_28760 (Z_to_le_bytes 4 96232) (Z_to_bv 64 96232) ltac:(addr_norm; rewrite ?Z.add_0_r; unfold M, MS; jtpeel; exact JT2) ltac:(apply W2Lib.lez4; lia).
      change (v_lw (Z_to_bv 64 96232)) with (Z_to_bv 64 96232).
      zv F_28764 D_28764 (Z_to_bv 64 168384).
      stepret F_28768 D_28768 (0x291c0 : word) ltac:(bveq).
      apply mst_refl.
    - ken.
  Qed.

  Lemma dsp_3 : forall regs, PRE regs -> index = 3%Z ->
    exists regs', msteps SEGS (mkst regs (0x2884c : word) M rom) (mkst regs' (0x293fc : word) M rom) /\ KEN regs' M.
  Proof.
    intros regs HE EI. unfold PRE in HE. repeat (let X := fresh "HE" in destruct HE as (X & HE)). rewrite EI in HE. eexists. split.
    - sn F_28750 D_28750. fixv (Z_to_bv 64 12) ltac:(rewrite zbv_slli by lia; reflexivity).
      sn F_28754 D_28754. sn F_28758 D_28758. fixv (Z_to_bv 64 0x119d8) ltac:(apply bv_eq; reflexivity).
      zv F_2875c D_2875c (Z_to_bv 64 72164).
      stepLD F_28760 D_28760 (Z_to_le_bytes 4 96804) (Z_to_bv 64 96804) ltac:(addr_norm; rewrite ?Z.add_0_r; unfold M, MS; jtpeel; exact JT3) ltac:(apply W2Lib.lez4; lia).
      change (v_lw (Z_to_bv 64 96804)) with (Z_to_bv 64 96804).
      zv F_28764 D_28764 (Z_to_bv 64 168956).
      stepret F_28768 D_28768 (0x293fc : word) ltac:(bveq).
      apply mst_refl.
    - ken.
  Qed.

  Lemma dsp_4 : forall regs, PRE regs -> index = 4%Z ->
    exists regs', msteps SEGS (mkst regs (0x2884c : word) M rom) (mkst regs' (0x28b70 : word) M rom) /\ KEN regs' M.
  Proof.
    intros regs HE EI. unfold PRE in HE. repeat (let X := fresh "HE" in destruct HE as (X & HE)). rewrite EI in HE. eexists. split.
    - sn F_28750 D_28750. fixv (Z_to_bv 64 16) ltac:(rewrite zbv_slli by lia; reflexivity).
      sn F_28754 D_28754. sn F_28758 D_28758. fixv (Z_to_bv 64 0x119d8) ltac:(apply bv_eq; reflexivity).
      zv F_2875c D_2875c (Z_to_bv 64 72168).
      stepLD F_28760 D_28760 (Z_to_le_bytes 4 94616) (Z_to_bv 64 94616) ltac:(addr_norm; rewrite ?Z.add_0_r; unfold M, MS; jtpeel; exact JT4) ltac:(apply W2Lib.lez4; lia).
      change (v_lw (Z_to_bv 64 94616)) with (Z_to_bv 64 94616).
      zv F_28764 D_28764 (Z_to_bv 64 166768).
      stepret F_28768 D_28768 (0x28b70 : word) ltac:(bveq).
      apply mst_refl.
    - ken.
  Qed.

  Lemma dsp_5 : forall regs, PRE regs -> index = 5%Z ->
    exists regs', msteps SEGS (mkst regs (0x2884c : word) M rom) (mkst regs' (0x29bfc : word) M rom) /\ KEN regs' M.
  Proof.
    intros regs HE EI. unfold PRE in HE. repeat (let X := fresh "HE" in destruct HE as (X & HE)). rewrite EI in HE. eexists. split.
    - sn F_28750 D_28750. fixv (Z_to_bv 64 20) ltac:(rewrite zbv_slli by lia; reflexivity).
      sn F_28754 D_28754. sn F_28758 D_28758. fixv (Z_to_bv 64 0x119d8) ltac:(apply bv_eq; reflexivity).
      zv F_2875c D_2875c (Z_to_bv 64 72172).
      stepLD F_28760 D_28760 (Z_to_le_bytes 4 98852) (Z_to_bv 64 98852) ltac:(addr_norm; rewrite ?Z.add_0_r; unfold M, MS; jtpeel; exact JT5) ltac:(apply W2Lib.lez4; lia).
      change (v_lw (Z_to_bv 64 98852)) with (Z_to_bv 64 98852).
      zv F_28764 D_28764 (Z_to_bv 64 171004).
      stepret F_28768 D_28768 (0x29bfc : word) ltac:(bveq).
      apply mst_refl.
    - ken.
  Qed.

  Lemma dsp_6 : forall regs, PRE regs -> index = 6%Z ->
    exists regs', msteps SEGS (mkst regs (0x2884c : word) M rom) (mkst regs' (0x29f68 : word) M rom) /\ KEN regs' M.
  Proof.
    intros regs HE EI. unfold PRE in HE. repeat (let X := fresh "HE" in destruct HE as (X & HE)). rewrite EI in HE. eexists. split.
    - sn F_28750 D_28750. fixv (Z_to_bv 64 24) ltac:(rewrite zbv_slli by lia; reflexivity).
      sn F_28754 D_28754. sn F_28758 D_28758. fixv (Z_to_bv 64 0x119d8) ltac:(apply bv_eq; reflexivity).
      zv F_2875c D_2875c (Z_to_bv 64 72176).
      stepLD F_28760 D_28760 (Z_to_le_bytes 4 99728) (Z_to_bv 64 99728) ltac:(addr_norm; rewrite ?Z.add_0_r; unfold M, MS; jtpeel; exact JT6) ltac:(apply W2Lib.lez4; lia).
      change (v_lw (Z_to_bv 64 99728)) with (Z_to_bv 64 99728).
      zv F_28764 D_28764 (Z_to_bv 64 171880).
      stepret F_28768 D_28768 (0x29f68 : word) ltac:(bveq).
      apply mst_refl.
    - ken.
  Qed.

  Lemma dsp_7 : forall regs, PRE regs -> index = 7%Z ->
    exists regs', msteps SEGS (mkst regs (0x2884c : word) M rom) (mkst regs' (0x29670 : word) M rom) /\ KEN regs' M.
  Proof.
    intros regs HE EI. unfold PRE in HE. repeat (let X := fresh "HE" in destruct HE as (X & HE)). rewrite EI in HE. eexists. split.
    - sn F_28750 D_28750. fixv (Z_to_bv 64 28) ltac:(rewrite zbv_slli by lia; reflexivity).
      sn F_28754 D_28754. sn F_28758 D_28758. fixv (Z_to_bv 64 0x119d8) ltac:(apply bv_eq; reflexivity).
      zv F_2875c D_2875c (Z_to_bv 64 72180).
      stepLD F_28760 D_28760 (Z_to_le_bytes 4 97432) (Z_to_bv 64 97432) ltac:(addr_norm; rewrite ?Z.add_0_r; unfold M, MS; jtpeel; exact JT7) ltac:(apply W2Lib.lez4; lia).
      change (v_lw (Z_to_bv 64 97432)) with (Z_to_bv 64 97432).
      zv F_28764 D_28764 (Z_to_bv 64 169584).
      stepret F_28768 D_28768 (0x29670 : word) ltac:(bveq).
      apply mst_refl.
    - ken.
  Qed.

  Lemma dsp_8 : forall regs, PRE regs -> index = 8%Z ->
    exists regs', msteps SEGS (mkst regs (0x2884c : word) M rom) (mkst regs' (0x2a2f4 : word) M rom) /\ KEN regs' M.
  Proof.
    intros regs HE EI. unfold PRE in HE. repeat (let X := fresh "HE" in destruct HE as (X & HE)). rewrite EI in HE. eexists. split.
    - sn F_28750 D_28750. fixv (Z_to_bv 64 32) ltac:(rewrite zbv_slli by lia; reflexivity).
      sn F_28754 D_28754. sn F_28758 D_28758. fixv (Z_to_bv 64 0x119d8) ltac:(apply bv_eq; reflexivity).
      zv F_2875c D_2875c (Z_to_bv 64 72184).
      stepLD F_28760 D_28760 (Z_to_le_bytes 4 100636) (Z_to_bv 64 100636) ltac:(addr_norm; rewrite ?Z.add_0_r; unfold M, MS; jtpeel; exact JT8) ltac:(apply W2Lib.lez4; lia).
      change (v_lw (Z_to_bv 64 100636)) with (Z_to_bv 64 100636).
      zv F_28764 D_28764 (Z_to_bv 64 172788).
      stepret F_28768 D_28768 (0x2a2f4 : word) ltac:(bveq).
      apply mst_refl.
    - ken.
  Qed.

  Lemma dsp_9 : forall regs, PRE regs -> index = 9%Z ->
    exists regs', msteps SEGS (mkst regs (0x2884c : word) M rom) (mkst regs' (0x28dc8 : word) M rom) /\ KEN regs' M.
  Proof.
    intros regs HE EI. unfold PRE in HE. repeat (let X := fresh "HE" in destruct HE as (X & HE)). rewrite EI in HE. eexists. split.
    - sn F_28750 D_28750. fixv (Z_to_bv 64 36) ltac:(rewrite zbv_slli by lia; reflexivity).
      sn F_28754 D_28754. sn F_28758 D_28758. fixv (Z_to_bv 64 0x119d8) ltac:(apply bv_eq; reflexivity).
      zv F_2875c D_2875c (Z_to_bv 64 72188).
      stepLD F_28760 D_28760 (Z_to_le_bytes 4 95216) (Z_to_bv 64 95216) ltac:(addr_norm; rewrite ?Z.add_0_r; unfold M, MS; jtpeel; exact JT9) ltac:(apply W2Lib.lez4; lia).
      change (v_lw (Z_to_bv 64 95216)) with (Z_to_bv 64 95216).
      zv F_28764 D_28764 (Z_to_bv 64 167368).
      stepret F_28768 D_28768 (0x28dc8 : word) ltac:(bveq).
      apply mst_refl.
    - ken.
  Qed.

  (* [comment removed for export] *)
  Lemma saved_cell : forall Mi (off : Z) bs, dwa_MInv M datad DN (s - 272) 168 Mi -> (168 <= off)%Z -> (off + 8 <= 272)%Z ->
    rdn SEGS M (Z_to_bv 64 (s - 272 + off)) 8 = Some bs -> rdn SEGS Mi (Z_to_bv 64 (s - 272 + off)) 8 = Some bs.
  Proof.
    intros Mi off bs [HI _] H1 H2 R. rewrite <- R. apply rdn_ext; [rewrite u_Z2bv by lia; cbn; lia|].
    intros x Hx. rewrite u_Z2bv in Hx by lia. cbn in Hx. apply HI; unfold disj_apart in FR; lia.
  Qed.
  Lemma epi : forall regs Mi, dwa_EX M datad DN (s - 272) 168 gpv tpv regs Mi ->
    exists regs', msteps SEGS (mkst regs (0x2a670 : word) Mi rom) (mkst regs' rav Mi rom)
      /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = rav /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\
         getr regs' 19 = s3v /\ getr regs' 20 = s4v /\ getr regs' 21 = s5v /\ getr regs' 22 = s6v /\ getr regs' 23 = s7v /\ getr regs' 24 = s8v /\ getr regs' 25 = s9v /\
         getr regs' 26 = s10v /\ getr regs' 27 = s11v /\ getr regs' 3 = gpv /\ getr regs' 4 = tpv.
  Proof.
    intros regs Mi (HIv & H2 & H3 & H4).
    assert (C : forall off v, (168 <= off)%Z -> (off + 8 <= 272)%Z -> rdn SEGS M (Z_to_bv 64 (s - 272 + off)) 8 = Some (word_to_le_bytes 8 v) ->
                rdn SEGS Mi (Z_to_bv 64 (s - 272 + off)) 8 = Some (word_to_le_bytes 8 v)) by (intros off v A B R; exact (saved_cell Mi off _ HIv A B R)).
    pose proof (C 264%Z rav ltac:(lia) ltac:(lia) ltac:(cellm)) as C264. pose proof (C 256%Z s0v ltac:(lia) ltac:(lia) ltac:(cellm)) as C256.
    pose proof (C 248%Z s1v ltac:(lia) ltac:(lia) ltac:(cellm)) as C248. pose proof (C 240%Z s2v ltac:(lia) ltac:(lia) ltac:(cellm)) as C240.
    pose proof (C 232%Z s3v ltac:(lia) ltac:(lia) ltac:(cellm)) as C232. pose proof (C 224%Z s4v ltac:(lia) ltac:(lia) ltac:(cellm)) as C224.
    pose proof (C 216%Z s5v ltac:(lia) ltac:(lia) ltac:(cellm)) as C216. pose proof (C 208%Z s6v ltac:(lia) ltac:(lia) ltac:(cellm)) as C208.
    pose proof (C 200%Z s7v ltac:(lia) ltac:(lia) ltac:(cellm)) as C200. pose proof (C 192%Z s8v ltac:(lia) ltac:(lia) ltac:(cellm)) as C192.
    pose proof (C 184%Z s9v ltac:(lia) ltac:(lia) ltac:(cellm)) as C184. pose proof (C 176%Z s10v ltac:(lia) ltac:(lia) ltac:(cellm)) as C176.
    pose proof (C 168%Z s11v ltac:(lia) ltac:(lia) ltac:(cellm)) as C168. clear C.
    eexists. split.
    - sn F_2a574 D_2a574.
      stepLD F_2a578 D_2a578 (word_to_le_bytes 8 rav) rav ltac:(rdn_addr (s - 272 + 264)%Z; exact C264) ltac:(apply bytes_le_to_Z_8).
      stepLD F_2a57c D_2a57c (word_to_le_bytes 8 s0v) s0v ltac:(rdn_addr (s - 272 + 256)%Z; exact C256) ltac:(apply bytes_le_to_Z_8).
      stepLD F_2a580 D_2a580 (word_to_le_bytes 8 s1v) s1v ltac:(rdn_addr (s - 272 + 248)%Z; exact C248) ltac:(apply bytes_le_to_Z_8).
      stepLD F_2a584 D_2a584 (word_to_le_bytes 8 s2v) s2v ltac:(rdn_addr (s - 272 + 240)%Z; exact C240) ltac:(apply bytes_le_to_Z_8).
      stepLD F_2a588 D_2a588 (word_to_le_bytes 8 s3v) s3v ltac:(rdn_addr (s - 272 + 232)%Z; exact C232) ltac:(apply bytes_le_to_Z_8).
      stepLD F_2a58c D_2a58c (word_to_le_bytes 8 s4v) s4v ltac:(rdn_addr (s - 272 + 224)%Z; exact C224) ltac:(apply bytes_le_to_Z_8).
      stepLD F_2a590 D_2a590 (word_to_le_bytes 8 s5v) s5v ltac:(rdn_addr (s - 272 + 216)%Z; exact C216) ltac:(apply bytes_le_to_Z_8).
      stepLD F_2a594 D_2a594 (word_to_le_bytes 8 s6v) s6v ltac:(rdn_addr (s - 272 + 208)%Z; exact C208) ltac:(apply bytes_le_to_Z_8).
      stepLD F_2a598 D_2a598 (word_to_le_bytes 8 s7v) s7v ltac:(rdn_addr (s - 272 + 200)%Z; exact C200) ltac:(apply bytes_le_to_Z_8).
      stepLD F_2a59c D_2a59c (word_to_le_bytes 8 s8v) s8v ltac:(rdn_addr (s - 272 + 192)%Z; exact C192) ltac:(apply bytes_le_to_Z_8).
      stepLD F_2a5a0 D_2a5a0 (word_to_le_bytes 8 s9v) s9v ltac:(rdn_addr (s - 272 + 184)%Z; exact C184) ltac:(apply bytes_le_to_Z_8).
      stepLD F_2a5a4 D_2a5a4 (word_to_le_bytes 8 s10v) s10v ltac:(rdn_addr (s - 272 + 176)%Z; exact C176) ltac:(apply bytes_le_to_Z_8).
      stepLD F_2a5a8 D_2a5a8 (word_to_le_bytes 8 s11v) s11v ltac:(rdn_addr (s - 272 + 168)%Z; exact C168) ltac:(apply bytes_le_to_Z_8).
      zv F_2a5ac D_2a5ac (Z_to_bv 64 s).
      stepret F_2a5b0 D_2a5b0 rav ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma Hsp' : (4096 <= s - 272 /\ s - 272 + 272 <= 2 ^ 63)%Z. Proof. lia. Qed.
  Lemma SOKs : store_ok SEGS M (Z_to_bv 64 SLO) (Z.to_nat (SHI - SLO)) = true. Proof. exact (store_ok_mono _ _ _ _ _ M_grows SOKs0). Qed.
  Lemma SOKd : store_ok SEGS M (Z_to_bv 64 datad) (Z.to_nat DN) = true. Proof. exact (store_ok_mono _ _ _ _ _ M_grows SOKd0). Qed.
  Lemma SOKf : store_ok SEGS M (Z_to_bv 64 (s - 272)) 168 = true.
  Proof. apply (store_ok_mono _ _ _ _ _ M_grows). eapply (store_ok_sub SEGS M0 (Z_to_bv 64 (s - 272)) _ 272); [ | exact SOKf0 | | ]; rewrite ?u_Z2bv by lia; lia. Qed.

  Definition DWA_POST (regs' : bvmap 5 word) (M' : word -> option byte) : Prop :=
    (forall x : word, ~ (datad <= u x < datad + DN)%Z -> ~ (s - 272 <= u x < s)%Z -> M' x = M0 x) /\ mem_grows M0 M' /\
    getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = rav /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\
    getr regs' 19 = s3v /\ getr regs' 20 = s4v /\ getr regs' 21 = s5v /\ getr regs' 22 = s6v /\ getr regs' 23 = s7v /\ getr regs' 24 = s8v /\ getr regs' 25 = s9v /\
    getr regs' 26 = s10v /\ getr regs' 27 = s11v /\ getr regs' 3 = gpv /\ getr regs' 4 = tpv.

  Lemma M_out : forall x : word, ~ (s - 272 <= u x < s)%Z -> M x = M0 x.
  Proof. intros x Hx. unfold M, MS. rewrite !wbytes_outside by (rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; lia). reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma fin : forall regs (pck : word),
    (exists regs', msteps SEGS (mkst regs (0x287f8 : word) M0 rom) (mkst regs' pck M rom) /\ KEN regs' M) ->
    (forall r Mi, KEN r Mi -> exists r' M', msteps SEGS (mkst r pck Mi rom) (mkst r' (0x2a670 : word) M' rom) /\ dwa_EX M datad DN (s - 272) 168 gpv tpv r' M') ->
    exists regs' M', msteps SEGS (mkst regs (0x287f8 : word) M0 rom) (mkst regs' rav M' rom) /\ DWA_POST regs' M'.
  Proof.
    intros regs pck (r1 & RUN1 & HEN) KR. destruct (KR r1 M HEN) as (r2 & M2 & RUN2 & HEX).
    destruct (epi r2 M2 HEX) as (r3 & RUN3 & FACTS). exists r3, M2.
    split; [eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 | exact RUN3]]|].
    destruct HEX as ([HI HG] & _). unfold DWA_POST. split; [| split; [eapply mem_grows_trans; [exact M_grows | exact HG] | exact FACTS]].
    intros x Hd Hf. rewrite HI by lia. apply M_out. exact Hf.
  Qed.

  Theorem dwa_run : forall regs, ENTRY regs -> getr regs 16 = Z_to_bv 64 index ->
    exists regs' M', msteps SEGS (mkst regs (0x287f8 : word) M0 rom) (mkst regs' rav M' rom) /\ DWA_POST regs' M'.
  Proof using All.
    intros regs HE H16.
    assert (CASES : (index = 0 \/ index = 1 \/ index = 2 \/ index = 3 \/ index = 4 \/ index = 5 \/ index = 6 \/ index = 7 \/ index = 8 \/ index = 9)%Z) by lia.
    pose proof H16 as H16'.
    destruct CASES as [E|[E|[E|[E|[E|[E|[E|[E|[E|E]]]]]]]]].
    - apply (fin regs (0x28868 : word)); [destruct (dsp_pre regs HE H16') as (rp & RUNp & HP); destruct (dsp_0 rp HP E) as (rq & RUNq & HQ); exists rq; split; [eapply msteps_trans; [exact RUNp | exact RUNq] | exact HQ] |]. intros r Mi HK.
      exact (V10DwaA.k0_run M rom w h wpls wpld PW datas datad (s - 272)%Z gpv tpv Hw Hh Hwpls Hwpld HPW Hsz Hsp' Hds Hdd SOKs SOKd SOKf FR Hals Hald r Mi HK).
    - apply (fin regs (0x29a14 : word)); [destruct (dsp_pre regs HE H16') as (rp & RUNp & HP); destruct (dsp_1 rp HP E) as (rq & RUNq & HQ); exists rq; split; [eapply msteps_trans; [exact RUNp | exact RUNq] | exact HQ] |]. intros r Mi HK.
      exact (V10DwaA.k1_run M rom w h wpls wpld PW datas datad (s - 272)%Z gpv tpv Hw Hh Hwpls Hwpld HPW Hsz Hsp' Hds Hdd SOKs SOKd SOKf FR Hals Hald r Mi HK).
    - apply (fin regs (0x291c0 : word)); [destruct (dsp_pre regs HE H16') as (rp & RUNp & HP); destruct (dsp_2 rp HP E) as (rq & RUNq & HQ); exists rq; split; [eapply msteps_trans; [exact RUNp | exact RUNq] | exact HQ] |]. intros r Mi HK.
      exact (V10DwaA.k2_run M rom w h wpls wpld PW datas datad (s - 272)%Z gpv tpv Hw Hh Hwpls Hwpld HPW Hsz Hsp' Hds Hdd SOKs SOKd SOKf FR Hals Hald r Mi HK).
    - apply (fin regs (0x293fc : word)); [destruct (dsp_pre regs HE H16') as (rp & RUNp & HP); destruct (dsp_3 rp HP E) as (rq & RUNq & HQ); exists rq; split; [eapply msteps_trans; [exact RUNp | exact RUNq] | exact HQ] |]. intros r Mi HK.
      exact (V10DwaA.k3_run M rom w h wpls wpld PW datas datad (s - 272)%Z gpv tpv Hw Hh Hwpls Hwpld HPW Hsz Hsp' Hds Hdd SOKs SOKd SOKf FR Hals Hald r Mi HK).
    - apply (fin regs (0x28b70 : word)); [destruct (dsp_pre regs HE H16') as (rp & RUNp & HP); destruct (dsp_4 rp HP E) as (rq & RUNq & HQ); exists rq; split; [eapply msteps_trans; [exact RUNp | exact RUNq] | exact HQ] |]. intros r Mi HK.
      exact (V10DwaB.k4_run M rom w h wpls wpld PW datas datad (s - 272)%Z gpv tpv Hw Hh Hwpls Hwpld HPW Hsz Hsp' Hds Hdd SOKs SOKd SOKf FR Hals Hald r Mi HK).
    - apply (fin regs (0x29bfc : word)); [destruct (dsp_pre regs HE H16') as (rp & RUNp & HP); destruct (dsp_5 rp HP E) as (rq & RUNq & HQ); exists rq; split; [eapply msteps_trans; [exact RUNp | exact RUNq] | exact HQ] |]. intros r Mi HK.
      exact (V10DwaB.k5_run M rom w h wpls wpld PW datas datad (s - 272)%Z gpv tpv Hw Hh Hwpls Hwpld HPW Hsz Hsp' Hds Hdd SOKs SOKd SOKf FR Hals Hald r Mi HK).
    - apply (fin regs (0x29f68 : word)); [destruct (dsp_pre regs HE H16') as (rp & RUNp & HP); destruct (dsp_6 rp HP E) as (rq & RUNq & HQ); exists rq; split; [eapply msteps_trans; [exact RUNp | exact RUNq] | exact HQ] |]. intros r Mi HK.
      exact (V10DwaC.k6_run M rom w h wpls wpld PW datas datad (s - 272)%Z gpv tpv Hw Hh Hwpls Hwpld HPW Hsz Hsp' Hds Hdd SOKs SOKd SOKf FR Hals Hald r Mi HK).
    - apply (fin regs (0x29670 : word)); [destruct (dsp_pre regs HE H16') as (rp & RUNp & HP); destruct (dsp_7 rp HP E) as (rq & RUNq & HQ); exists rq; split; [eapply msteps_trans; [exact RUNp | exact RUNq] | exact HQ] |]. intros r Mi HK.
      exact (V10DwaC.k7_run M rom w h wpls wpld PW datas datad (s - 272)%Z gpv tpv Hw Hh Hwpls Hwpld HPW Hsz Hsp' Hds Hdd SOKs SOKd SOKf FR Hals Hald r Mi HK).
    - apply (fin regs (0x2a2f4 : word)); [destruct (dsp_pre regs HE H16') as (rp & RUNp & HP); destruct (dsp_8 rp HP E) as (rq & RUNq & HQ); exists rq; split; [eapply msteps_trans; [exact RUNp | exact RUNq] | exact HQ] |]. intros r Mi HK.
      exact (V10DwaD.k8_run M rom w h wpls wpld PW datas datad (s - 272)%Z gpv tpv Hw Hh Hwpls Hwpld HPW Hsz Hsp' Hds Hdd SOKs SOKd SOKf FR Hals Hald r Mi HK).
    - apply (fin regs (0x28dc8 : word)); [destruct (dsp_pre regs HE H16') as (rp & RUNp & HP); destruct (dsp_9 rp HP E) as (rq & RUNq & HQ); exists rq; split; [eapply msteps_trans; [exact RUNp | exact RUNq] | exact HQ] |]. intros r Mi HK.
      exact (V10DwaD.k9_run M rom w h wpls wpld PW datas datad (s - 272)%Z gpv tpv Hw Hh Hwpls Hwpld HPW Hsz Hsp' Hds Hdd SOKs SOKd SOKf FR Hals Hald r Mi HK).
  Qed.
End RUN.

(* [comment removed for export] *)
Lemma jt0 : rdn SEGS (fun _ => None) (Z_to_bv 64 72152) 4 = Some (Z_to_le_bytes 4 93840). Proof. vm_refl_bv. Qed.
Lemma jt1 : rdn SEGS (fun _ => None) (Z_to_bv 64 72156) 4 = Some (Z_to_le_bytes 4 98364). Proof. vm_refl_bv. Qed.
Lemma jt2 : rdn SEGS (fun _ => None) (Z_to_bv 64 72160) 4 = Some (Z_to_le_bytes 4 96232). Proof. vm_refl_bv. Qed.
Lemma jt3 : rdn SEGS (fun _ => None) (Z_to_bv 64 72164) 4 = Some (Z_to_le_bytes 4 96804). Proof. vm_refl_bv. Qed.
Lemma jt4 : rdn SEGS (fun _ => None) (Z_to_bv 64 72168) 4 = Some (Z_to_le_bytes 4 94616). Proof. vm_refl_bv. Qed.
Lemma jt5 : rdn SEGS (fun _ => None) (Z_to_bv 64 72172) 4 = Some (Z_to_le_bytes 4 98852). Proof. vm_refl_bv. Qed.
Lemma jt6 : rdn SEGS (fun _ => None) (Z_to_bv 64 72176) 4 = Some (Z_to_le_bytes 4 99728). Proof. vm_refl_bv. Qed.
Lemma jt7 : rdn SEGS (fun _ => None) (Z_to_bv 64 72180) 4 = Some (Z_to_le_bytes 4 97432). Proof. vm_refl_bv. Qed.
Lemma jt8 : rdn SEGS (fun _ => None) (Z_to_bv 64 72184) 4 = Some (Z_to_le_bytes 4 100636). Proof. vm_refl_bv. Qed.
Lemma jt9 : rdn SEGS (fun _ => None) (Z_to_bv 64 72188) 4 = Some (Z_to_le_bytes 4 95216). Proof. vm_refl_bv. Qed.

(* [comment removed for export] *)
Lemma wpl_border : forall w, (1 <= w)%Z -> (wpl_of (w + 64) 1 = (w + 31) / 2 ^ 5 + 2)%Z.
Proof.
  intros w Hw. unfold wpl_of. change (2 ^ 5)%Z with 32%Z. replace ((w + 64) * 1 + 31)%Z with ((w + 31) + 2 * 32)%Z by lia.
  rewrite Z.div_add by lia. reflexivity.
Qed.

Section DwaW.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V10Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Theorem fhmtgen_low_1_W : fhmtgen_low_1_contract.
Proof.
  unfold fhmtgen_low_1_contract, PC_fhmtgen_low_1, DWA_STACK, dwa_rbytes.
  intros C Ar A m md regs s ds dd w h index ret S CK HW SUB H2 Hs16 Hlo Hhi H1 Hret H10 H11 H12 H13 H14 H15 H16 Hidx Hw1 Hh1 HOK Rs Rd Ls Ld Ld0 Ld00 NEsd HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img ll_ro LLU16] in *.
  pose proof HOK as (DV & Hw2 & Hh2 & Hsz).
  pose proof (wpl_border w Hw1) as EW. set (PW := ((w + 31) / 2 ^ 5)%Z) in *.
  assert (HPW1 : (1 <= PW)%Z) by (subst PW; change (2 ^ 5)%Z with 32%Z; apply Z.div_le_lower_bound; lia).
  assert (HPWu : (32 * PW <= w + 31)%Z) by (subst PW; change (2 ^ 5)%Z with 32%Z; apply Z.mul_div_le; lia).
  set (wpl := wpl_of (w + 64) 1) in *.
  assert (Hwh : (0 <= wpl * h)%Z) by (apply Z.mul_nonneg_nonneg; lia).
  set (n := (4 * (wpl * (h + 64)))%Z) in *.
  assert (En : (n = 4 * (wpl * h) + 256 * wpl)%Z) by (subst n; lia).
  assert (Hn0 : (0 < n)%Z) by lia.
  destruct (blk_range C A m md (Z_to_bv 64 ds) n CK HW Ls Hn0) as [Gs TOPs]. rewrite u_Z2bv in Gs, TOPs by lia.
  destruct (blk_range C A m md (Z_to_bv 64 dd) n CK HW Ld Hn0) as [Gd TOPd]. rewrite u_Z2bv in Gd, TOPd by lia.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  set (datas := (ds + 128 * wpl + 4)%Z) in *. set (datad := (dd + 128 * wpl + 4)%Z) in *.
  pose proof (blk_sok C A m md ds n CK HW Ls ltac:(lia) ltac:(lia) ltac:(lia)) as SKs.
  pose proof (blk_sok C A m md dd n CK HW Ld ltac:(lia) ltac:(lia) ltac:(lia)) as SKd.
  assert (SOKs0 : store_ok SEGS m (Z_to_bv 64 (datas - 24 * wpl - 4)) (Z.to_nat (datas + 4 * (wpl * h) + 20 * wpl + 4 * PW + 8 - (datas - 24 * wpl - 4))) = true).
  { eapply (store_ok_sub SEGS m (Z_to_bv 64 ds) _ (Z.to_nat n)); [ | exact SKs | | ]; rewrite ?u_Z2bv by (subst datas; lia); subst datas; lia. }
  assert (SOKd0 : store_ok SEGS m (Z_to_bv 64 datad) (Z.to_nat (4 * (wpl * h) - 4 * wpl + 4 * PW)) = true).
  { eapply (store_ok_sub SEGS m (Z_to_bv 64 dd) _ (Z.to_nat n)); [ | exact SKd | | ]; rewrite ?u_Z2bv by (subst datad; lia); subst datad; lia. }
  pose proof (W_sok_win C A m md (s - 272) 272 CK HW ltac:(lia) ltac:(cbn; lia)) as SOKf0.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Ls) as (_ & ALs & _). rewrite u_Z2bv in ALs by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Ld) as (_ & ALd & _). rewrite u_Z2bv in ALd by lia.
  assert (AL4 : forall p, (p mod 16 = 0)%Z -> ((p + 128 * wpl + 4) mod 4 = 0)%Z).
  { intros p Hp. replace (p + 128 * wpl + 4)%Z with (p + (32 * wpl + 1) * 4)%Z by lia. apply mod16_plus_mod4; [exact Hp | apply Z_mod_mult]. }
  assert (JT : forall a v, (0x10000 <= a)%Z -> (a + 4 <= 0x33000)%Z -> rdn SEGS (fun _ => None) (Z_to_bv 64 a) 4 = Some v -> rdn SEGS m (Z_to_bv 64 a) 4 = Some v).
  { intros a v A1 A2 R. rewrite <- p16_segs. rewrite (W_rdn_ro C A m md a 4 HW) by (cbn; lia). rewrite p16_segs. exact R. }
  destruct (dwa_run m al_rom w h wpl wpl PW datas datad s index ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20)
              (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 3) (getr regs 4)
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) eq_refl ltac:(lia) ltac:(lia) Hidx Hret ltac:(subst datas; lia) ltac:(subst datad; lia)
              SOKs0 SOKd0 SOKf0 ltac:(unfold disj_apart; subst datad; lia) (AL4 ds ALs) (AL4 dd ALd)
              (JT 72152%Z _ ltac:(lia) ltac:(lia) jt0) (JT 72156%Z _ ltac:(lia) ltac:(lia) jt1) (JT 72160%Z _ ltac:(lia) ltac:(lia) jt2) (JT 72164%Z _ ltac:(lia) ltac:(lia) jt3)
              (JT 72168%Z _ ltac:(lia) ltac:(lia) jt4) (JT 72172%Z _ ltac:(lia) ltac:(lia) jt5) (JT 72176%Z _ ltac:(lia) ltac:(lia) jt6) (JT 72180%Z _ ltac:(lia) ltac:(lia) jt7)
              (JT 72184%Z _ ltac:(lia) ltac:(lia) jt8) (JT 72188%Z _ ltac:(lia) ltac:(lia) jt9) regs)
    as (r1 & m1 & RUN1 & OUT1 & GR1 & Q10 & Q2 & Q1 & Q8 & Q9 & Q18 & Q19 & Q20 & Q21 & Q22 & Q23 & Q24 & Q25 & Q26 & Q27 & Q3 & Q4).
  { unfold ENTRY. repeat split; try reflexivity; assumption. }
  { exact H16. }
  replace (Z_to_bv 64 0x287f8) with (0x287f8 : word) by (apply bv_eq; reflexivity).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  assert (OUTM : forall a : word, ~ (s - 288 <= u a < s)%Z -> ~ (dd <= u a < dd + n)%Z -> m1 a = m a).
  { intros a Ha Hb. apply OUT1; subst datad; lia. }
  assert (CH : forall a, m1 a <> m a -> scratch C s a \/ (dd <= u a < dd + n)%Z).
  { intros a NE. destruct (Z_lt_ge_dec (u a) dd) as [B1|B1]; [| destruct (Z_lt_ge_dec (u a) (dd + n)) as [B2|B2]; [right; lia |]];
      (left; unfold scratch; destruct (Z_lt_ge_dec (u a) (s - 288)); [exfalso; apply NE; apply OUTM; lia|];
       destruct (Z_lt_ge_dec (u a) s); [lia|]; exfalso; apply NE; apply OUTM; lia). }
  apply HK.
  - apply (W_local C A m md m1 s CK HW Hhi); [| exact GR1].
    intros a NE. destruct (CH a NE) as [X|R]; [left; exact X | right].
    exists (Z_to_bv 64 dd), n. rewrite u_Z2bv by lia. split; [exact Ld | split; [exact Ld00 | lia]].
  - apply cs_kept_intro; csr; try reflexivity.
  - apply (POSTM_local C Ar A m md m1 s CK HW SUB). intros a NE. destruct (CH a NE) as [X|R]; [left; exact X | right].
    exists (Z_to_bv 64 dd), n. rewrite u_Z2bv by lia. split; [exact Ld | split; [exact Ld0 | lia]].
  - intros a Ha Hb. apply OUTM; assumption.
  - exact Q10.
Qed.
End DwaW.
