(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.fhmtgen_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2 GrayACELib LeptSel.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require Import V10LeptStderr V10LeptBase V10LeptUb.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require Import V10CL7a.
Import V10CL7a.V10LeptErr. Import V10CL7a.V10LeptSel_iface.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require Import V10CL8a.
Import V10CL8a.V10LeptPixHdr.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require Import V10LeptPixCreate V10LeptCmapValid V10LeptCmap2 V10LeptPixCopyA V10LeptPixCopy.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require Import V10CL9a.
Import V10CL9a.V10LeptPixDestroy. Import V10CL9a.V10LeptDwa_iface.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require Import V10LeptPixT V10LeptPixCopyT V10LeptGrayA V10LeptGrayBorder V10LeptFhmt.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require Import LeptRoom LeptRoomPC LeptRoom14 LeptRoom10.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require LiaFast.   (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= first [ solve [LiaFast.flia2] | Zify.zify; xlia zchecker ].
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section FhmtW.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V10Pins}.
Let AL_segs : al_segs = SEGS := p16_segs.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Hypothesis STRCMP : strcmp_run.
Hypothesis DWA : fhmtgen_low_1_contract.

Lemma in_s4 : forall x : reg, In x [10; 11; 12; 13]%list -> In x [1; 10; 11; 12; 13; 18]%list. Proof. cbn [In]. tauto. Qed.
Lemma in_c3 : forall x : reg, In x [1; 10; 11]%list -> In x [1; 10; 11; 12; 13; 18]%list. Proof. cbn [In]. tauto. Qed.
Lemma in_h1 : forall x : reg, In x [18]%list -> In x [1; 10; 11; 12; 13; 18]%list. Proof. cbn [In]. tauto. Qed.

(* [comment removed for export] *)
Lemma fg_search : forall (rom : word -> option byte) regs m (name j : Z),
  (0 <= j < 10)%Z -> (1 <= name)%Z -> (name + 8 < 2 ^ 64)%Z ->
  rd_str SEGS m name (hm_name j ++ [Z_to_bv 8 0]) ->
  (forall i, (0 <= i < 10)%Z -> rd_str SEGS m (A_SELNAMES + 80 * i) (hm_name i ++ [Z_to_bv 8 0])) ->
  getr regs 1 = Z_to_bv 64 0x28440 -> getr regs 10 = Z_to_bv 64 name -> getr regs 11 = Z_to_bv 64 0x34e20 ->
  getr regs 18 = Z_to_bv 64 name -> getr regs 19 = Z_to_bv 64 0x34e20 ->
  exists regs',
    msteps SEGS (mkst regs (0x32838 : word) m rom) (mkst regs' (0x285cc : word) m rom)
    /\ getr regs' 18 = Z_to_bv 64 j
    /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 18]%list) regs regs'.
Proof.
  intros rom regs m name j Hj Hn Hn64 HN HS R1 R10 R11 R18 R19.
  assert (CS : forall i, (0 <= i < 10)%Z -> cstr (hm_name i ++ [Z_to_bv 8 0])) by (intros i Hi; destruct (cstr_name i) as [X|X]; [exact X | exfalso; exact (X Hi)]).
  assert (LEN : forall i, (0 <= i < 10)%Z -> Z.of_nat (length (hm_name i ++ [Z_to_bv 8 0])) = 8%Z).
  { intros i Hi. assert (I : (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9)%Z) by lia.
    destruct I as [->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]; reflexivity. }
  assert (J : (j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 8 \/ j = 9)%Z) by lia. clear Hj.
  destruct J as [->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]].
  - (* [comment removed for export] *)
    destruct (STRCMP rom regs m name (0x34e20 + 80 * 0)%Z (hm_name 0 ++ [Z_to_bv 8 0]) (hm_name 0 ++ [Z_to_bv 8 0]) (Z_to_bv 64 0x28440) HN (HS 0%Z ltac:(lia)) (CS 0%Z ltac:(lia)) (CS 0%Z ltac:(lia))
                ltac:(lia) ltac:(rewrite LEN by lia; lia) ltac:(lia) ltac:(rewrite LEN by lia; lia) R1 ltac:(red; apply bv_eq; reflexivity) R10 R11) as (t0 & S0 & a10_0 & AG0).
    replace (Z_to_bv 64 PC_strcmp) with (0x32838 : word) in S0 by (apply bv_eq; reflexivity). replace (Z_to_bv 64 0x28440) with (0x28440 : word) in S0 by (apply bv_eq; reflexivity).
    replace (strcmp_Z (hm_name 0 ++ [Z_to_bv 8 0]) (hm_name 0 ++ [Z_to_bv 8 0])) with (0)%Z in a10_0 by (vm_compute; reflexivity).
    assert (k18_0 : getr t0 18 = Z_to_bv 64 name) by (rewrite (AG0 18) by notin_lit; exact R18).
    assert (k19_0 : getr t0 19 = Z_to_bv 64 0x34e20) by (rewrite (AG0 19) by notin_lit; exact R19).
    destruct (fg_hit_0 rom t0 m a10_0) as (rf & HITf & f18 & AGf).
    exists rf. split; [eapply msteps_trans; [exact S0 | exact HITf]|]. split; [exact f18|].
    intros x Hx. rewrite (AGf x) by (intros X; exact (Hx (in_h1 x X))). rewrite (AG0 x) by (intros X; exact (Hx (in_s4 x X))). reflexivity.
  - (* [comment removed for export] *)
    destruct (STRCMP rom regs m name (0x34e20 + 80 * 0)%Z (hm_name 1 ++ [Z_to_bv 8 0]) (hm_name 0 ++ [Z_to_bv 8 0]) (Z_to_bv 64 0x28440) HN (HS 0%Z ltac:(lia)) (CS 1%Z ltac:(lia)) (CS 0%Z ltac:(lia))
                ltac:(lia) ltac:(rewrite LEN by lia; lia) ltac:(lia) ltac:(rewrite LEN by lia; lia) R1 ltac:(red; apply bv_eq; reflexivity) R10 R11) as (t0 & S0 & a10_0 & AG0).
    replace (Z_to_bv 64 PC_strcmp) with (0x32838 : word) in S0 by (apply bv_eq; reflexivity). replace (Z_to_bv 64 0x28440) with (0x28440 : word) in S0 by (apply bv_eq; reflexivity).
    replace (strcmp_Z (hm_name 1 ++ [Z_to_bv 8 0]) (hm_name 0 ++ [Z_to_bv 8 0])) with (-4)%Z in a10_0 by (vm_compute; reflexivity).
    assert (k18_0 : getr t0 18 = Z_to_bv 64 name) by (rewrite (AG0 18) by notin_lit; exact R18).
    assert (k19_0 : getr t0 19 = Z_to_bv 64 0x34e20) by (rewrite (AG0 19) by notin_lit; exact R19).
    pose proof (fg_miss_0 rom t0 m (-4)%Z ltac:(lia) ltac:(lia) a10_0) as M0.
    destruct (fg_call_1 rom t0 m name k18_0 k19_0) as (u1 & C1 & c1_1 & c10_1 & c11_1 & AGc1).
    assert (d18_1 : getr u1 18 = Z_to_bv 64 name) by (rewrite (AGc1 18) by notin_lit; exact k18_0).
    assert (d19_1 : getr u1 19 = Z_to_bv 64 0x34e20) by (rewrite (AGc1 19) by notin_lit; exact k19_0).
    destruct (STRCMP rom u1 m name (0x34e20 + 80 * 1)%Z (hm_name 1 ++ [Z_to_bv 8 0]) (hm_name 1 ++ [Z_to_bv 8 0]) (Z_to_bv 64 0x28450) HN (HS 1%Z ltac:(lia)) (CS 1%Z ltac:(lia)) (CS 1%Z ltac:(lia))
                ltac:(lia) ltac:(rewrite LEN by lia; lia) ltac:(lia) ltac:(rewrite LEN by lia; lia) c1_1 ltac:(red; apply bv_eq; reflexivity) c10_1 c11_1) as (t1 & S1 & a10_1 & AG1).
    replace (Z_to_bv 64 PC_strcmp) with (0x32838 : word) in S1 by (apply bv_eq; reflexivity). replace (Z_to_bv 64 0x28450) with (0x28450 : word) in S1 by (apply bv_eq; reflexivity).
    replace (strcmp_Z (hm_name 1 ++ [Z_to_bv 8 0]) (hm_name 1 ++ [Z_to_bv 8 0])) with (0)%Z in a10_1 by (vm_compute; reflexivity).
    assert (k18_1 : getr t1 18 = Z_to_bv 64 name) by (rewrite (AG1 18) by notin_lit; exact d18_1).
    assert (k19_1 : getr t1 19 = Z_to_bv 64 0x34e20) by (rewrite (AG1 19) by notin_lit; exact d19_1).
    destruct (fg_hit_1 rom t1 m a10_1) as (rf & HITf & f18 & AGf).
    exists rf. split; [eapply msteps_trans; [exact S0 | eapply msteps_trans; [exact M0 | eapply msteps_trans; [exact C1 | eapply msteps_trans; [exact S1 | exact HITf]]]]|]. split; [exact f18|].
    intros x Hx. rewrite (AGf x) by (intros X; exact (Hx (in_h1 x X))). rewrite (AG1 x) by (intros X; exact (Hx (in_s4 x X))). rewrite (AGc1 x) by (intros X; exact (Hx (in_c3 x X))). rewrite (AG0 x) by (intros X; exact (Hx (in_s4 x X))). reflexivity.
  - (* [comment removed for export] *)
    destruct (STRCMP rom regs m name (0x34e20 + 80 * 0)%Z (hm_name 2 ++ [Z_to_bv 8 0]) (hm_name 0 ++ [Z_to_bv 8 0]) (Z_to_bv 64 0x28440) HN (HS 0%Z ltac:(lia)) (CS 2%Z ltac:(lia)) (CS 0%Z ltac:(lia))
                ltac:(lia) ltac:(rewrite LEN by lia; lia) ltac:(lia) ltac:(rewrite LEN by lia; lia) R1 ltac:(red; apply bv_eq; reflexivity) R10 R11) as (t0 & S0 & a10_0 & AG0).
    replace (Z_to_bv 64 PC_strcmp) with (0x32838 : word) in S0 by (apply bv_eq; reflexivity). replace (Z_to_bv 64 0x28440) with (0x28440 : word) in S0 by (apply bv_eq; reflexivity).
    replace (strcmp_Z (hm_name 2 ++ [Z_to_bv 8 0]) (hm_name 0 ++ [Z_to_bv 8 0])) with (13)%Z in a10_0 by (vm_compute; reflexivity).
    assert (k18_0 : getr t0 18 = Z_to_bv 64 name) by (rewrite (AG0 18) by notin_lit; exact R18).
    assert (k19_0 : getr t0 19 = Z_to_bv 64 0x34e20) by (rewrite (AG0 19) by notin_lit; exact R19).
    pose proof (fg_miss_0 rom t0 m (13)%Z ltac:(lia) ltac:(lia) a10_0) as M0.
    destruct (fg_call_1 rom t0 m name k18_0 k19_0) as (u1 & C1 & c1_1 & c10_1 & c11_1 & AGc1).
    assert (d18_1 : getr u1 18 = Z_to_bv 64 name) by (rewrite (AGc1 18) by notin_lit; exact k18_0).
    assert (d19_1 : getr u1 19 = Z_to_bv 64 0x34e20) by (rewrite (AGc1 19) by notin_lit; exact k19_0).
    destruct (STRCMP rom u1 m name (0x34e20 + 80 * 1)%Z (hm_name 2 ++ [Z_to_bv 8 0]) (hm_name 1 ++ [Z_to_bv 8 0]) (Z_to_bv 64 0x28450) HN (HS 1%Z ltac:(lia)) (CS 2%Z ltac:(lia)) (CS 1%Z ltac:(lia))
                ltac:(lia) ltac:(rewrite LEN by lia; lia) ltac:(lia) ltac:(rewrite LEN by lia; lia) c1_1 ltac:(red; apply bv_eq; reflexivity) c10_1 c11_1) as (t1 & S1 & a10_1 & AG1).
    replace (Z_to_bv 64 PC_strcmp) with (0x32838 : word) in S1 by (apply bv_eq; reflexivity). replace (Z_to_bv 64 0x28450) with (0x28450 : word) in S1 by (apply bv_eq; reflexivity).
    replace (strcmp_Z (hm_name 2 ++ [Z_to_bv 8 0]) (hm_name 1 ++ [Z_to_bv 8 0])) with (17)%Z in a10_1 by (vm_compute; reflexivity).
    assert (k18_1 : getr t1 18 = Z_to_bv 64 name) by (rewrite (AG1 18) by notin_lit; exact d18_1).
    assert (k19_1 : getr t1 19 = Z_to_bv 64 0x34e20) by (rewrite (AG1 19) by notin_lit; exact d19_1).
    pose proof (fg_miss_1 rom t1 m (17)%Z ltac:(lia) ltac:(lia) a10_1) as M1.
    destruct (fg_call_2 rom t1 m name k18_1 k19_1) as (u2 & C2 & c1_2 & c10_2 & c11_2 & AGc2).
    assert (d18_2 : getr u2 18 = Z_to_bv 64 name) by (rewrite (AGc2 18) by notin_lit; exact k18_1).
    assert (d19_2 : getr u2 19 = Z_to_bv 64 0x34e20) by (rewrite (AGc2 19) by notin_lit; exact k19_1).
    destruct (STRCMP rom u2 m name (0x34e20 + 80 * 2)%Z (hm_name 2 ++ [Z_to_bv 8 0]) (hm_name 2 ++ [Z_to_bv 8 0]) (Z_to_bv 64 0x28460) HN (HS 2%Z ltac:(lia)) (CS 2%Z ltac:(lia)) (CS 2%Z ltac:(lia))
                ltac:(lia) ltac:(rewrite LEN by lia; lia) ltac:(lia) ltac:(rewrite LEN by lia; lia) c1_2 ltac:(red; apply bv_eq; reflexivity) c10_2 c11_2) as (t2 & S2 & a10_2 & AG2).
    replace (Z_to_bv 64 PC_strcmp) with (0x32838 : word) in S2 by (apply bv_eq; reflexivity). replace (Z_to_bv 64 0x28460) with (0x28460 : word) in S2 by (apply bv_eq; reflexivity).
    replace (strcmp_Z (hm_name 2 ++ [Z_to_bv 8 0]) (hm_name 2 ++ [Z_to_bv 8 0])) with (0)%Z in a10_2 by (vm_compute; reflexivity).
    assert (k18_2 : getr t2 18 = Z_to_bv 64 name) by (rewrite (AG2 18) by notin_lit; exact d18_2).
    assert (k19_2 : getr t2 19 = Z_to_bv 64 0x34e20) by (rewrite (AG2 19) by notin_lit; exact d19_2).
    destruct (fg_hit_2 rom t2 m a10_2) as (rf & HITf & f18 & AGf).
    exists rf. split; [eapply msteps_trans; [exact S0 | eapply msteps_trans; [exact M0 | eapply msteps_trans; [exact C1 | eapply msteps_trans; [exact S1 | eapply msteps_trans; [exact M1 | eapply msteps_trans; [exact C2 | eapply msteps_trans; [exact S2 | exact HITf]]]]]]]|]. split; [exact f18|].
    intros x Hx. rewrite (AGf x) by (intros X; exact (Hx (in_h1 x X))). rewrite (AG2 x) by (intros X; exact (Hx (in_s4 x X))). rewrite (AGc2 x) by (intros X; exact (Hx (in_c3 x X))). rewrite (AG1 x) by (intros X; exact (Hx (in_s4 x X))). rewrite (AGc1 x) by (intros X; exact (Hx (in_c3 x X))). rewrite (AG0 x) by (intros X; exact (Hx (in_s4 x X))). reflexivity.
  - (* [comment removed for export] *)
    destruct (STRCMP rom regs m name (0x34e20 + 80 * 0)%Z (hm_name 3 ++ [Z_to_bv 8 0]) (hm_name 0 ++ [Z_to_bv 8 0]) (Z_to_bv 64 0x28440) HN (HS 0%Z ltac:(lia)) (CS 3%Z ltac:(lia)) (CS 0%Z ltac:(lia))
                ltac:(lia) ltac:(rewrite LEN by lia; lia) ltac:(lia) ltac:(rewrite LEN by lia; lia) R1 ltac:(red; apply bv_eq; reflexivity) R10 R11) as (t0 & S0 & a10_0 & AG0).
    replace (Z_to_bv 64 PC_strcmp) with (0x32838 : word) in S0 by (apply bv_eq; reflexivity). replace (Z_to_bv 64 0x28440) with (0x28440 : word) in S0 by (apply bv_eq; reflexivity).
    replace (strcmp_Z (hm_name 3 ++ [Z_to_bv 8 0]) (hm_name 0 ++ [Z_to_bv 8 0])) with (10)%Z in a10_0 by (vm_compute; reflexivity).
    assert (k18_0 : getr t0 18 = Z_to_bv 64 name) by (rewrite (AG0 18) by notin_lit; exact R18).
    assert (k19_0 : getr t0 19 = Z_to_bv 64 0x34e20) by (rewrite (AG0 19) by notin_lit; exact R19).
    pose proof (fg_miss_0 rom t0 m (10)%Z ltac:(lia) ltac:(lia) a10_0) as M0.
    destruct (fg_call_1 rom t0 m name k18_0 k19_0) as (u1 & C1 & c1_1 & c10_1 & c11_1 & AGc1).
    assert (d18_1 : getr u1 18 = Z_to_bv 64 name) by (rewrite (AGc1 18) by notin_lit; exact k18_0).
    assert (d19_1 : getr u1 19 = Z_to_bv 64 0x34e20) by (rewrite (AGc1 19) by notin_lit; exact k19_0).
    destruct (STRCMP rom u1 m name (0x34e20 + 80 * 1)%Z (hm_name 3 ++ [Z_to_bv 8 0]) (hm_name 1 ++ [Z_to_bv 8 0]) (Z_to_bv 64 0x28450) HN (HS 1%Z ltac:(lia)) (CS 3%Z ltac:(lia)) (CS 1%Z ltac:(lia))
                ltac:(lia) ltac:(rewrite LEN by lia; lia) ltac:(lia) ltac:(rewrite LEN by lia; lia) c1_1 ltac:(red; apply bv_eq; reflexivity) c10_1 c11_1) as (t1 & S1 & a10_1 & AG1).
    replace (Z_to_bv 64 PC_strcmp) with (0x32838 : word) in S1 by (apply bv_eq; reflexivity). replace (Z_to_bv 64 0x28450) with (0x28450 : word) in S1 by (apply bv_eq; reflexivity).
    replace (strcmp_Z (hm_name 3 ++ [Z_to_bv 8 0]) (hm_name 1 ++ [Z_to_bv 8 0])) with (14)%Z in a10_1 by (vm_compute; reflexivity).
    assert (k18_1 : getr t1 18 = Z_to_bv 64 name) by (rewrite (AG1 18) by notin_lit; exact d18_1).
    assert (k19_1 : getr t1 19 = Z_to_bv 64 0x34e20) by (rewrite (AG1 19) by notin_lit; exact d19_1).
    pose proof (fg_miss_1 rom t1 m (14)%Z ltac:(lia) ltac:(lia) a10_1) as M1.
    destruct (fg_call_2 rom t1 m name k18_1 k19_1) as (u2 & C2 & c1_2 & c10_2 & c11_2 & AGc2).
    assert (d18_2 : getr u2 18 = Z_to_bv 64 name) by (rewrite (AGc2 18) by notin_lit; exact k18_1).
    assert (d19_2 : getr u2 19 = Z_to_bv 64 0x34e20) by (rewrite (AGc2 19) by notin_lit; exact k19_1).
    destruct (STRCMP rom u2 m name (0x34e20 + 80 * 2)%Z (hm_name 3 ++ [Z_to_bv 8 0]) (hm_name 2 ++ [Z_to_bv 8 0]) (Z_to_bv 64 0x28460) HN (HS 2%Z ltac:(lia)) (CS 3%Z ltac:(lia)) (CS 2%Z ltac:(lia))
                ltac:(lia) ltac:(rewrite LEN by lia; lia) ltac:(lia) ltac:(rewrite LEN by lia; lia) c1_2 ltac:(red; apply bv_eq; reflexivity) c10_2 c11_2) as (t2 & S2 & a10_2 & AG2).
    replace (Z_to_bv 64 PC_strcmp) with (0x32838 : word) in S2 by (apply bv_eq; reflexivity). replace (Z_to_bv 64 0x28460) with (0x28460 : word) in S2 by (apply bv_eq; reflexivity).
    replace (strcmp_Z (hm_name 3 ++ [Z_to_bv 8 0]) (hm_name 2 ++ [Z_to_bv 8 0])) with (-3)%Z in a10_2 by (vm_compute; reflexivity).
    assert (k18_2 : getr t2 18 = Z_to_bv 64 name) by (rewrite (AG2 18) by notin_lit; exact d18_2).
    assert (k19_2 : getr t2 19 = Z_to_bv 64 0x34e20) by (rewrite (AG2 19) by notin_lit; exact d19_2).
    pose proof (fg_miss_2 rom t2 m (-3)%Z ltac:(lia) ltac:(lia) a10_2) as M2.
    destruct (fg_call_3 rom t2 m name k18_2 k19_2) as (u3 & C3 & c1_3 & c10_3 & c11_3 & AGc3).
    assert (d18_3 : getr u3 18 = Z_to_bv 64 name) by (rewrite (AGc3 18) by notin_lit; exact k18_2).
    assert (d19_3 : getr u3 19 = Z_to_bv 64 0x34e20) by (rewrite (AGc3 19) by notin_lit; exact k19_2).
    destruct (STRCMP rom u3 m name (0x34e20 + 80 * 3)%Z (hm_name 3 ++ [Z_to_bv 8 0]) (hm_name 3 ++ [Z_to_bv 8 0]) (Z_to_bv 64 0x28470) HN (HS 3%Z ltac:(lia)) (CS 3%Z ltac:(lia)) (CS 3%Z ltac:(lia))
                ltac:(lia) ltac:(rewrite LEN by lia; lia) ltac:(lia) ltac:(rewrite LEN by lia; lia) c1_3 ltac:(red; apply bv_eq; reflexivity) c10_3 c11_3) as (t3 & S3 & a10_3 & AG3).
    replace (Z_to_bv 64 PC_strcmp) with (0x32838 : word) in S3 by (apply bv_eq; reflexivity). replace (Z_to_bv 64 0x28470) with (0x28470 : word) in S3 by (apply bv_eq; reflexivity).
    replace (strcmp_Z (hm_name 3 ++ [Z_to_bv 8 0]) (hm_name 3 ++ [Z_to_bv 8 0])) with (0)%Z in a10_3 by (vm_compute; reflexivity).
    assert (k18_3 : getr t3 18 = Z_to_bv 64 name) by (rewrite (AG3 18) by notin_lit; exact d18_3).
    assert (k19_3 : getr t3 19 = Z_to_bv 64 0x34e20) by (rewrite (AG3 19) by notin_lit; exact d19_3).
    destruct (fg_hit_3 rom t3 m a10_3) as (rf & HITf & f18 & AGf).
    exists rf. split; [eapply msteps_trans; [exact S0 | eapply msteps_trans; [exact M0 | eapply msteps_trans; [exact C1 | eapply msteps_trans; [exact S1 | eapply msteps_trans; [exact M1 | eapply msteps_trans; [exact C2 | eapply msteps_trans; [exact S2 | eapply msteps_trans; [exact M2 | eapply msteps_trans; [exact C3 | eapply msteps_trans; [exact S3 | exact HITf]]]]]]]]]]|]. split; [exact f18|].
    intros x Hx. rewrite (AGf x) by (intros X; exact (Hx (in_h1 x X))). rewrite (AG3 x) by (intros X; exact (Hx (in_s4 x X))). rewrite (AGc3 x) by (intros X; exact (Hx (in_c3 x X))). rewrite (AG2 x) by (intros X; exact (Hx (in_s4 x X))). rewrite (AGc2 x) by (intros X; exact (Hx (in_c3 x X))). rewrite (AG1 x) by (intros X; exact (Hx (in_s4 x X))). rewrite (AGc1 x) by (intros X; exact (Hx (in_c3 x X))). rewrite (AG0 x) by (intros X; exact (Hx (in_s4 x X))). reflexivity.
  - (* [comment removed for export] *)
    destruct (STRCMP rom regs m name (0x34e20 + 80 * 0)%Z (hm_name 4 ++ [Z_to_bv 8 0]) (hm_name 0 ++ [Z_to_bv 8 0]) (Z_to_bv 64 0x28440) HN (HS 0%Z ltac:(lia)) (CS 4%Z ltac:(lia)) (CS 0%Z ltac:(lia))
                ltac:(lia) ltac:(rewrite LEN by lia; lia) ltac:(lia) ltac:(rewrite LEN by lia; lia) R1 ltac:(red; apply bv_eq; reflexivity) R10 R11) as (t0 & S0 & a10_0 & AG0).
    replace (Z_to_bv 64 PC_strcmp) with (0x32838 : word) in S0 by (apply bv_eq; reflexivity). replace (Z_to_bv 64 0x28440) with (0x28440 : word) in S0 by (apply bv_eq; reflexivity).
    replace (strcmp_Z (hm_name 4 ++ [Z_to_bv 8 0]) (hm_name 0 ++ [Z_to_bv 8 0])) with (4)%Z in a10_0 by (vm_compute; reflexivity).
    assert (k18_0 : getr t0 18 = Z_to_bv 64 name) by (rewrite (AG0 18) by notin_lit; exact R18).
    assert (k19_0 : getr t0 19 = Z_to_bv 64 0x34e20) by (rewrite (AG0 19) by notin_lit; exact R19).
    pose proof (fg_miss_0 rom t0 m (4)%Z ltac:(lia) ltac:(lia) a10_0) as M0.
    destruct (fg_call_1 rom t0 m name k18_0 k19_0) as (u1 & C1 & c1_1 & c10_1 & c11_1 & AGc1).
    assert (d18_1 : getr u1 18 = Z_to_bv 64 name) by (rewrite (AGc1 18) by notin_lit; exact k18_0).
    assert (d19_1 : getr u1 19 = Z_to_bv 64 0x34e20) by (rewrite (AGc1 19) by notin_lit; exact k19_0).
    destruct (STRCMP rom u1 m name (0x34e20 + 80 * 1)%Z (hm_name 4 ++ [Z_to_bv 8 0]) (hm_name 1 ++ [Z_to_bv 8 0]) (Z_to_bv 64 0x28450) HN (HS 1%Z ltac:(lia)) (CS 4%Z ltac:(lia)) (CS 1%Z ltac:(lia))
                ltac:(lia) ltac:(rewrite LEN by lia; lia) ltac:(lia) ltac:(rewrite LEN by lia; lia) c1_1 ltac:(red; apply bv_eq; reflexivity) c10_1 c11_1) as (t1 & S1 & a10_1 & AG1).
    replace (Z_to_bv 64 PC_strcmp) with (0x32838 : word) in S1 by (apply bv_eq; reflexivity). replace (Z_to_bv 64 0x28450) with (0x28450 : word) in S1 by (apply bv_eq; reflexivity).
    replace (strcmp_Z (hm_name 4 ++ [Z_to_bv 8 0]) (hm_name 1 ++ [Z_to_bv 8 0])) with (8)%Z in a10_1 by (vm_compute; reflexivity).
    assert (k18_1 : getr t1 18 = Z_to_bv 64 name) by (rewrite (AG1 18) by notin_lit; exact d18_1).
    assert (k19_1 : getr t1 19 = Z_to_bv 64 0x34e20) by (rewrite (AG1 19) by notin_lit; exact d19_1).
    pose proof (fg_miss_1 rom t1 m (8)%Z ltac:(lia) ltac:(lia) a10_1) as M1.
    destruct (fg_call_2 rom t1 m name k18_1 k19_1) as (u2 & C2 & c1_2 & c10_2 & c11_2 & AGc2).
    assert (d18_2 : getr u2 18 = Z_to_bv 64 name) by (rewrite (AGc2 18) by notin_lit; exact k18_1).
    assert (d19_2 : getr u2 19 = Z_to_bv 64 0x34e20) by (rewrite (AGc2 19) by notin_lit; exact k19_1).
    destruct (STRCMP rom u2 m name (0x34e20 + 80 * 2)%Z (hm_name 4 ++ [Z_to_bv 8 0]) (hm_name 2 ++ [Z_to_bv 8 0]) (Z_to_bv 64 0x28460) HN (HS 2%Z ltac:(lia)) (CS 4%Z ltac:(lia)) (CS 2%Z ltac:(lia))
                ltac:(lia) ltac:(rewrite LEN by lia; lia) ltac:(lia) ltac:(rewrite LEN by lia; lia) c1_2 ltac:(red; apply bv_eq; reflexivity) c10_2 c11_2) as (t2 & S2 & a10_2 & AG2).
    replace (Z_to_bv 64 PC_strcmp) with (0x32838 : word) in S2 by (apply bv_eq; reflexivity). replace (Z_to_bv 64 0x28460) with (0x28460 : word) in S2 by (apply bv_eq; reflexivity).
    replace (strcmp_Z (hm_name 4 ++ [Z_to_bv 8 0]) (hm_name 2 ++ [Z_to_bv 8 0])) with (-9)%Z in a10_2 by (vm_compute; reflexivity).
    assert (k18_2 : getr t2 18 = Z_to_bv 64 name) by (rewrite (AG2 18) by notin_lit; exact d18_2).
    assert (k19_2 : getr t2 19 = Z_to_bv 64 0x34e20) by (rewrite (AG2 19) by notin_lit; exact d19_2).
    pose proof (fg_miss_2 rom t2 m (-9)%Z ltac:(lia) ltac:(lia) a10_2) as M2.
    destruct (fg_call_3 rom t2 m name k18_2 k19_2) as (u3 & C3 & c1_3 & c10_3 & c11_3 & AGc3).
    assert (d18_3 : getr u3 18 = Z_to_bv 64 name) by (rewrite (AGc3 18) by notin_lit; exact k18_2).
    assert (d19_3 : getr u3 19 = Z_to_bv 64 0x34e20) by (rewrite (AGc3 19) by notin_lit; exact k19_2).
    destruct (STRCMP rom u3 m name (0x34e20 + 80 * 3)%Z (hm_name 4 ++ [Z_to_bv 8 0]) (hm_name 3 ++ [Z_to_bv 8 0]) (Z_to_bv 64 0x28470) HN (HS 3%Z ltac:(lia)) (CS 4%Z ltac:(lia)) (CS 3%Z ltac:(lia))
                ltac:(lia) ltac:(rewrite LEN by lia; lia) ltac:(lia) ltac:(rewrite LEN by lia; lia) c1_3 ltac:(red; apply bv_eq; reflexivity) c10_3 c11_3) as (t3 & S3 & a10_3 & AG3).
    replace (Z_to_bv 64 PC_strcmp) with (0x32838 : word) in S3 by (apply bv_eq; reflexivity). replace (Z_to_bv 64 0x28470) with (0x28470 : word) in S3 by (apply bv_eq; reflexivity).
    replace (strcmp_Z (hm_name 4 ++ [Z_to_bv 8 0]) (hm_name 3 ++ [Z_to_bv 8 0])) with (-6)%Z in a10_3 by (vm_compute; reflexivity).
    assert (k18_3 : getr t3 18 = Z_to_bv 64 name) by (rewrite (AG3 18) by notin_lit; exact d18_3).
    assert (k19_3 : getr t3 19 = Z_to_bv 64 0x34e20) by (rewrite (AG3 19) by notin_lit; exact d19_3).
    pose proof (fg_miss_3 rom t3 m (-6)%Z ltac:(lia) ltac:(lia) a10_3) as M3.
    destruct (fg_call_4 rom t3 m name k18_3 k19_3) as (u4 & C4 & c1_4 & c10_4 & c11_4 & AGc4).
    assert (d18_4 : getr u4 18 = Z_to_bv 64 name) by (rewrite (AGc4 18) by notin_lit; exact k18_3).
    assert (d19_4 : getr u4 19 = Z_to_bv 64 0x34e20) by (rewrite (AGc4 19) by notin_lit; exact k19_3).
    destruct (STRCMP rom u4 m name (0x34e20 + 80 * 4)%Z (hm_name 4 ++ [Z_to_bv 8 0]) (hm_name 4 ++ [Z_to_bv 8 0]) (Z_to_bv 64 0x28480) HN (HS 4%Z ltac:(lia)) (CS 4%Z ltac:(lia)) (CS 4%Z ltac:(lia))
                ltac:(lia) ltac:(rewrite LEN by lia; lia) ltac:(lia) ltac:(rewrite LEN by lia; lia) c1_4 ltac:(red; apply bv_eq; reflexivity) c10_4 c11_4) as (t4 & S4 & a10_4 & AG4).
    replace (Z_to_bv 64 PC_strcmp) with (0x32838 : word) in S4 by (apply bv_eq; reflexivity). replace (Z_to_bv 64 0x28480) with (0x28480 : word) in S4 by (apply bv_eq; reflexivity).
    replace (strcmp_Z (hm_name 4 ++ [Z_to_bv 8 0]) (hm_name 4 ++ [Z_to_bv 8 0])) with (0)%Z in a10_4 by (vm_compute; reflexivity).
    assert (k18_4 : getr t4 18 = Z_to_bv 64 name) by (rewrite (AG4 18) by notin_lit; exact d18_4).
    assert (k19_4 : getr t4 19 = Z_to_bv 64 0x34e20) by (rewrite (AG4 19) by notin_lit; exact d19_4).
    destruct (fg_hit_4 rom t4 m a10_4) as (rf & HITf & f18 & AGf).
    exists rf. split; [eapply msteps_trans; [exact S0 | eapply msteps_trans; [exact M0 | eapply msteps_trans; [exact C1 | eapply msteps_trans; [exact S1 | eapply msteps_trans; [exact M1 | eapply msteps_trans; [exact C2 | eapply msteps_trans; [exact S2 | eapply msteps_trans; [exact M2 | eapply msteps_trans; [exact C3 | eapply msteps_trans; [exact S3 | eapply msteps_trans; [exact M3 | eapply msteps_trans; [exact C4 | eapply msteps_trans; [exact S4 | exact HITf]]]]]]]]]]]]]|]. split; [exact f18|].
    intros x Hx. rewrite (AGf x) by (intros X; exact (Hx (in_h1 x X))). rewrite (AG4 x) by (intros X; exact (Hx (in_s4 x X))). rewrite (AGc4 x) by (intros X; exact (Hx (in_c3 x X))). rewrite (AG3 x) by (intros X; exact (Hx (in_s4 x X))). rewrite (AGc3 x) by (intros X; exact (Hx (in_c3 x X))). rewrite (AG2 x) by (intros X; exact (Hx (in_s4 x X))). rewrite (AGc2 x) by (intros X; exact (Hx (in_c3 x X))). rewrite (AG1 x) by (intros X; exact (Hx (in_s4 x X))). rewrite (AGc1 x) by (intros X; exact (Hx (in_c3 x X))). rewrite (AG0 x) by (intros X; exact (Hx (in_s4 x X))). reflexivity.
  - (* [comment removed for export] *)
    destruct (STRCMP rom regs m name (0x34e20 + 80 * 0)%Z (hm_name 5 ++ [Z_to_bv 8 0]) (hm_name 0 ++ [Z_to_bv 8 0]) (Z_to_bv 64 0x28440) HN (HS 0%Z ltac:(lia)) (CS 5%Z ltac:(lia)) (CS 0%Z ltac:(lia))
                ltac:(lia) ltac:(rewrite LEN by lia; lia) ltac:(lia) ltac:(rewrite LEN by lia; lia) R1 ltac:(red; apply bv_eq; reflexivity) R10 R11) as (t0 & S0 & a10_0 & AG0).
    replace (Z_to_bv 64 PC_strcmp) with (0x32838 : word) in S0 by (apply bv_eq; reflexivity). replace (Z_to_bv 64 0x28440) with (0x28440 : word) in S0 by (apply bv_eq; reflexivity).
    replace (strcmp_Z (hm_name 5 ++ [Z_to_bv 8 0]) (hm_name 0 ++ [Z_to_bv 8 0])) with (64)%Z in a10_0 by (vm_compute; reflexivity).
    assert (k18_0 : getr t0 18 = Z_to_bv 64 name) by (rewrite (AG0 18) by notin_lit; exact R18).
    assert (k19_0 : getr t0 19 = Z_to_bv 64 0x34e20) by (rewrite (AG0 19) by notin_lit; exact R19).
    pose proof (fg_miss_0 rom t0 m (64)%Z ltac:(lia) ltac:(lia) a10_0) as M0.
    destruct (fg_call_1 rom t0 m name k18_0 k19_0) as (u1 & C1 & c1_1 & c10_1 & c11_1 & AGc1).
    assert (d18_1 : getr u1 18 = Z_to_bv 64 name) by (rewrite (AGc1 18) by notin_lit; exact k18_0).
    assert (d19_1 : getr u1 19 = Z_to_bv 64 0x34e20) by (rewrite (AGc1 19) by notin_lit; exact k19_0).
    destruct (STRCMP rom u1 m name (0x34e20 + 80 * 1)%Z (hm_name 5 ++ [Z_to_bv 8 0]) (hm_name 1 ++ [Z_to_bv 8 0]) (Z_to_bv 64 0x28450) HN (HS 1%Z ltac:(lia)) (CS 5%Z ltac:(lia)) (CS 1%Z ltac:(lia))
                ltac:(lia) ltac:(rewrite LEN by lia; lia) ltac:(lia) ltac:(rewrite LEN by lia; lia) c1_1 ltac:(red; apply bv_eq; reflexivity) c10_1 c11_1) as (t1 & S1 & a10_1 & AG1).
    replace (Z_to_bv 64 PC_strcmp) with (0x32838 : word) in S1 by (apply bv_eq; reflexivity). replace (Z_to_bv 64 0x28450) with (0x28450 : word) in S1 by (apply bv_eq; reflexivity).
    replace (strcmp_Z (hm_name 5 ++ [Z_to_bv 8 0]) (hm_name 1 ++ [Z_to_bv 8 0])) with (64)%Z in a10_1 by (vm_compute; reflexivity).
    assert (k18_1 : getr t1 18 = Z_to_bv 64 name) by (rewrite (AG1 18) by notin_lit; exact d18_1).
    assert (k19_1 : getr t1 19 = Z_to_bv 64 0x34e20) by (rewrite (AG1 19) by notin_lit; exact d19_1).
    pose proof (fg_miss_1 rom t1 m (64)%Z ltac:(lia) ltac:(lia) a10_1) as M1.
    destruct (fg_call_2 rom t1 m name k18_1 k19_1) as (u2 & C2 & c1_2 & c10_2 & c11_2 & AGc2).
    assert (d18_2 : getr u2 18 = Z_to_bv 64 name) by (rewrite (AGc2 18) by notin_lit; exact k18_1).
    assert (d19_2 : getr u2 19 = Z_to_bv 64 0x34e20) by (rewrite (AGc2 19) by notin_lit; exact k19_1).
    destruct (STRCMP rom u2 m name (0x34e20 + 80 * 2)%Z (hm_name 5 ++ [Z_to_bv 8 0]) (hm_name 2 ++ [Z_to_bv 8 0]) (Z_to_bv 64 0x28460) HN (HS 2%Z ltac:(lia)) (CS 5%Z ltac:(lia)) (CS 2%Z ltac:(lia))
                ltac:(lia) ltac:(rewrite LEN by lia; lia) ltac:(lia) ltac:(rewrite LEN by lia; lia) c1_2 ltac:(red; apply bv_eq; reflexivity) c10_2 c11_2) as (t2 & S2 & a10_2 & AG2).
    replace (Z_to_bv 64 PC_strcmp) with (0x32838 : word) in S2 by (apply bv_eq; reflexivity). replace (Z_to_bv 64 0x28460) with (0x28460 : word) in S2 by (apply bv_eq; reflexivity).
    replace (strcmp_Z (hm_name 5 ++ [Z_to_bv 8 0]) (hm_name 2 ++ [Z_to_bv 8 0])) with (64)%Z in a10_2 by (vm_compute; reflexivity).
    assert (k18_2 : getr t2 18 = Z_to_bv 64 name) by (rewrite (AG2 18) by notin_lit; exact d18_2).
    assert (k19_2 : getr t2 19 = Z_to_bv 64 0x34e20) by (rewrite (AG2 19) by notin_lit; exact d19_2).
    pose proof (fg_miss_2 rom t2 m (64)%Z ltac:(lia) ltac:(lia) a10_2) as M2.
    destruct (fg_call_3 rom t2 m name k18_2 k19_2) as (u3 & C3 & c1_3 & c10_3 & c11_3 & AGc3).
    assert (d18_3 : getr u3 18 = Z_to_bv 64 name) by (rewrite (AGc3 18) by notin_lit; exact k18_2).
    assert (d19_3 : getr u3 19 = Z_to_bv 64 0x34e20) by (rewrite (AGc3 19) by notin_lit; exact k19_2).
    destruct (STRCMP rom u3 m name (0x34e20 + 80 * 3)%Z (hm_name 5 ++ [Z_to_bv 8 0]) (hm_name 3 ++ [Z_to_bv 8 0]) (Z_to_bv 64 0x28470) HN (HS 3%Z ltac:(lia)) (CS 5%Z ltac:(lia)) (CS 3%Z ltac:(lia))
                ltac:(lia) ltac:(rewrite LEN by lia; lia) ltac:(lia) ltac:(rewrite LEN by lia; lia) c1_3 ltac:(red; apply bv_eq; reflexivity) c10_3 c11_3) as (t3 & S3 & a10_3 & AG3).
    replace (Z_to_bv 64 PC_strcmp) with (0x32838 : word) in S3 by (apply bv_eq; reflexivity). replace (Z_to_bv 64 0x28470) with (0x28470 : word) in S3 by (apply bv_eq; reflexivity).
    replace (strcmp_Z (hm_name 5 ++ [Z_to_bv 8 0]) (hm_name 3 ++ [Z_to_bv 8 0])) with (64)%Z in a10_3 by (vm_compute; reflexivity).
    assert (k18_3 : getr t3 18 = Z_to_bv 64 name) by (rewrite (AG3 18) by notin_lit; exact d18_3).
    assert (k19_3 : getr t3 19 = Z_to_bv 64 0x34e20) by (rewrite (AG3 19) by notin_lit; exact d19_3).
    pose proof (fg_miss_3 rom t3 m (64)%Z ltac:(lia) ltac:(lia) a10_3) as M3.
    destruct (fg_call_4 rom t3 m name k18_3 k19_3) as (u4 & C4 & c1_4 & c10_4 & c11_4 & AGc4).
    assert (d18_4 : getr u4 18 = Z_to_bv 64 name) by (rewrite (AGc4 18) by notin_lit; exact k18_3).
    assert (d19_4 : getr u4 19 = Z_to_bv 64 0x34e20) by (rewrite (AGc4 19) by notin_lit; exact k19_3).
    destruct (STRCMP rom u4 m name (0x34e20 + 80 * 4)%Z (hm_name 5 ++ [Z_to_bv 8 0]) (hm_name 4 ++ [Z_to_bv 8 0]) (Z_to_bv 64 0x28480) HN (HS 4%Z ltac:(lia)) (CS 5%Z ltac:(lia)) (CS 4%Z ltac:(lia))
                ltac:(lia) ltac:(rewrite LEN by lia; lia) ltac:(lia) ltac:(rewrite LEN by lia; lia) c1_4 ltac:(red; apply bv_eq; reflexivity) c10_4 c11_4) as (t4 & S4 & a10_4 & AG4).
    replace (Z_to_bv 64 PC_strcmp) with (0x32838 : word) in S4 by (apply bv_eq; reflexivity). replace (Z_to_bv 64 0x28480) with (0x28480 : word) in S4 by (apply bv_eq; reflexivity).
    replace (strcmp_Z (hm_name 5 ++ [Z_to_bv 8 0]) (hm_name 4 ++ [Z_to_bv 8 0])) with (64)%Z in a10_4 by (vm_compute; reflexivity).
    assert (k18_4 : getr t4 18 = Z_to_bv 64 name) by (rewrite (AG4 18) by notin_lit; exact d18_4).
    assert (k19_4 : getr t4 19 = Z_to_bv 64 0x34e20) by (rewrite (AG4 19) by notin_lit; exact d19_4).
    pose proof (fg_miss_4 rom t4 m (64)%Z ltac:(lia) ltac:(lia) a10_4) as M4.
    destruct (fg_call_5 rom t4 m name k18_4 k19_4) as (u5 & C5 & c1_5 & c10_5 & c11_5 & AGc5).
    assert (d18_5 : getr u5 18 = Z_to_bv 64 name) by (rewrite (AGc5 18) by notin_lit; exact k18_4).
    assert (d19_5 : getr u5 19 = Z_to_bv 64 0x34e20) by (rewrite (AGc5 19) by notin_lit; exact k19_4).
    destruct (STRCMP rom u5 m name (0x34e20 + 80 * 5)%Z (hm_name 5 ++ [Z_to_bv 8 0]) (hm_name 5 ++ [Z_to_bv 8 0]) (Z_to_bv 64 0x28490) HN (HS 5%Z ltac:(lia)) (CS 5%Z ltac:(lia)) (CS 5%Z ltac:(lia))
                ltac:(lia) ltac:(rewrite LEN by lia; lia) ltac:(lia) ltac:(rewrite LEN by lia; lia) c1_5 ltac:(red; apply bv_eq; reflexivity) c10_5 c11_5) as (t5 & S5 & a10_5 & AG5).
    replace (Z_to_bv 64 PC_strcmp) with (0x32838 : word) in S5 by (apply bv_eq; reflexivity). replace (Z_to_bv 64 0x28490) with (0x28490 : word) in S5 by (apply bv_eq; reflexivity).
    replace (strcmp_Z (hm_name 5 ++ [Z_to_bv 8 0]) (hm_name 5 ++ [Z_to_bv 8 0])) with (0)%Z in a10_5 by (vm_compute; reflexivity).
    assert (k18_5 : getr t5 18 = Z_to_bv 64 name) by (rewrite (AG5 18) by notin_lit; exact d18_5).
    assert (k19_5 : getr t5 19 = Z_to_bv 64 0x34e20) by (rewrite (AG5 19) by notin_lit; exact d19_5).
    destruct (fg_hit_5 rom t5 m a10_5) as (rf & HITf & f18 & AGf).
    exists rf. split; [eapply msteps_trans; [exact S0 | eapply msteps_trans; [exact M0 | eapply msteps_trans; [exact C1 | eapply msteps_trans; [exact S1 | eapply msteps_trans; [exact M1 | eapply msteps_trans; [exact C2 | eapply msteps_trans; [exact S2 | eapply msteps_trans; [exact M2 | eapply msteps_trans; [exact C3 | eapply msteps_trans; [exact S3 | eapply msteps_trans; [exact M3 | eapply msteps_trans; [exact C4 | eapply msteps_trans; [exact S4 | eapply msteps_trans; [exact M4 | eapply msteps_trans; [exact C5 | eapply msteps_trans; [exact S5 | exact HITf]]]]]]]]]]]]]]]]|]. split; [exact f18|].
    intros x Hx. rewrite (AGf x) by (intros X; exact (Hx (in_h1 x X))). rewrite (AG5 x) by (intros X; exact (Hx (in_s4 x X))). rewrite (AGc5 x) by (intros X; exact (Hx (in_c3 x X))). rewrite (AG4 x) by (intros X; exact (Hx (in_s4 x X))). rewrite (AGc4 x) by (intros X; exact (Hx (in_c3 x X))). rewrite (AG3 x) by (intros X; exact (Hx (in_s4 x X))). rewrite (AGc3 x) by (intros X; exact (Hx (in_c3 x X))). rewrite (AG2 x) by (intros X; exact (Hx (in_s4 x X))). rewrite (AGc2 x) by (intros X; exact (Hx (in_c3 x X))). rewrite (AG1 x) by (intros X; exact (Hx (in_s4 x X))). rewrite (AGc1 x) by (intros X; exact (Hx (in_c3 x X))). rewrite (AG0 x) by (intros X; exact (Hx (in_s4 x X))). reflexivity.
  - (* [comment removed for export] *)
    destruct (STRCMP rom regs m name (0x34e20 + 80 * 0)%Z (hm_name 6 ++ [Z_to_bv 8 0]) (hm_name 0 ++ [Z_to_bv 8 0]) (Z_to_bv 64 0x28440) HN (HS 0%Z ltac:(lia)) (CS 6%Z ltac:(lia)) (CS 0%Z ltac:(lia))
                ltac:(lia) ltac:(rewrite LEN by lia; lia) ltac:(lia) ltac:(rewrite LEN by lia; lia) R1 ltac:(red; apply bv_eq; reflexivity) R10 R11) as (t0 & S0 & a10_0 & AG0).
    replace (Z_to_bv 64 PC_strcmp) with (0x32838 : word) in S0 by (apply bv_eq; reflexivity). replace (Z_to_bv 64 0x28440) with (0x28440 : word) in S0 by (apply bv_eq; reflexivity).
    replace (strcmp_Z (hm_name 6 ++ [Z_to_bv 8 0]) (hm_name 0 ++ [Z_to_bv 8 0])) with (66)%Z in a10_0 by (vm_compute; reflexivity).
    assert (k18_0 : getr t0 18 = Z_to_bv 64 name) by (rewrite (AG0 18) by notin_lit; exact R18).
    assert (k19_0 : getr t0 19 = Z_to_bv 64 0x34e20) by (rewrite (AG0 19) by notin_lit; exact R19).
    pose proof (fg_miss_0 rom t0 m (66)%Z ltac:(lia) ltac:(lia) a10_0) as M0.
    destruct (fg_call_1 rom t0 m name k18_0 k19_0) as (u1 & C1 & c1_1 & c10_1 & c11_1 & AGc1).
    assert (d18_1 : getr u1 18 = Z_to_bv 64 name) by (rewrite (AGc1 18) by notin_lit; exact k18_0).
    assert (d19_1 : getr u1 19 = Z_to_bv 64 0x34e20) by (rewrite (AGc1 19) by notin_lit; exact k19_0).
    destruct (STRCMP rom u1 m name (0x34e20 + 80 * 1)%Z (hm_name 6 ++ [Z_to_bv 8 0]) (hm_name 1 ++ [Z_to_bv 8 0]) (Z_to_bv 64 0x28450) HN (HS 1%Z ltac:(lia)) (CS 6%Z ltac:(lia)) (CS 1%Z ltac:(lia))
                ltac:(lia) ltac:(rewrite LEN by lia; lia) ltac:(lia) ltac:(rewrite LEN by lia; lia) c1_1 ltac:(red; apply bv_eq; reflexivity) c10_1 c11_1) as (t1 & S1 & a10_1 & AG1).
    replace (Z_to_bv 64 PC_strcmp) with (0x32838 : word) in S1 by (apply bv_eq; reflexivity). replace (Z_to_bv 64 0x28450) with (0x28450 : word) in S1 by (apply bv_eq; reflexivity).
    replace (strcmp_Z (hm_name 6 ++ [Z_to_bv 8 0]) (hm_name 1 ++ [Z_to_bv 8 0])) with (66)%Z in a10_1 by (vm_compute; reflexivity).
    assert (k18_1 : getr t1 18 = Z_to_bv 64 name) by (rewrite (AG1 18) by notin_lit; exact d18_1).
    assert (k19_1 : getr t1 19 = Z_to_bv 64 0x34e20) by (rewrite (AG1 19) by notin_lit; exact d19_1).
    pose proof (fg_miss_1 rom t1 m (66)%Z ltac:(lia) ltac:(lia) a10_1) as M1.
    destruct (fg_call_2 rom t1 m name k18_1 k19_1) as (u2 & C2 & c1_2 & c10_2 & c11_2 & AGc2).
    assert (d18_2 : getr u2 18 = Z_to_bv 64 name) by (rewrite (AGc2 18) by notin_lit; exact k18_1).
    assert (d19_2 : getr u2 19 = Z_to_bv 64 0x34e20) by (rewrite (AGc2 19) by notin_lit; exact k19_1).
    destruct (STRCMP rom u2 m name (0x34e20 + 80 * 2)%Z (hm_name 6 ++ [Z_to_bv 8 0]) (hm_name 2 ++ [Z_to_bv 8 0]) (Z_to_bv 64 0x28460) HN (HS 2%Z ltac:(lia)) (CS 6%Z ltac:(lia)) (CS 2%Z ltac:(lia))
                ltac:(lia) ltac:(rewrite LEN by lia; lia) ltac:(lia) ltac:(rewrite LEN by lia; lia) c1_2 ltac:(red; apply bv_eq; reflexivity) c10_2 c11_2) as (t2 & S2 & a10_2 & AG2).
    replace (Z_to_bv 64 PC_strcmp) with (0x32838 : word) in S2 by (apply bv_eq; reflexivity). replace (Z_to_bv 64 0x28460) with (0x28460 : word) in S2 by (apply bv_eq; reflexivity).
    replace (strcmp_Z (hm_name 6 ++ [Z_to_bv 8 0]) (hm_name 2 ++ [Z_to_bv 8 0])) with (66)%Z in a10_2 by (vm_compute; reflexivity).
    assert (k18_2 : getr t2 18 = Z_to_bv 64 name) by (rewrite (AG2 18) by notin_lit; exact d18_2).
    assert (k19_2 : getr t2 19 = Z_to_bv 64 0x34e20) by (rewrite (AG2 19) by notin_lit; exact d19_2).
    pose proof (fg_miss_2 rom t2 m (66)%Z ltac:(lia) ltac:(lia) a10_2) as M2.
    destruct (fg_call_3 rom t2 m name k18_2 k19_2) as (u3 & C3 & c1_3 & c10_3 & c11_3 & AGc3).
    assert (d18_3 : getr u3 18 = Z_to_bv 64 name) by (rewrite (AGc3 18) by notin_lit; exact k18_2).
    assert (d19_3 : getr u3 19 = Z_to_bv 64 0x34e20) by (rewrite (AGc3 19) by notin_lit; exact k19_2).
    destruct (STRCMP rom u3 m name (0x34e20 + 80 * 3)%Z (hm_name 6 ++ [Z_to_bv 8 0]) (hm_name 3 ++ [Z_to_bv 8 0]) (Z_to_bv 64 0x28470) HN (HS 3%Z ltac:(lia)) (CS 6%Z ltac:(lia)) (CS 3%Z ltac:(lia))
                ltac:(lia) ltac:(rewrite LEN by lia; lia) ltac:(lia) ltac:(rewrite LEN by lia; lia) c1_3 ltac:(red; apply bv_eq; reflexivity) c10_3 c11_3) as (t3 & S3 & a10_3 & AG3).
    replace (Z_to_bv 64 PC_strcmp) with (0x32838 : word) in S3 by (apply bv_eq; reflexivity). replace (Z_to_bv 64 0x28470) with (0x28470 : word) in S3 by (apply bv_eq; reflexivity).
    replace (strcmp_Z (hm_name 6 ++ [Z_to_bv 8 0]) (hm_name 3 ++ [Z_to_bv 8 0])) with (66)%Z in a10_3 by (vm_compute; reflexivity).
    assert (k18_3 : getr t3 18 = Z_to_bv 64 name) by (rewrite (AG3 18) by notin_lit; exact d18_3).
    assert (k19_3 : getr t3 19 = Z_to_bv 64 0x34e20) by (rewrite (AG3 19) by notin_lit; exact d19_3).
    pose proof (fg_miss_3 rom t3 m (66)%Z ltac:(lia) ltac:(lia) a10_3) as M3.
    destruct (fg_call_4 rom t3 m name k18_3 k19_3) as (u4 & C4 & c1_4 & c10_4 & c11_4 & AGc4).
    assert (d18_4 : getr u4 18 = Z_to_bv 64 name) by (rewrite (AGc4 18) by notin_lit; exact k18_3).
    assert (d19_4 : getr u4 19 = Z_to_bv 64 0x34e20) by (rewrite (AGc4 19) by notin_lit; exact k19_3).
    destruct (STRCMP rom u4 m name (0x34e20 + 80 * 4)%Z (hm_name 6 ++ [Z_to_bv 8 0]) (hm_name 4 ++ [Z_to_bv 8 0]) (Z_to_bv 64 0x28480) HN (HS 4%Z ltac:(lia)) (CS 6%Z ltac:(lia)) (CS 4%Z ltac:(lia))
                ltac:(lia) ltac:(rewrite LEN by lia; lia) ltac:(lia) ltac:(rewrite LEN by lia; lia) c1_4 ltac:(red; apply bv_eq; reflexivity) c10_4 c11_4) as (t4 & S4 & a10_4 & AG4).
    replace (Z_to_bv 64 PC_strcmp) with (0x32838 : word) in S4 by (apply bv_eq; reflexivity). replace (Z_to_bv 64 0x28480) with (0x28480 : word) in S4 by (apply bv_eq; reflexivity).
    replace (strcmp_Z (hm_name 6 ++ [Z_to_bv 8 0]) (hm_name 4 ++ [Z_to_bv 8 0])) with (66)%Z in a10_4 by (vm_compute; reflexivity).
    assert (k18_4 : getr t4 18 = Z_to_bv 64 name) by (rewrite (AG4 18) by notin_lit; exact d18_4).
    assert (k19_4 : getr t4 19 = Z_to_bv 64 0x34e20) by (rewrite (AG4 19) by notin_lit; exact d19_4).
    pose proof (fg_miss_4 rom t4 m (66)%Z ltac:(lia) ltac:(lia) a10_4) as M4.
    destruct (fg_call_5 rom t4 m name k18_4 k19_4) as (u5 & C5 & c1_5 & c10_5 & c11_5 & AGc5).
    assert (d18_5 : getr u5 18 = Z_to_bv 64 name) by (rewrite (AGc5 18) by notin_lit; exact k18_4).
    assert (d19_5 : getr u5 19 = Z_to_bv 64 0x34e20) by (rewrite (AGc5 19) by notin_lit; exact k19_4).
    destruct (STRCMP rom u5 m name (0x34e20 + 80 * 5)%Z (hm_name 6 ++ [Z_to_bv 8 0]) (hm_name 5 ++ [Z_to_bv 8 0]) (Z_to_bv 64 0x28490) HN (HS 5%Z ltac:(lia)) (CS 6%Z ltac:(lia)) (CS 5%Z ltac:(lia))
                ltac:(lia) ltac:(rewrite LEN by lia; lia) ltac:(lia) ltac:(rewrite LEN by lia; lia) c1_5 ltac:(red; apply bv_eq; reflexivity) c10_5 c11_5) as (t5 & S5 & a10_5 & AG5).
    replace (Z_to_bv 64 PC_strcmp) with (0x32838 : word) in S5 by (apply bv_eq; reflexivity). replace (Z_to_bv 64 0x28490) with (0x28490 : word) in S5 by (apply bv_eq; reflexivity).
    replace (strcmp_Z (hm_name 6 ++ [Z_to_bv 8 0]) (hm_name 5 ++ [Z_to_bv 8 0])) with (2)%Z in a10_5 by (vm_compute; reflexivity).
    assert (k18_5 : getr t5 18 = Z_to_bv 64 name) by (rewrite (AG5 18) by notin_lit; exact d18_5).
    assert (k19_5 : getr t5 19 = Z_to_bv 64 0x34e20) by (rewrite (AG5 19) by notin_lit; exact d19_5).
    pose proof (fg_miss_5 rom t5 m (2)%Z ltac:(lia) ltac:(lia) a10_5) as M5.
    destruct (fg_call_6 rom t5 m name k18_5 k19_5) as (u6 & C6 & c1_6 & c10_6 & c11_6 & AGc6).
    assert (d18_6 : getr u6 18 = Z_to_bv 64 name) by (rewrite (AGc6 18) by notin_lit; exact k18_5).
    assert (d19_6 : getr u6 19 = Z_to_bv 64 0x34e20) by (rewrite (AGc6 19) by notin_lit; exact k19_5).
    destruct (STRCMP rom u6 m name (0x34e20 + 80 * 6)%Z (hm_name 6 ++ [Z_to_bv 8 0]) (hm_name 6 ++ [Z_to_bv 8 0]) (Z_to_bv 64 0x284a0) HN (HS 6%Z ltac:(lia)) (CS 6%Z ltac:(lia)) (CS 6%Z ltac:(lia))
                ltac:(lia) ltac:(rewrite LEN by lia; lia) ltac:(lia) ltac:(rewrite LEN by lia; lia) c1_6 ltac:(red; apply bv_eq; reflexivity) c10_6 c11_6) as (t6 & S6 & a10_6 & AG6).
    replace (Z_to_bv 64 PC_strcmp) with (0x32838 : word) in S6 by (apply bv_eq; reflexivity). replace (Z_to_bv 64 0x284a0) with (0x284a0 : word) in S6 by (apply bv_eq; reflexivity).
    replace (strcmp_Z (hm_name 6 ++ [Z_to_bv 8 0]) (hm_name 6 ++ [Z_to_bv 8 0])) with (0)%Z in a10_6 by (vm_compute; reflexivity).
    assert (k18_6 : getr t6 18 = Z_to_bv 64 name) by (rewrite (AG6 18) by notin_lit; exact d18_6).
    assert (k19_6 : getr t6 19 = Z_to_bv 64 0x34e20) by (rewrite (AG6 19) by notin_lit; exact d19_6).
    destruct (fg_hit_6 rom t6 m a10_6) as (rf & HITf & f18 & AGf).
    exists rf. split; [eapply msteps_trans; [exact S0 | eapply msteps_trans; [exact M0 | eapply msteps_trans; [exact C1 | eapply msteps_trans; [exact S1 | eapply msteps_trans; [exact M1 | eapply msteps_trans; [exact C2 | eapply msteps_trans; [exact S2 | eapply msteps_trans; [exact M2 | eapply msteps_trans; [exact C3 | eapply msteps_trans; [exact S3 | eapply msteps_trans; [exact M3 | eapply msteps_trans; [exact C4 | eapply msteps_trans; [exact S4 | eapply msteps_trans; [exact M4 | eapply msteps_trans; [exact C5 | eapply msteps_trans; [exact S5 | eapply msteps_trans; [exact M5 | eapply msteps_trans; [exact C6 | eapply msteps_trans; [exact S6 | exact HITf]]]]]]]]]]]]]]]]]]]|]. split; [exact f18|].
    intros x Hx. rewrite (AGf x) by (intros X; exact (Hx (in_h1 x X))). rewrite (AG6 x) by (intros X; exact (Hx (in_s4 x X))). rewrite (AGc6 x) by (intros X; exact (Hx (in_c3 x X))). rewrite (AG5 x) by (intros X; exact (Hx (in_s4 x X))). rewrite (AGc5 x) by (intros X; exact (Hx (in_c3 x X))). rewrite (AG4 x) by (intros X; exact (Hx (in_s4 x X))). rewrite (AGc4 x) by (intros X; exact (Hx (in_c3 x X))). rewrite (AG3 x) by (intros X; exact (Hx (in_s4 x X))). rewrite (AGc3 x) by (intros X; exact (Hx (in_c3 x X))). rewrite (AG2 x) by (intros X; exact (Hx (in_s4 x X))). rewrite (AGc2 x) by (intros X; exact (Hx (in_c3 x X))). rewrite (AG1 x) by (intros X; exact (Hx (in_s4 x X))). rewrite (AGc1 x) by (intros X; exact (Hx (in_c3 x X))). rewrite (AG0 x) by (intros X; exact (Hx (in_s4 x X))). reflexivity.
  - (* [comment removed for export] *)
    destruct (STRCMP rom regs m name (0x34e20 + 80 * 0)%Z (hm_name 7 ++ [Z_to_bv 8 0]) (hm_name 0 ++ [Z_to_bv 8 0]) (Z_to_bv 64 0x28440) HN (HS 0%Z ltac:(lia)) (CS 7%Z ltac:(lia)) (CS 0%Z ltac:(lia))
                ltac:(lia) ltac:(rewrite LEN by lia; lia) ltac:(lia) ltac:(rewrite LEN by lia; lia) R1 ltac:(red; apply bv_eq; reflexivity) R10 R11) as (t0 & S0 & a10_0 & AG0).
    replace (Z_to_bv 64 PC_strcmp) with (0x32838 : word) in S0 by (apply bv_eq; reflexivity). replace (Z_to_bv 64 0x28440) with (0x28440 : word) in S0 by (apply bv_eq; reflexivity).
    replace (strcmp_Z (hm_name 7 ++ [Z_to_bv 8 0]) (hm_name 0 ++ [Z_to_bv 8 0])) with (66)%Z in a10_0 by (vm_compute; reflexivity).
    assert (k18_0 : getr t0 18 = Z_to_bv 64 name) by (rewrite (AG0 18) by notin_lit; exact R18).
    assert (k19_0 : getr t0 19 = Z_to_bv 64 0x34e20) by (rewrite (AG0 19) by notin_lit; exact R19).
    pose proof (fg_miss_0 rom t0 m (66)%Z ltac:(lia) ltac:(lia) a10_0) as M0.
    destruct (fg_call_1 rom t0 m name k18_0 k19_0) as (u1 & C1 & c1_1 & c10_1 & c11_1 & AGc1).
    assert (d18_1 : getr u1 18 = Z_to_bv 64 name) by (rewrite (AGc1 18) by notin_lit; exact k18_0).
    assert (d19_1 : getr u1 19 = Z_to_bv 64 0x34e20) by (rewrite (AGc1 19) by notin_lit; exact k19_0).
    destruct (STRCMP rom u1 m name (0x34e20 + 80 * 1)%Z (hm_name 7 ++ [Z_to_bv 8 0]) (hm_name 1 ++ [Z_to_bv 8 0]) (Z_to_bv 64 0x28450) HN (HS 1%Z ltac:(lia)) (CS 7%Z ltac:(lia)) (CS 1%Z ltac:(lia))
                ltac:(lia) ltac:(rewrite LEN by lia; lia) ltac:(lia) ltac:(rewrite LEN by lia; lia) c1_1 ltac:(red; apply bv_eq; reflexivity) c10_1 c11_1) as (t1 & S1 & a10_1 & AG1).
    replace (Z_to_bv 64 PC_strcmp) with (0x32838 : word) in S1 by (apply bv_eq; reflexivity). replace (Z_to_bv 64 0x28450) with (0x28450 : word) in S1 by (apply bv_eq; reflexivity).
    replace (strcmp_Z (hm_name 7 ++ [Z_to_bv 8 0]) (hm_name 1 ++ [Z_to_bv 8 0])) with (66)%Z in a10_1 by (vm_compute; reflexivity).
    assert (k18_1 : getr t1 18 = Z_to_bv 64 name) by (rewrite (AG1 18) by notin_lit; exact d18_1).
    assert (k19_1 : getr t1 19 = Z_to_bv 64 0x34e20) by (rewrite (AG1 19) by notin_lit; exact d19_1).
    pose proof (fg_miss_1 rom t1 m (66)%Z ltac:(lia) ltac:(lia) a10_1) as M1.
    destruct (fg_call_2 rom t1 m name k18_1 k19_1) as (u2 & C2 & c1_2 & c10_2 & c11_2 & AGc2).
    assert (d18_2 : getr u2 18 = Z_to_bv 64 name) by (rewrite (AGc2 18) by notin_lit; exact k18_1).
    assert (d19_2 : getr u2 19 = Z_to_bv 64 0x34e20) by (rewrite (AGc2 19) by notin_lit; exact k19_1).
    destruct (STRCMP rom u2 m name (0x34e20 + 80 * 2)%Z (hm_name 7 ++ [Z_to_bv 8 0]) (hm_name 2 ++ [Z_to_bv 8 0]) (Z_to_bv 64 0x28460) HN (HS 2%Z ltac:(lia)) (CS 7%Z ltac:(lia)) (CS 2%Z ltac:(lia))
                ltac:(lia) ltac:(rewrite LEN by lia; lia) ltac:(lia) ltac:(rewrite LEN by lia; lia) c1_2 ltac:(red; apply bv_eq; reflexivity) c10_2 c11_2) as (t2 & S2 & a10_2 & AG2).
    replace (Z_to_bv 64 PC_strcmp) with (0x32838 : word) in S2 by (apply bv_eq; reflexivity). replace (Z_to_bv 64 0x28460) with (0x28460 : word) in S2 by (apply bv_eq; reflexivity).
    replace (strcmp_Z (hm_name 7 ++ [Z_to_bv 8 0]) (hm_name 2 ++ [Z_to_bv 8 0])) with (66)%Z in a10_2 by (vm_compute; reflexivity).
    assert (k18_2 : getr t2 18 = Z_to_bv 64 name) by (rewrite (AG2 18) by notin_lit; exact d18_2).
    assert (k19_2 : getr t2 19 = Z_to_bv 64 0x34e20) by (rewrite (AG2 19) by notin_lit; exact d19_2).
    pose proof (fg_miss_2 rom t2 m (66)%Z ltac:(lia) ltac:(lia) a10_2) as M2.
    destruct (fg_call_3 rom t2 m name k18_2 k19_2) as (u3 & C3 & c1_3 & c10_3 & c11_3 & AGc3).
    assert (d18_3 : getr u3 18 = Z_to_bv 64 name) by (rewrite (AGc3 18) by notin_lit; exact k18_2).
    assert (d19_3 : getr u3 19 = Z_to_bv 64 0x34e20) by (rewrite (AGc3 19) by notin_lit; exact k19_2).
    destruct (STRCMP rom u3 m name (0x34e20 + 80 * 3)%Z (hm_name 7 ++ [Z_to_bv 8 0]) (hm_name 3 ++ [Z_to_bv 8 0]) (Z_to_bv 64 0x28470) HN (HS 3%Z ltac:(lia)) (CS 7%Z ltac:(lia)) (CS 3%Z ltac:(lia))
                ltac:(lia) ltac:(rewrite LEN by lia; lia) ltac:(lia) ltac:(rewrite LEN by lia; lia) c1_3 ltac:(red; apply bv_eq; reflexivity) c10_3 c11_3) as (t3 & S3 & a10_3 & AG3).
    replace (Z_to_bv 64 PC_strcmp) with (0x32838 : word) in S3 by (apply bv_eq; reflexivity). replace (Z_to_bv 64 0x28470) with (0x28470 : word) in S3 by (apply bv_eq; reflexivity).
    replace (strcmp_Z (hm_name 7 ++ [Z_to_bv 8 0]) (hm_name 3 ++ [Z_to_bv 8 0])) with (66)%Z in a10_3 by (vm_compute; reflexivity).
    assert (k18_3 : getr t3 18 = Z_to_bv 64 name) by (rewrite (AG3 18) by notin_lit; exact d18_3).
    assert (k19_3 : getr t3 19 = Z_to_bv 64 0x34e20) by (rewrite (AG3 19) by notin_lit; exact d19_3).
    pose proof (fg_miss_3 rom t3 m (66)%Z ltac:(lia) ltac:(lia) a10_3) as M3.
    destruct (fg_call_4 rom t3 m name k18_3 k19_3) as (u4 & C4 & c1_4 & c10_4 & c11_4 & AGc4).
    assert (d18_4 : getr u4 18 = Z_to_bv 64 name) by (rewrite (AGc4 18) by notin_lit; exact k18_3).
    assert (d19_4 : getr u4 19 = Z_to_bv 64 0x34e20) by (rewrite (AGc4 19) by notin_lit; exact k19_3).
    destruct (STRCMP rom u4 m name (0x34e20 + 80 * 4)%Z (hm_name 7 ++ [Z_to_bv 8 0]) (hm_name 4 ++ [Z_to_bv 8 0]) (Z_to_bv 64 0x28480) HN (HS 4%Z ltac:(lia)) (CS 7%Z ltac:(lia)) (CS 4%Z ltac:(lia))
                ltac:(lia) ltac:(rewrite LEN by lia; lia) ltac:(lia) ltac:(rewrite LEN by lia; lia) c1_4 ltac:(red; apply bv_eq; reflexivity) c10_4 c11_4) as (t4 & S4 & a10_4 & AG4).
    replace (Z_to_bv 64 PC_strcmp) with (0x32838 : word) in S4 by (apply bv_eq; reflexivity). replace (Z_to_bv 64 0x28480) with (0x28480 : word) in S4 by (apply bv_eq; reflexivity).
    replace (strcmp_Z (hm_name 7 ++ [Z_to_bv 8 0]) (hm_name 4 ++ [Z_to_bv 8 0])) with (66)%Z in a10_4 by (vm_compute; reflexivity).
    assert (k18_4 : getr t4 18 = Z_to_bv 64 name) by (rewrite (AG4 18) by notin_lit; exact d18_4).
    assert (k19_4 : getr t4 19 = Z_to_bv 64 0x34e20) by (rewrite (AG4 19) by notin_lit; exact d19_4).
    pose proof (fg_miss_4 rom t4 m (66)%Z ltac:(lia) ltac:(lia) a10_4) as M4.
    destruct (fg_call_5 rom t4 m name k18_4 k19_4) as (u5 & C5 & c1_5 & c10_5 & c11_5 & AGc5).
    assert (d18_5 : getr u5 18 = Z_to_bv 64 name) by (rewrite (AGc5 18) by notin_lit; exact k18_4).
    assert (d19_5 : getr u5 19 = Z_to_bv 64 0x34e20) by (rewrite (AGc5 19) by notin_lit; exact k19_4).
    destruct (STRCMP rom u5 m name (0x34e20 + 80 * 5)%Z (hm_name 7 ++ [Z_to_bv 8 0]) (hm_name 5 ++ [Z_to_bv 8 0]) (Z_to_bv 64 0x28490) HN (HS 5%Z ltac:(lia)) (CS 7%Z ltac:(lia)) (CS 5%Z ltac:(lia))
                ltac:(lia) ltac:(rewrite LEN by lia; lia) ltac:(lia) ltac:(rewrite LEN by lia; lia) c1_5 ltac:(red; apply bv_eq; reflexivity) c10_5 c11_5) as (t5 & S5 & a10_5 & AG5).
    replace (Z_to_bv 64 PC_strcmp) with (0x32838 : word) in S5 by (apply bv_eq; reflexivity). replace (Z_to_bv 64 0x28490) with (0x28490 : word) in S5 by (apply bv_eq; reflexivity).
    replace (strcmp_Z (hm_name 7 ++ [Z_to_bv 8 0]) (hm_name 5 ++ [Z_to_bv 8 0])) with (2)%Z in a10_5 by (vm_compute; reflexivity).
    assert (k18_5 : getr t5 18 = Z_to_bv 64 name) by (rewrite (AG5 18) by notin_lit; exact d18_5).
    assert (k19_5 : getr t5 19 = Z_to_bv 64 0x34e20) by (rewrite (AG5 19) by notin_lit; exact d19_5).
    pose proof (fg_miss_5 rom t5 m (2)%Z ltac:(lia) ltac:(lia) a10_5) as M5.
    destruct (fg_call_6 rom t5 m name k18_5 k19_5) as (u6 & C6 & c1_6 & c10_6 & c11_6 & AGc6).
    assert (d18_6 : getr u6 18 = Z_to_bv 64 name) by (rewrite (AGc6 18) by notin_lit; exact k18_5).
    assert (d19_6 : getr u6 19 = Z_to_bv 64 0x34e20) by (rewrite (AGc6 19) by notin_lit; exact k19_5).
    destruct (STRCMP rom u6 m name (0x34e20 + 80 * 6)%Z (hm_name 7 ++ [Z_to_bv 8 0]) (hm_name 6 ++ [Z_to_bv 8 0]) (Z_to_bv 64 0x284a0) HN (HS 6%Z ltac:(lia)) (CS 7%Z ltac:(lia)) (CS 6%Z ltac:(lia))
                ltac:(lia) ltac:(rewrite LEN by lia; lia) ltac:(lia) ltac:(rewrite LEN by lia; lia) c1_6 ltac:(red; apply bv_eq; reflexivity) c10_6 c11_6) as (t6 & S6 & a10_6 & AG6).
    replace (Z_to_bv 64 PC_strcmp) with (0x32838 : word) in S6 by (apply bv_eq; reflexivity). replace (Z_to_bv 64 0x284a0) with (0x284a0 : word) in S6 by (apply bv_eq; reflexivity).
    replace (strcmp_Z (hm_name 7 ++ [Z_to_bv 8 0]) (hm_name 6 ++ [Z_to_bv 8 0])) with (6)%Z in a10_6 by (vm_compute; reflexivity).
    assert (k18_6 : getr t6 18 = Z_to_bv 64 name) by (rewrite (AG6 18) by notin_lit; exact d18_6).
    assert (k19_6 : getr t6 19 = Z_to_bv 64 0x34e20) by (rewrite (AG6 19) by notin_lit; exact d19_6).
    pose proof (fg_miss_6 rom t6 m (6)%Z ltac:(lia) ltac:(lia) a10_6) as M6.
    destruct (fg_call_7 rom t6 m name k18_6 k19_6) as (u7 & C7 & c1_7 & c10_7 & c11_7 & AGc7).
    assert (d18_7 : getr u7 18 = Z_to_bv 64 name) by (rewrite (AGc7 18) by notin_lit; exact k18_6).
    assert (d19_7 : getr u7 19 = Z_to_bv 64 0x34e20) by (rewrite (AGc7 19) by notin_lit; exact k19_6).
    destruct (STRCMP rom u7 m name (0x34e20 + 80 * 7)%Z (hm_name 7 ++ [Z_to_bv 8 0]) (hm_name 7 ++ [Z_to_bv 8 0]) (Z_to_bv 64 0x284b0) HN (HS 7%Z ltac:(lia)) (CS 7%Z ltac:(lia)) (CS 7%Z ltac:(lia))
                ltac:(lia) ltac:(rewrite LEN by lia; lia) ltac:(lia) ltac:(rewrite LEN by lia; lia) c1_7 ltac:(red; apply bv_eq; reflexivity) c10_7 c11_7) as (t7 & S7 & a10_7 & AG7).
    replace (Z_to_bv 64 PC_strcmp) with (0x32838 : word) in S7 by (apply bv_eq; reflexivity). replace (Z_to_bv 64 0x284b0) with (0x284b0 : word) in S7 by (apply bv_eq; reflexivity).
    replace (strcmp_Z (hm_name 7 ++ [Z_to_bv 8 0]) (hm_name 7 ++ [Z_to_bv 8 0])) with (0)%Z in a10_7 by (vm_compute; reflexivity).
    assert (k18_7 : getr t7 18 = Z_to_bv 64 name) by (rewrite (AG7 18) by notin_lit; exact d18_7).
    assert (k19_7 : getr t7 19 = Z_to_bv 64 0x34e20) by (rewrite (AG7 19) by notin_lit; exact d19_7).
    destruct (fg_hit_7 rom t7 m a10_7) as (rf & HITf & f18 & AGf).
    exists rf. split; [eapply msteps_trans; [exact S0 | eapply msteps_trans; [exact M0 | eapply msteps_trans; [exact C1 | eapply msteps_trans; [exact S1 | eapply msteps_trans; [exact M1 | eapply msteps_trans; [exact C2 | eapply msteps_trans; [exact S2 | eapply msteps_trans; [exact M2 | eapply msteps_trans; [exact C3 | eapply msteps_trans; [exact S3 | eapply msteps_trans; [exact M3 | eapply msteps_trans; [exact C4 | eapply msteps_trans; [exact S4 | eapply msteps_trans; [exact M4 | eapply msteps_trans; [exact C5 | eapply msteps_trans; [exact S5 | eapply msteps_trans; [exact M5 | eapply msteps_trans; [exact C6 | eapply msteps_trans; [exact S6 | eapply msteps_trans; [exact M6 | eapply msteps_trans; [exact C7 | eapply msteps_trans; [exact S7 | exact HITf]]]]]]]]]]]]]]]]]]]]]]|]. split; [exact f18|].
    intros x Hx. rewrite (AGf x) by (intros X; exact (Hx (in_h1 x X))). rewrite (AG7 x) by (intros X; exact (Hx (in_s4 x X))). rewrite (AGc7 x) by (intros X; exact (Hx (in_c3 x X))). rewrite (AG6 x) by (intros X; exact (Hx (in_s4 x X))). rewrite (AGc6 x) by (intros X; exact (Hx (in_c3 x X))). rewrite (AG5 x) by (intros X; exact (Hx (in_s4 x X))). rewrite (AGc5 x) by (intros X; exact (Hx (in_c3 x X))). rewrite (AG4 x) by (intros X; exact (Hx (in_s4 x X))). rewrite (AGc4 x) by (intros X; exact (Hx (in_c3 x X))). rewrite (AG3 x) by (intros X; exact (Hx (in_s4 x X))). rewrite (AGc3 x) by (intros X; exact (Hx (in_c3 x X))). rewrite (AG2 x) by (intros X; exact (Hx (in_s4 x X))). rewrite (AGc2 x) by (intros X; exact (Hx (in_c3 x X))). rewrite (AG1 x) by (intros X; exact (Hx (in_s4 x X))). rewrite (AGc1 x) by (intros X; exact (Hx (in_c3 x X))). rewrite (AG0 x) by (intros X; exact (Hx (in_s4 x X))). reflexivity.
  - (* [comment removed for export] *)
    destruct (STRCMP rom regs m name (0x34e20 + 80 * 0)%Z (hm_name 8 ++ [Z_to_bv 8 0]) (hm_name 0 ++ [Z_to_bv 8 0]) (Z_to_bv 64 0x28440) HN (HS 0%Z ltac:(lia)) (CS 8%Z ltac:(lia)) (CS 0%Z ltac:(lia))
                ltac:(lia) ltac:(rewrite LEN by lia; lia) ltac:(lia) ltac:(rewrite LEN by lia; lia) R1 ltac:(red; apply bv_eq; reflexivity) R10 R11) as (t0 & S0 & a10_0 & AG0).
    replace (Z_to_bv 64 PC_strcmp) with (0x32838 : word) in S0 by (apply bv_eq; reflexivity). replace (Z_to_bv 64 0x28440) with (0x28440 : word) in S0 by (apply bv_eq; reflexivity).
    replace (strcmp_Z (hm_name 8 ++ [Z_to_bv 8 0]) (hm_name 0 ++ [Z_to_bv 8 0])) with (57)%Z in a10_0 by (vm_compute; reflexivity).
    assert (k18_0 : getr t0 18 = Z_to_bv 64 name) by (rewrite (AG0 18) by notin_lit; exact R18).
    assert (k19_0 : getr t0 19 = Z_to_bv 64 0x34e20) by (rewrite (AG0 19) by notin_lit; exact R19).
    pose proof (fg_miss_0 rom t0 m (57)%Z ltac:(lia) ltac:(lia) a10_0) as M0.
    destruct (fg_call_1 rom t0 m name k18_0 k19_0) as (u1 & C1 & c1_1 & c10_1 & c11_1 & AGc1).
    assert (d18_1 : getr u1 18 = Z_to_bv 64 name) by (rewrite (AGc1 18) by notin_lit; exact k18_0).
    assert (d19_1 : getr u1 19 = Z_to_bv 64 0x34e20) by (rewrite (AGc1 19) by notin_lit; exact k19_0).
    destruct (STRCMP rom u1 m name (0x34e20 + 80 * 1)%Z (hm_name 8 ++ [Z_to_bv 8 0]) (hm_name 1 ++ [Z_to_bv 8 0]) (Z_to_bv 64 0x28450) HN (HS 1%Z ltac:(lia)) (CS 8%Z ltac:(lia)) (CS 1%Z ltac:(lia))
                ltac:(lia) ltac:(rewrite LEN by lia; lia) ltac:(lia) ltac:(rewrite LEN by lia; lia) c1_1 ltac:(red; apply bv_eq; reflexivity) c10_1 c11_1) as (t1 & S1 & a10_1 & AG1).
    replace (Z_to_bv 64 PC_strcmp) with (0x32838 : word) in S1 by (apply bv_eq; reflexivity). replace (Z_to_bv 64 0x28450) with (0x28450 : word) in S1 by (apply bv_eq; reflexivity).
    replace (strcmp_Z (hm_name 8 ++ [Z_to_bv 8 0]) (hm_name 1 ++ [Z_to_bv 8 0])) with (57)%Z in a10_1 by (vm_compute; reflexivity).
    assert (k18_1 : getr t1 18 = Z_to_bv 64 name) by (rewrite (AG1 18) by notin_lit; exact d18_1).
    assert (k19_1 : getr t1 19 = Z_to_bv 64 0x34e20) by (rewrite (AG1 19) by notin_lit; exact d19_1).
    pose proof (fg_miss_1 rom t1 m (57)%Z ltac:(lia) ltac:(lia) a10_1) as M1.
    destruct (fg_call_2 rom t1 m name k18_1 k19_1) as (u2 & C2 & c1_2 & c10_2 & c11_2 & AGc2).
    assert (d18_2 : getr u2 18 = Z_to_bv 64 name) by (rewrite (AGc2 18) by notin_lit; exact k18_1).
    assert (d19_2 : getr u2 19 = Z_to_bv 64 0x34e20) by (rewrite (AGc2 19) by notin_lit; exact k19_1).
    destruct (STRCMP rom u2 m name (0x34e20 + 80 * 2)%Z (hm_name 8 ++ [Z_to_bv 8 0]) (hm_name 2 ++ [Z_to_bv 8 0]) (Z_to_bv 64 0x28460) HN (HS 2%Z ltac:(lia)) (CS 8%Z ltac:(lia)) (CS 2%Z ltac:(lia))
                ltac:(lia) ltac:(rewrite LEN by lia; lia) ltac:(lia) ltac:(rewrite LEN by lia; lia) c1_2 ltac:(red; apply bv_eq; reflexivity) c10_2 c11_2) as (t2 & S2 & a10_2 & AG2).
    replace (Z_to_bv 64 PC_strcmp) with (0x32838 : word) in S2 by (apply bv_eq; reflexivity). replace (Z_to_bv 64 0x28460) with (0x28460 : word) in S2 by (apply bv_eq; reflexivity).
    replace (strcmp_Z (hm_name 8 ++ [Z_to_bv 8 0]) (hm_name 2 ++ [Z_to_bv 8 0])) with (57)%Z in a10_2 by (vm_compute; reflexivity).
    assert (k18_2 : getr t2 18 = Z_to_bv 64 name) by (rewrite (AG2 18) by notin_lit; exact d18_2).
    assert (k19_2 : getr t2 19 = Z_to_bv 64 0x34e20) by (rewrite (AG2 19) by notin_lit; exact d19_2).
    pose proof (fg_miss_2 rom t2 m (57)%Z ltac:(lia) ltac:(lia) a10_2) as M2.
    destruct (fg_call_3 rom t2 m name k18_2 k19_2) as (u3 & C3 & c1_3 & c10_3 & c11_3 & AGc3).
    assert (d18_3 : getr u3 18 = Z_to_bv 64 name) by (rewrite (AGc3 18) by notin_lit; exact k18_2).
    assert (d19_3 : getr u3 19 = Z_to_bv 64 0x34e20) by (rewrite (AGc3 19) by notin_lit; exact k19_2).
    destruct (STRCMP rom u3 m name (0x34e20 + 80 * 3)%Z (hm_name 8 ++ [Z_to_bv 8 0]) (hm_name 3 ++ [Z_to_bv 8 0]) (Z_to_bv 64 0x28470) HN (HS 3%Z ltac:(lia)) (CS 8%Z ltac:(lia)) (CS 3%Z ltac:(lia))
                ltac:(lia) ltac:(rewrite LEN by lia; lia) ltac:(lia) ltac:(rewrite LEN by lia; lia) c1_3 ltac:(red; apply bv_eq; reflexivity) c10_3 c11_3) as (t3 & S3 & a10_3 & AG3).
    replace (Z_to_bv 64 PC_strcmp) with (0x32838 : word) in S3 by (apply bv_eq; reflexivity). replace (Z_to_bv 64 0x28470) with (0x28470 : word) in S3 by (apply bv_eq; reflexivity).
    replace (strcmp_Z (hm_name 8 ++ [Z_to_bv 8 0]) (hm_name 3 ++ [Z_to_bv 8 0])) with (57)%Z in a10_3 by (vm_compute; reflexivity).
    assert (k18_3 : getr t3 18 = Z_to_bv 64 name) by (rewrite (AG3 18) by notin_lit; exact d18_3).
    assert (k19_3 : getr t3 19 = Z_to_bv 64 0x34e20) by (rewrite (AG3 19) by notin_lit; exact d19_3).
    pose proof (fg_miss_3 rom t3 m (57)%Z ltac:(lia) ltac:(lia) a10_3) as M3.
    destruct (fg_call_4 rom t3 m name k18_3 k19_3) as (u4 & C4 & c1_4 & c10_4 & c11_4 & AGc4).
    assert (d18_4 : getr u4 18 = Z_to_bv 64 name) by (rewrite (AGc4 18) by notin_lit; exact k18_3).
    assert (d19_4 : getr u4 19 = Z_to_bv 64 0x34e20) by (rewrite (AGc4 19) by notin_lit; exact k19_3).
    destruct (STRCMP rom u4 m name (0x34e20 + 80 * 4)%Z (hm_name 8 ++ [Z_to_bv 8 0]) (hm_name 4 ++ [Z_to_bv 8 0]) (Z_to_bv 64 0x28480) HN (HS 4%Z ltac:(lia)) (CS 8%Z ltac:(lia)) (CS 4%Z ltac:(lia))
                ltac:(lia) ltac:(rewrite LEN by lia; lia) ltac:(lia) ltac:(rewrite LEN by lia; lia) c1_4 ltac:(red; apply bv_eq; reflexivity) c10_4 c11_4) as (t4 & S4 & a10_4 & AG4).
    replace (Z_to_bv 64 PC_strcmp) with (0x32838 : word) in S4 by (apply bv_eq; reflexivity). replace (Z_to_bv 64 0x28480) with (0x28480 : word) in S4 by (apply bv_eq; reflexivity).
    replace (strcmp_Z (hm_name 8 ++ [Z_to_bv 8 0]) (hm_name 4 ++ [Z_to_bv 8 0])) with (57)%Z in a10_4 by (vm_compute; reflexivity).
    assert (k18_4 : getr t4 18 = Z_to_bv 64 name) by (rewrite (AG4 18) by notin_lit; exact d18_4).
    assert (k19_4 : getr t4 19 = Z_to_bv 64 0x34e20) by (rewrite (AG4 19) by notin_lit; exact d19_4).
    pose proof (fg_miss_4 rom t4 m (57)%Z ltac:(lia) ltac:(lia) a10_4) as M4.
    destruct (fg_call_5 rom t4 m name k18_4 k19_4) as (u5 & C5 & c1_5 & c10_5 & c11_5 & AGc5).
    assert (d18_5 : getr u5 18 = Z_to_bv 64 name) by (rewrite (AGc5 18) by notin_lit; exact k18_4).
    assert (d19_5 : getr u5 19 = Z_to_bv 64 0x34e20) by (rewrite (AGc5 19) by notin_lit; exact k19_4).
    destruct (STRCMP rom u5 m name (0x34e20 + 80 * 5)%Z (hm_name 8 ++ [Z_to_bv 8 0]) (hm_name 5 ++ [Z_to_bv 8 0]) (Z_to_bv 64 0x28490) HN (HS 5%Z ltac:(lia)) (CS 8%Z ltac:(lia)) (CS 5%Z ltac:(lia))
                ltac:(lia) ltac:(rewrite LEN by lia; lia) ltac:(lia) ltac:(rewrite LEN by lia; lia) c1_5 ltac:(red; apply bv_eq; reflexivity) c10_5 c11_5) as (t5 & S5 & a10_5 & AG5).
    replace (Z_to_bv 64 PC_strcmp) with (0x32838 : word) in S5 by (apply bv_eq; reflexivity). replace (Z_to_bv 64 0x28490) with (0x28490 : word) in S5 by (apply bv_eq; reflexivity).
    replace (strcmp_Z (hm_name 8 ++ [Z_to_bv 8 0]) (hm_name 5 ++ [Z_to_bv 8 0])) with (-7)%Z in a10_5 by (vm_compute; reflexivity).
    assert (k18_5 : getr t5 18 = Z_to_bv 64 name) by (rewrite (AG5 18) by notin_lit; exact d18_5).
    assert (k19_5 : getr t5 19 = Z_to_bv 64 0x34e20) by (rewrite (AG5 19) by notin_lit; exact d19_5).
    pose proof (fg_miss_5 rom t5 m (-7)%Z ltac:(lia) ltac:(lia) a10_5) as M5.
    destruct (fg_call_6 rom t5 m name k18_5 k19_5) as (u6 & C6 & c1_6 & c10_6 & c11_6 & AGc6).
    assert (d18_6 : getr u6 18 = Z_to_bv 64 name) by (rewrite (AGc6 18) by notin_lit; exact k18_5).
    assert (d19_6 : getr u6 19 = Z_to_bv 64 0x34e20) by (rewrite (AGc6 19) by notin_lit; exact k19_5).
    destruct (STRCMP rom u6 m name (0x34e20 + 80 * 6)%Z (hm_name 8 ++ [Z_to_bv 8 0]) (hm_name 6 ++ [Z_to_bv 8 0]) (Z_to_bv 64 0x284a0) HN (HS 6%Z ltac:(lia)) (CS 8%Z ltac:(lia)) (CS 6%Z ltac:(lia))
                ltac:(lia) ltac:(rewrite LEN by lia; lia) ltac:(lia) ltac:(rewrite LEN by lia; lia) c1_6 ltac:(red; apply bv_eq; reflexivity) c10_6 c11_6) as (t6 & S6 & a10_6 & AG6).
    replace (Z_to_bv 64 PC_strcmp) with (0x32838 : word) in S6 by (apply bv_eq; reflexivity). replace (Z_to_bv 64 0x284a0) with (0x284a0 : word) in S6 by (apply bv_eq; reflexivity).
    replace (strcmp_Z (hm_name 8 ++ [Z_to_bv 8 0]) (hm_name 6 ++ [Z_to_bv 8 0])) with (-9)%Z in a10_6 by (vm_compute; reflexivity).
    assert (k18_6 : getr t6 18 = Z_to_bv 64 name) by (rewrite (AG6 18) by notin_lit; exact d18_6).
    assert (k19_6 : getr t6 19 = Z_to_bv 64 0x34e20) by (rewrite (AG6 19) by notin_lit; exact d19_6).
    pose proof (fg_miss_6 rom t6 m (-9)%Z ltac:(lia) ltac:(lia) a10_6) as M6.
    destruct (fg_call_7 rom t6 m name k18_6 k19_6) as (u7 & C7 & c1_7 & c10_7 & c11_7 & AGc7).
    assert (d18_7 : getr u7 18 = Z_to_bv 64 name) by (rewrite (AGc7 18) by notin_lit; exact k18_6).
    assert (d19_7 : getr u7 19 = Z_to_bv 64 0x34e20) by (rewrite (AGc7 19) by notin_lit; exact k19_6).
    destruct (STRCMP rom u7 m name (0x34e20 + 80 * 7)%Z (hm_name 8 ++ [Z_to_bv 8 0]) (hm_name 7 ++ [Z_to_bv 8 0]) (Z_to_bv 64 0x284b0) HN (HS 7%Z ltac:(lia)) (CS 8%Z ltac:(lia)) (CS 7%Z ltac:(lia))
                ltac:(lia) ltac:(rewrite LEN by lia; lia) ltac:(lia) ltac:(rewrite LEN by lia; lia) c1_7 ltac:(red; apply bv_eq; reflexivity) c10_7 c11_7) as (t7 & S7 & a10_7 & AG7).
    replace (Z_to_bv 64 PC_strcmp) with (0x32838 : word) in S7 by (apply bv_eq; reflexivity). replace (Z_to_bv 64 0x284b0) with (0x284b0 : word) in S7 by (apply bv_eq; reflexivity).
    replace (strcmp_Z (hm_name 8 ++ [Z_to_bv 8 0]) (hm_name 7 ++ [Z_to_bv 8 0])) with (-9)%Z in a10_7 by (vm_compute; reflexivity).
    assert (k18_7 : getr t7 18 = Z_to_bv 64 name) by (rewrite (AG7 18) by notin_lit; exact d18_7).
    assert (k19_7 : getr t7 19 = Z_to_bv 64 0x34e20) by (rewrite (AG7 19) by notin_lit; exact d19_7).
    pose proof (fg_miss_7 rom t7 m (-9)%Z ltac:(lia) ltac:(lia) a10_7) as M7.
    destruct (fg_call_8 rom t7 m name k18_7 k19_7) as (u8 & C8 & c1_8 & c10_8 & c11_8 & AGc8).
    assert (d18_8 : getr u8 18 = Z_to_bv 64 name) by (rewrite (AGc8 18) by notin_lit; exact k18_7).
    assert (d19_8 : getr u8 19 = Z_to_bv 64 0x34e20) by (rewrite (AGc8 19) by notin_lit; exact k19_7).
    destruct (STRCMP rom u8 m name (0x34e20 + 80 * 8)%Z (hm_name 8 ++ [Z_to_bv 8 0]) (hm_name 8 ++ [Z_to_bv 8 0]) (Z_to_bv 64 0x284c0) HN (HS 8%Z ltac:(lia)) (CS 8%Z ltac:(lia)) (CS 8%Z ltac:(lia))
                ltac:(lia) ltac:(rewrite LEN by lia; lia) ltac:(lia) ltac:(rewrite LEN by lia; lia) c1_8 ltac:(red; apply bv_eq; reflexivity) c10_8 c11_8) as (t8 & S8 & a10_8 & AG8).
    replace (Z_to_bv 64 PC_strcmp) with (0x32838 : word) in S8 by (apply bv_eq; reflexivity). replace (Z_to_bv 64 0x284c0) with (0x284c0 : word) in S8 by (apply bv_eq; reflexivity).
    replace (strcmp_Z (hm_name 8 ++ [Z_to_bv 8 0]) (hm_name 8 ++ [Z_to_bv 8 0])) with (0)%Z in a10_8 by (vm_compute; reflexivity).
    assert (k18_8 : getr t8 18 = Z_to_bv 64 name) by (rewrite (AG8 18) by notin_lit; exact d18_8).
    assert (k19_8 : getr t8 19 = Z_to_bv 64 0x34e20) by (rewrite (AG8 19) by notin_lit; exact d19_8).
    destruct (fg_hit_8 rom t8 m a10_8) as (rf & HITf & f18 & AGf).
    exists rf. split; [eapply msteps_trans; [exact S0 | eapply msteps_trans; [exact M0 | eapply msteps_trans; [exact C1 | eapply msteps_trans; [exact S1 | eapply msteps_trans; [exact M1 | eapply msteps_trans; [exact C2 | eapply msteps_trans; [exact S2 | eapply msteps_trans; [exact M2 | eapply msteps_trans; [exact C3 | eapply msteps_trans; [exact S3 | eapply msteps_trans; [exact M3 | eapply msteps_trans; [exact C4 | eapply msteps_trans; [exact S4 | eapply msteps_trans; [exact M4 | eapply msteps_trans; [exact C5 | eapply msteps_trans; [exact S5 | eapply msteps_trans; [exact M5 | eapply msteps_trans; [exact C6 | eapply msteps_trans; [exact S6 | eapply msteps_trans; [exact M6 | eapply msteps_trans; [exact C7 | eapply msteps_trans; [exact S7 | eapply msteps_trans; [exact M7 | eapply msteps_trans; [exact C8 | eapply msteps_trans; [exact S8 | exact HITf]]]]]]]]]]]]]]]]]]]]]]]]]|]. split; [exact f18|].
    intros x Hx. rewrite (AGf x) by (intros X; exact (Hx (in_h1 x X))). rewrite (AG8 x) by (intros X; exact (Hx (in_s4 x X))). rewrite (AGc8 x) by (intros X; exact (Hx (in_c3 x X))). rewrite (AG7 x) by (intros X; exact (Hx (in_s4 x X))). rewrite (AGc7 x) by (intros X; exact (Hx (in_c3 x X))). rewrite (AG6 x) by (intros X; exact (Hx (in_s4 x X))). rewrite (AGc6 x) by (intros X; exact (Hx (in_c3 x X))). rewrite (AG5 x) by (intros X; exact (Hx (in_s4 x X))). rewrite (AGc5 x) by (intros X; exact (Hx (in_c3 x X))). rewrite (AG4 x) by (intros X; exact (Hx (in_s4 x X))). rewrite (AGc4 x) by (intros X; exact (Hx (in_c3 x X))). rewrite (AG3 x) by (intros X; exact (Hx (in_s4 x X))). rewrite (AGc3 x) by (intros X; exact (Hx (in_c3 x X))). rewrite (AG2 x) by (intros X; exact (Hx (in_s4 x X))). rewrite (AGc2 x) by (intros X; exact (Hx (in_c3 x X))). rewrite (AG1 x) by (intros X; exact (Hx (in_s4 x X))). rewrite (AGc1 x) by (intros X; exact (Hx (in_c3 x X))). rewrite (AG0 x) by (intros X; exact (Hx (in_s4 x X))). reflexivity.
  - (* [comment removed for export] *)
    destruct (STRCMP rom regs m name (0x34e20 + 80 * 0)%Z (hm_name 9 ++ [Z_to_bv 8 0]) (hm_name 0 ++ [Z_to_bv 8 0]) (Z_to_bv 64 0x28440) HN (HS 0%Z ltac:(lia)) (CS 9%Z ltac:(lia)) (CS 0%Z ltac:(lia))
                ltac:(lia) ltac:(rewrite LEN by lia; lia) ltac:(lia) ltac:(rewrite LEN by lia; lia) R1 ltac:(red; apply bv_eq; reflexivity) R10 R11) as (t0 & S0 & a10_0 & AG0).
    replace (Z_to_bv 64 PC_strcmp) with (0x32838 : word) in S0 by (apply bv_eq; reflexivity). replace (Z_to_bv 64 0x28440) with (0x28440 : word) in S0 by (apply bv_eq; reflexivity).
    replace (strcmp_Z (hm_name 9 ++ [Z_to_bv 8 0]) (hm_name 0 ++ [Z_to_bv 8 0])) with (57)%Z in a10_0 by (vm_compute; reflexivity).
    assert (k18_0 : getr t0 18 = Z_to_bv 64 name) by (rewrite (AG0 18) by notin_lit; exact R18).
    assert (k19_0 : getr t0 19 = Z_to_bv 64 0x34e20) by (rewrite (AG0 19) by notin_lit; exact R19).
    pose proof (fg_miss_0 rom t0 m (57)%Z ltac:(lia) ltac:(lia) a10_0) as M0.
    destruct (fg_call_1 rom t0 m name k18_0 k19_0) as (u1 & C1 & c1_1 & c10_1 & c11_1 & AGc1).
    assert (d18_1 : getr u1 18 = Z_to_bv 64 name) by (rewrite (AGc1 18) by notin_lit; exact k18_0).
    assert (d19_1 : getr u1 19 = Z_to_bv 64 0x34e20) by (rewrite (AGc1 19) by notin_lit; exact k19_0).
    destruct (STRCMP rom u1 m name (0x34e20 + 80 * 1)%Z (hm_name 9 ++ [Z_to_bv 8 0]) (hm_name 1 ++ [Z_to_bv 8 0]) (Z_to_bv 64 0x28450) HN (HS 1%Z ltac:(lia)) (CS 9%Z ltac:(lia)) (CS 1%Z ltac:(lia))
                ltac:(lia) ltac:(rewrite LEN by lia; lia) ltac:(lia) ltac:(rewrite LEN by lia; lia) c1_1 ltac:(red; apply bv_eq; reflexivity) c10_1 c11_1) as (t1 & S1 & a10_1 & AG1).
    replace (Z_to_bv 64 PC_strcmp) with (0x32838 : word) in S1 by (apply bv_eq; reflexivity). replace (Z_to_bv 64 0x28450) with (0x28450 : word) in S1 by (apply bv_eq; reflexivity).
    replace (strcmp_Z (hm_name 9 ++ [Z_to_bv 8 0]) (hm_name 1 ++ [Z_to_bv 8 0])) with (57)%Z in a10_1 by (vm_compute; reflexivity).
    assert (k18_1 : getr t1 18 = Z_to_bv 64 name) by (rewrite (AG1 18) by notin_lit; exact d18_1).
    assert (k19_1 : getr t1 19 = Z_to_bv 64 0x34e20) by (rewrite (AG1 19) by notin_lit; exact d19_1).
    pose proof (fg_miss_1 rom t1 m (57)%Z ltac:(lia) ltac:(lia) a10_1) as M1.
    destruct (fg_call_2 rom t1 m name k18_1 k19_1) as (u2 & C2 & c1_2 & c10_2 & c11_2 & AGc2).
    assert (d18_2 : getr u2 18 = Z_to_bv 64 name) by (rewrite (AGc2 18) by notin_lit; exact k18_1).
    assert (d19_2 : getr u2 19 = Z_to_bv 64 0x34e20) by (rewrite (AGc2 19) by notin_lit; exact k19_1).
    destruct (STRCMP rom u2 m name (0x34e20 + 80 * 2)%Z (hm_name 9 ++ [Z_to_bv 8 0]) (hm_name 2 ++ [Z_to_bv 8 0]) (Z_to_bv 64 0x28460) HN (HS 2%Z ltac:(lia)) (CS 9%Z ltac:(lia)) (CS 2%Z ltac:(lia))
                ltac:(lia) ltac:(rewrite LEN by lia; lia) ltac:(lia) ltac:(rewrite LEN by lia; lia) c1_2 ltac:(red; apply bv_eq; reflexivity) c10_2 c11_2) as (t2 & S2 & a10_2 & AG2).
    replace (Z_to_bv 64 PC_strcmp) with (0x32838 : word) in S2 by (apply bv_eq; reflexivity). replace (Z_to_bv 64 0x28460) with (0x28460 : word) in S2 by (apply bv_eq; reflexivity).
    replace (strcmp_Z (hm_name 9 ++ [Z_to_bv 8 0]) (hm_name 2 ++ [Z_to_bv 8 0])) with (57)%Z in a10_2 by (vm_compute; reflexivity).
    assert (k18_2 : getr t2 18 = Z_to_bv 64 name) by (rewrite (AG2 18) by notin_lit; exact d18_2).
    assert (k19_2 : getr t2 19 = Z_to_bv 64 0x34e20) by (rewrite (AG2 19) by notin_lit; exact d19_2).
    pose proof (fg_miss_2 rom t2 m (57)%Z ltac:(lia) ltac:(lia) a10_2) as M2.
    destruct (fg_call_3 rom t2 m name k18_2 k19_2) as (u3 & C3 & c1_3 & c10_3 & c11_3 & AGc3).
    assert (d18_3 : getr u3 18 = Z_to_bv 64 name) by (rewrite (AGc3 18) by notin_lit; exact k18_2).
    assert (d19_3 : getr u3 19 = Z_to_bv 64 0x34e20) by (rewrite (AGc3 19) by notin_lit; exact k19_2).
    destruct (STRCMP rom u3 m name (0x34e20 + 80 * 3)%Z (hm_name 9 ++ [Z_to_bv 8 0]) (hm_name 3 ++ [Z_to_bv 8 0]) (Z_to_bv 64 0x28470) HN (HS 3%Z ltac:(lia)) (CS 9%Z ltac:(lia)) (CS 3%Z ltac:(lia))
                ltac:(lia) ltac:(rewrite LEN by lia; lia) ltac:(lia) ltac:(rewrite LEN by lia; lia) c1_3 ltac:(red; apply bv_eq; reflexivity) c10_3 c11_3) as (t3 & S3 & a10_3 & AG3).
    replace (Z_to_bv 64 PC_strcmp) with (0x32838 : word) in S3 by (apply bv_eq; reflexivity). replace (Z_to_bv 64 0x28470) with (0x28470 : word) in S3 by (apply bv_eq; reflexivity).
    replace (strcmp_Z (hm_name 9 ++ [Z_to_bv 8 0]) (hm_name 3 ++ [Z_to_bv 8 0])) with (57)%Z in a10_3 by (vm_compute; reflexivity).
    assert (k18_3 : getr t3 18 = Z_to_bv 64 name) by (rewrite (AG3 18) by notin_lit; exact d18_3).
    assert (k19_3 : getr t3 19 = Z_to_bv 64 0x34e20) by (rewrite (AG3 19) by notin_lit; exact d19_3).
    pose proof (fg_miss_3 rom t3 m (57)%Z ltac:(lia) ltac:(lia) a10_3) as M3.
    destruct (fg_call_4 rom t3 m name k18_3 k19_3) as (u4 & C4 & c1_4 & c10_4 & c11_4 & AGc4).
    assert (d18_4 : getr u4 18 = Z_to_bv 64 name) by (rewrite (AGc4 18) by notin_lit; exact k18_3).
    assert (d19_4 : getr u4 19 = Z_to_bv 64 0x34e20) by (rewrite (AGc4 19) by notin_lit; exact k19_3).
    destruct (STRCMP rom u4 m name (0x34e20 + 80 * 4)%Z (hm_name 9 ++ [Z_to_bv 8 0]) (hm_name 4 ++ [Z_to_bv 8 0]) (Z_to_bv 64 0x28480) HN (HS 4%Z ltac:(lia)) (CS 9%Z ltac:(lia)) (CS 4%Z ltac:(lia))
                ltac:(lia) ltac:(rewrite LEN by lia; lia) ltac:(lia) ltac:(rewrite LEN by lia; lia) c1_4 ltac:(red; apply bv_eq; reflexivity) c10_4 c11_4) as (t4 & S4 & a10_4 & AG4).
    replace (Z_to_bv 64 PC_strcmp) with (0x32838 : word) in S4 by (apply bv_eq; reflexivity). replace (Z_to_bv 64 0x28480) with (0x28480 : word) in S4 by (apply bv_eq; reflexivity).
    replace (strcmp_Z (hm_name 9 ++ [Z_to_bv 8 0]) (hm_name 4 ++ [Z_to_bv 8 0])) with (57)%Z in a10_4 by (vm_compute; reflexivity).
    assert (k18_4 : getr t4 18 = Z_to_bv 64 name) by (rewrite (AG4 18) by notin_lit; exact d18_4).
    assert (k19_4 : getr t4 19 = Z_to_bv 64 0x34e20) by (rewrite (AG4 19) by notin_lit; exact d19_4).
    pose proof (fg_miss_4 rom t4 m (57)%Z ltac:(lia) ltac:(lia) a10_4) as M4.
    destruct (fg_call_5 rom t4 m name k18_4 k19_4) as (u5 & C5 & c1_5 & c10_5 & c11_5 & AGc5).
    assert (d18_5 : getr u5 18 = Z_to_bv 64 name) by (rewrite (AGc5 18) by notin_lit; exact k18_4).
    assert (d19_5 : getr u5 19 = Z_to_bv 64 0x34e20) by (rewrite (AGc5 19) by notin_lit; exact k19_4).
    destruct (STRCMP rom u5 m name (0x34e20 + 80 * 5)%Z (hm_name 9 ++ [Z_to_bv 8 0]) (hm_name 5 ++ [Z_to_bv 8 0]) (Z_to_bv 64 0x28490) HN (HS 5%Z ltac:(lia)) (CS 9%Z ltac:(lia)) (CS 5%Z ltac:(lia))
                ltac:(lia) ltac:(rewrite LEN by lia; lia) ltac:(lia) ltac:(rewrite LEN by lia; lia) c1_5 ltac:(red; apply bv_eq; reflexivity) c10_5 c11_5) as (t5 & S5 & a10_5 & AG5).
    replace (Z_to_bv 64 PC_strcmp) with (0x32838 : word) in S5 by (apply bv_eq; reflexivity). replace (Z_to_bv 64 0x28490) with (0x28490 : word) in S5 by (apply bv_eq; reflexivity).
    replace (strcmp_Z (hm_name 9 ++ [Z_to_bv 8 0]) (hm_name 5 ++ [Z_to_bv 8 0])) with (-7)%Z in a10_5 by (vm_compute; reflexivity).
    assert (k18_5 : getr t5 18 = Z_to_bv 64 name) by (rewrite (AG5 18) by notin_lit; exact d18_5).
    assert (k19_5 : getr t5 19 = Z_to_bv 64 0x34e20) by (rewrite (AG5 19) by notin_lit; exact d19_5).
    pose proof (fg_miss_5 rom t5 m (-7)%Z ltac:(lia) ltac:(lia) a10_5) as M5.
    destruct (fg_call_6 rom t5 m name k18_5 k19_5) as (u6 & C6 & c1_6 & c10_6 & c11_6 & AGc6).
    assert (d18_6 : getr u6 18 = Z_to_bv 64 name) by (rewrite (AGc6 18) by notin_lit; exact k18_5).
    assert (d19_6 : getr u6 19 = Z_to_bv 64 0x34e20) by (rewrite (AGc6 19) by notin_lit; exact k19_5).
    destruct (STRCMP rom u6 m name (0x34e20 + 80 * 6)%Z (hm_name 9 ++ [Z_to_bv 8 0]) (hm_name 6 ++ [Z_to_bv 8 0]) (Z_to_bv 64 0x284a0) HN (HS 6%Z ltac:(lia)) (CS 9%Z ltac:(lia)) (CS 6%Z ltac:(lia))
                ltac:(lia) ltac:(rewrite LEN by lia; lia) ltac:(lia) ltac:(rewrite LEN by lia; lia) c1_6 ltac:(red; apply bv_eq; reflexivity) c10_6 c11_6) as (t6 & S6 & a10_6 & AG6).
    replace (Z_to_bv 64 PC_strcmp) with (0x32838 : word) in S6 by (apply bv_eq; reflexivity). replace (Z_to_bv 64 0x284a0) with (0x284a0 : word) in S6 by (apply bv_eq; reflexivity).
    replace (strcmp_Z (hm_name 9 ++ [Z_to_bv 8 0]) (hm_name 6 ++ [Z_to_bv 8 0])) with (-9)%Z in a10_6 by (vm_compute; reflexivity).
    assert (k18_6 : getr t6 18 = Z_to_bv 64 name) by (rewrite (AG6 18) by notin_lit; exact d18_6).
    assert (k19_6 : getr t6 19 = Z_to_bv 64 0x34e20) by (rewrite (AG6 19) by notin_lit; exact d19_6).
    pose proof (fg_miss_6 rom t6 m (-9)%Z ltac:(lia) ltac:(lia) a10_6) as M6.
    destruct (fg_call_7 rom t6 m name k18_6 k19_6) as (u7 & C7 & c1_7 & c10_7 & c11_7 & AGc7).
    assert (d18_7 : getr u7 18 = Z_to_bv 64 name) by (rewrite (AGc7 18) by notin_lit; exact k18_6).
    assert (d19_7 : getr u7 19 = Z_to_bv 64 0x34e20) by (rewrite (AGc7 19) by notin_lit; exact k19_6).
    destruct (STRCMP rom u7 m name (0x34e20 + 80 * 7)%Z (hm_name 9 ++ [Z_to_bv 8 0]) (hm_name 7 ++ [Z_to_bv 8 0]) (Z_to_bv 64 0x284b0) HN (HS 7%Z ltac:(lia)) (CS 9%Z ltac:(lia)) (CS 7%Z ltac:(lia))
                ltac:(lia) ltac:(rewrite LEN by lia; lia) ltac:(lia) ltac:(rewrite LEN by lia; lia) c1_7 ltac:(red; apply bv_eq; reflexivity) c10_7 c11_7) as (t7 & S7 & a10_7 & AG7).
    replace (Z_to_bv 64 PC_strcmp) with (0x32838 : word) in S7 by (apply bv_eq; reflexivity). replace (Z_to_bv 64 0x284b0) with (0x284b0 : word) in S7 by (apply bv_eq; reflexivity).
    replace (strcmp_Z (hm_name 9 ++ [Z_to_bv 8 0]) (hm_name 7 ++ [Z_to_bv 8 0])) with (-9)%Z in a10_7 by (vm_compute; reflexivity).
    assert (k18_7 : getr t7 18 = Z_to_bv 64 name) by (rewrite (AG7 18) by notin_lit; exact d18_7).
    assert (k19_7 : getr t7 19 = Z_to_bv 64 0x34e20) by (rewrite (AG7 19) by notin_lit; exact d19_7).
    pose proof (fg_miss_7 rom t7 m (-9)%Z ltac:(lia) ltac:(lia) a10_7) as M7.
    destruct (fg_call_8 rom t7 m name k18_7 k19_7) as (u8 & C8 & c1_8 & c10_8 & c11_8 & AGc8).
    assert (d18_8 : getr u8 18 = Z_to_bv 64 name) by (rewrite (AGc8 18) by notin_lit; exact k18_7).
    assert (d19_8 : getr u8 19 = Z_to_bv 64 0x34e20) by (rewrite (AGc8 19) by notin_lit; exact k19_7).
    destruct (STRCMP rom u8 m name (0x34e20 + 80 * 8)%Z (hm_name 9 ++ [Z_to_bv 8 0]) (hm_name 8 ++ [Z_to_bv 8 0]) (Z_to_bv 64 0x284c0) HN (HS 8%Z ltac:(lia)) (CS 9%Z ltac:(lia)) (CS 8%Z ltac:(lia))
                ltac:(lia) ltac:(rewrite LEN by lia; lia) ltac:(lia) ltac:(rewrite LEN by lia; lia) c1_8 ltac:(red; apply bv_eq; reflexivity) c10_8 c11_8) as (t8 & S8 & a10_8 & AG8).
    replace (Z_to_bv 64 PC_strcmp) with (0x32838 : word) in S8 by (apply bv_eq; reflexivity). replace (Z_to_bv 64 0x284c0) with (0x284c0 : word) in S8 by (apply bv_eq; reflexivity).
    replace (strcmp_Z (hm_name 9 ++ [Z_to_bv 8 0]) (hm_name 8 ++ [Z_to_bv 8 0])) with (6)%Z in a10_8 by (vm_compute; reflexivity).
    assert (k18_8 : getr t8 18 = Z_to_bv 64 name) by (rewrite (AG8 18) by notin_lit; exact d18_8).
    assert (k19_8 : getr t8 19 = Z_to_bv 64 0x34e20) by (rewrite (AG8 19) by notin_lit; exact d19_8).
    pose proof (fg_miss_8 rom t8 m (6)%Z ltac:(lia) ltac:(lia) a10_8) as M8.
    destruct (fg_call_9 rom t8 m name k18_8 k19_8) as (u9 & C9 & c1_9 & c10_9 & c11_9 & AGc9).
    assert (d18_9 : getr u9 18 = Z_to_bv 64 name) by (rewrite (AGc9 18) by notin_lit; exact k18_8).
    assert (d19_9 : getr u9 19 = Z_to_bv 64 0x34e20) by (rewrite (AGc9 19) by notin_lit; exact k19_8).
    destruct (STRCMP rom u9 m name (0x34e20 + 80 * 9)%Z (hm_name 9 ++ [Z_to_bv 8 0]) (hm_name 9 ++ [Z_to_bv 8 0]) (Z_to_bv 64 0x284d0) HN (HS 9%Z ltac:(lia)) (CS 9%Z ltac:(lia)) (CS 9%Z ltac:(lia))
                ltac:(lia) ltac:(rewrite LEN by lia; lia) ltac:(lia) ltac:(rewrite LEN by lia; lia) c1_9 ltac:(red; apply bv_eq; reflexivity) c10_9 c11_9) as (t9 & S9 & a10_9 & AG9).
    replace (Z_to_bv 64 PC_strcmp) with (0x32838 : word) in S9 by (apply bv_eq; reflexivity). replace (Z_to_bv 64 0x284d0) with (0x284d0 : word) in S9 by (apply bv_eq; reflexivity).
    replace (strcmp_Z (hm_name 9 ++ [Z_to_bv 8 0]) (hm_name 9 ++ [Z_to_bv 8 0])) with (0)%Z in a10_9 by (vm_compute; reflexivity).
    assert (k18_9 : getr t9 18 = Z_to_bv 64 name) by (rewrite (AG9 18) by notin_lit; exact d18_9).
    assert (k19_9 : getr t9 19 = Z_to_bv 64 0x34e20) by (rewrite (AG9 19) by notin_lit; exact d19_9).
    destruct (fg_hit_9 rom t9 m a10_9) as (rf & HITf & f18 & AGf).
    exists rf. split; [eapply msteps_trans; [exact S0 | eapply msteps_trans; [exact M0 | eapply msteps_trans; [exact C1 | eapply msteps_trans; [exact S1 | eapply msteps_trans; [exact M1 | eapply msteps_trans; [exact C2 | eapply msteps_trans; [exact S2 | eapply msteps_trans; [exact M2 | eapply msteps_trans; [exact C3 | eapply msteps_trans; [exact S3 | eapply msteps_trans; [exact M3 | eapply msteps_trans; [exact C4 | eapply msteps_trans; [exact S4 | eapply msteps_trans; [exact M4 | eapply msteps_trans; [exact C5 | eapply msteps_trans; [exact S5 | eapply msteps_trans; [exact M5 | eapply msteps_trans; [exact C6 | eapply msteps_trans; [exact S6 | eapply msteps_trans; [exact M6 | eapply msteps_trans; [exact C7 | eapply msteps_trans; [exact S7 | eapply msteps_trans; [exact M7 | eapply msteps_trans; [exact C8 | eapply msteps_trans; [exact S8 | eapply msteps_trans; [exact M8 | eapply msteps_trans; [exact C9 | eapply msteps_trans; [exact S9 | exact HITf]]]]]]]]]]]]]]]]]]]]]]]]]]]]|]. split; [exact f18|].
    intros x Hx. rewrite (AGf x) by (intros X; exact (Hx (in_h1 x X))). rewrite (AG9 x) by (intros X; exact (Hx (in_s4 x X))). rewrite (AGc9 x) by (intros X; exact (Hx (in_c3 x X))). rewrite (AG8 x) by (intros X; exact (Hx (in_s4 x X))). rewrite (AGc8 x) by (intros X; exact (Hx (in_c3 x X))). rewrite (AG7 x) by (intros X; exact (Hx (in_s4 x X))). rewrite (AGc7 x) by (intros X; exact (Hx (in_c3 x X))). rewrite (AG6 x) by (intros X; exact (Hx (in_s4 x X))). rewrite (AGc6 x) by (intros X; exact (Hx (in_c3 x X))). rewrite (AG5 x) by (intros X; exact (Hx (in_s4 x X))). rewrite (AGc5 x) by (intros X; exact (Hx (in_c3 x X))). rewrite (AG4 x) by (intros X; exact (Hx (in_s4 x X))). rewrite (AGc4 x) by (intros X; exact (Hx (in_c3 x X))). rewrite (AG3 x) by (intros X; exact (Hx (in_s4 x X))). rewrite (AGc3 x) by (intros X; exact (Hx (in_c3 x X))). rewrite (AG2 x) by (intros X; exact (Hx (in_s4 x X))). rewrite (AGc2 x) by (intros X; exact (Hx (in_c3 x X))). rewrite (AG1 x) by (intros X; exact (Hx (in_s4 x X))). rewrite (AGc1 x) by (intros X; exact (Hx (in_c3 x X))). rewrite (AG0 x) by (intros X; exact (Hx (in_s4 x X))). reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma W_selnames : forall C A m md i, W C A m md -> (0 <= i < 10)%Z -> rd_str SEGS m (A_SELNAMES + 80 * i) (hm_name i ++ [Z_to_bv 8 0]).
Proof.
  intros C A m md i HW Hi. apply rd_str_rdn.
  assert (I : (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9)%Z) by lia.
  destruct I as [->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]];
    (match goal with |- rdn _ _ (Z_to_bv 64 ?a) ?n = _ => let lo := eval vm_compute in a in let k := eval vm_compute in n in
       change (Z_to_bv 64 a) with (Z_to_bv 64 lo); change n with k;
       rewrite <- AL_segs; rewrite (W_rdn_clr _ _ _ _ lo k HW); [rewrite AL_segs; vm_refl_bv | intros z Hz; cbv [inZs inZ fst snd ll_clr LLU16]; lia | lia | cbn; lia] end).
Qed.

Lemma hm_len : forall i, (0 <= i < 10)%Z -> Z.of_nat (length (hm_name i ++ [Z_to_bv 8 0])) = 8%Z.
Proof.
  intros i Hi. assert (I : (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9)%Z) by lia.
  destruct I as [->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition FHG_STACK : Z := 96 + 160 + LSF.        (* [comment removed for export] *)

Lemma cells_FRG : forall m s ret regs, (96 <= s)%Z -> (s < 2 ^ 64)%Z -> cellsZ (FRG m s ret regs) (frameG s ret regs).
Proof. intros m s ret regs Hs Hs64. unfold frameG, FRG. cbn [cellsZ]. repeat split; rdn_solve. Qed.
Lemma frameG_bounds : forall s ret r0, (96 <= s)%Z -> (s < 2 ^ 64)%Z -> Forall (fun av => s - 88 <= fst av /\ fst av + 8 <= s)%Z (frameG s ret r0).
Proof. intros s ret r0 Hs Hs64. unfold frameG. repeat (apply Forall_cons; [cbn [fst snd]; lia |]). apply Forall_nil. Qed.
Lemma FRG_out : forall m s ret regs (x : word), (96 <= s)%Z -> (s < 2 ^ 64)%Z -> ~ (s - 88 <= u x < s)%Z -> FRG m s ret regs x = m x.
Proof.
  intros m s ret regs x Hs Hs64 Hx. unfold FRG.
  repeat (rewrite (wbytes_out_Z _ _ 8); [| rewrite length_N_to_le_bytes; reflexivity | lia | lia | lia]). reflexivity.
Qed.
Lemma cellsG_frm : forall C s' m m' s ret r0, Cok C -> FRM C s' m m' -> (c_top C - LSTK <= s')%Z -> (s' <= s - 88)%Z -> (96 <= s)%Z -> (s < 2 ^ 64)%Z ->
  cellsZ m (frameG s ret r0) -> cellsZ m' (frameG s ret r0).
Proof.
  intros C s' m m' s ret r0 CK F H1 H2 Hs Hs64 CE. apply (cellsZ_frm C s' m m' _ CK F H1); [|exact CE].
  eapply Forall_impl; [|exact (frameG_bounds s ret r0 Hs Hs64)]. intros [a v] [X Y]; cbn [fst snd] in *. lia.
Qed.
Lemma cellsG_out : forall m m' (lo hi : Z) s ret r0, (forall x : word, ~ (lo <= u x < hi)%Z -> m' x = m x) -> (hi <= s - 88 \/ s <= lo)%Z -> (96 <= s)%Z -> (s < 2 ^ 64)%Z ->
  cellsZ m (frameG s ret r0) -> cellsZ m' (frameG s ret r0).
Proof.
  intros m m' lo hi s ret r0 OUT Hd Hs Hs64 CE. apply (cellsZ_out m m' lo hi _ OUT); [|exact CE].
  eapply Forall_impl; [|exact (frameG_bounds s ret r0 Hs Hs64)]. intros [a v] [X Y]; cbn [fst snd] in *. lia.
Qed.

Lemma str_pixFHMTGen_1 : str16 0x108aa 12. Proof. str16_tac. Qed.
Lemma str_msg_pixs_undef' : str16 0x10298 16. Proof. str16_tac. Qed.

(* [comment removed for export] *)
Lemma pixt_new_frame : forall C A A1 m2 md2 m' (lo hi pixd w h d cd data : Z) (cv : cmapv),
  Cok C -> W C A1 m2 md2 -> (alloc_top (c_vm C) <= lo)%Z -> (0 <= wpl_of w d * h)%Z ->
  pixt_new C A A1 m2 pixd w h d cd data cv ->
  (forall a : word, ~ (lo <= u a < hi)%Z -> ~ (data <= u a < data + 4 * (wpl_of w d * h))%Z -> m' a = m2 a) ->
  pixt_new C A A1 m' pixd w h d cd data cv.
Proof.
  intros C A A1 m2 md2 m' lo hi pixd w h d cd data cv CK HW Hlo Hn PT FP.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  destruct PT as (Gp & TOPp & ALp & Gd & TOPd & ALd & NEpd & L0p & L0d & L00p & L00d & L1p & L1d & PXd & CMR).
  assert (NEw : Z_to_bv 64 pixd <> Z_to_bv 64 data) by (apply zbv_ne2; lia).
  pose proof (blk_apart C A1 m2 _ _ _ _ _ CK HW L1p L1d NEw ltac:(lia) ltac:(lia)) as APpd. rewrite !u_Z2bv in APpd by lia.
  unfold pixt_new. repeat (split; [assumption|]). split.
  - apply (PIXat_frame m2); [exact PXd|]. intros x Hx. apply FP; lia.
  - destruct CMR as [[CD0 LEQ] | (ad & CMOKc & Gcd & TOPcd & Gad & TOPad & NEcdad & NEcdp & NEcdd & NEadp & NEadd & LAcd & LAad & L00cd & L00ad & L2cd & L2ad & CM4 & LEQ)]; [left; split; [exact CD0 | exact LEQ] | right].
    exists ad. do 16 (split; [assumption|]). split; [| exact LEQ].
    assert (NEw1 : Z_to_bv 64 cd <> Z_to_bv 64 data) by (apply zbv_ne2; lia).
    pose proof (blk_apart C A1 m2 _ _ _ _ _ CK HW L2cd L1d NEw1 ltac:(lia) ltac:(lia)) as APcd. rewrite !u_Z2bv in APcd by lia.
    apply (CMAPat_frame m2); [exact CM4|]. intros x Hx. apply FP; lia.
Qed.

Definition pixFHMTGen_1_contract : Prop :=
  forall C A m md regs (s pixs w h cm datas name j : Z) (cv : cmapv) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + FHG_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x45480 ->
  getr regs 10 = Z_to_bv 64 0 -> getr regs 11 = Z_to_bv 64 pixs -> getr regs 12 = Z_to_bv 64 name ->
  PIXat m pixs (hdv (w + 64) (h + 64) 1 cm datas) -> hdr_ok (w + 64) (h + 64) 1 -> (1 <= w)%Z -> (1 <= h)%Z ->
  live A (Z_to_bv 64 pixs) = Some 64%Z -> live A (Z_to_bv 64 datas) = Some (4 * (wpl_of (w + 64) 1 * (h + 64)))%Z -> cm_facts A m cm cv ->
  (0 <= j < 10)%Z -> selname_at (alloc_top (c_vm C)) A m name (hm_name j) ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_pixcopy <= kR)%Z -> (RB10_pixcopy (4 * (wpl_of (w + 64) 1 * (h + 64))) <= bR)%Z ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
     ( (getr regs' 10 = Z_to_bv 64 0 /\ forall q, live A' q = live A q)
       \/ (exists pixd cd data, getr regs' 10 = Z_to_bv 64 pixd /\ pixt_new C A A' m' pixd (w + 64) (h + 64) 1 cd data cv) ) ->
     aroom A' vm' (kR - RK_pixcopy) (bR - RB10_pixcopy (4 * (wpl_of (w + 64) 1 * (h + 64)))) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (Z_to_bv 64 PC_pixFHMTGen_1) m al_rom) md) S.

(* [comment removed for export] *)
Definition pixFHMTGen_1_null_contract : Prop :=
  forall C A m md regs (s : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + FHG_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 10 = Z_to_bv 64 0 -> getr regs 11 = Z_to_bv 64 0 ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' -> POSTM C A s m m' -> getr regs' 10 = Z_to_bv 64 0 ->
      realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (Z_to_bv 64 PC_pixFHMTGen_1) m al_rom) md) S.

Theorem pixFHMTGen_1_null_W : pixFHMTGen_1_null_contract.
Proof.
  unfold pixFHMTGen_1_null_contract.
  intros C A m md regs s ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H10 H11 HK.
  replace (Z_to_bv 64 PC_pixFHMTGen_1) with (0x283dc : word) by (apply bv_eq; reflexivity).
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold FHG_STACK, LSF in *.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  destruct (fg_N1 al_rom regs m s 0 ret ltac:(lia) ltac:(lia) (W_sok_win C A m md (s - 96) 96 CK HW ltac:(lia) ltac:(cbn; lia)) H2 H1 H10 H11) as (r1 & RUN1 & Q2 & Q8 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |]. clear RUN1.
  assert (WP1 : W C A (FRG m s ret regs) md /\ POSTM C A s m (FRG m s ret regs)) by (unfold FRG; wp_win CK).
  destruct WP1 as [HW1 PM1]. set (M1 := FRG m s ret regs) in *.
  destruct (fg_N2 al_rom r1 regs M1 s 0 ret ltac:(lia) ltac:(lia) (W_sev_got C A M1 _ HW1) (W_sev C A M1 _ HW1) (cells_FRG m s ret regs ltac:(lia) ltac:(lia)) Q2 Q8)
    as (r2 & RUN2 & V2 & V1 & V10 & V11 & V12 & VR & AG2).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN2 |]. clear RUN2.
  apply (returnErrorPtr_W C A M1 md r2 s 0x10298 0x108aa 16 12 ret (Z_to_bv 64 0) S CK HW1 V2 Hs16 ltac:(unfold LSF; lia) Hhi V1 Hret
           V10 V11 V12 str_msg_pixs_undef' str_pixFHMTGen_1).
  intros m4 r5 HW4 OUT4 GR4 CS4 A10. unfold LSF in OUT4.
  apply (HK m4 r5 HW4).
  - apply cs_kept_intro; csr; first [reflexivity | solve [apply VR; in_lit] | (rewrite H2; reflexivity)].
  - eapply POSTM_trans; [exact PM1|]. eapply (POSTM_range C A M1 _ m4); [exact CK | exact HW1 | exact OUT4 | lia | lia | lia].
  - exact A10.
Qed.

Theorem pixFHMTGen_1_W : pixFHMTGen_1_contract.
Proof.
  unfold pixFHMTGen_1_contract.
  intros C A m md regs s pixs w h cm datas name j cv ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 H12 PXs HOK Hw Hh Lps Lds HCM Hj HNM kR bR Hrm Hrk Hrb HK.
  replace (Z_to_bv 64 PC_pixFHMTGen_1) with (0x283dc : word) by (apply bv_eq; reflexivity).
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold FHG_STACK, LSF in *.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof HOK as (DV & Hw2 & Hh2 & Hsz). pose proof (wpl_of_range (w + 64) 1 ltac:(lia) DV) as Hwpl.
  assert (Hwpl1 : (1 <= wpl_of (w + 64) 1 <= 627)%Z).
  { rewrite wpl_of_1 by lia. split; [apply Z.div_le_lower_bound; lia | enough ((w + 64 + 31) / 32 < 628)%Z by lia; apply Z.div_lt_upper_bound; lia]. }
  set (wpl := wpl_of (w + 64) 1) in *. set (n := (4 * (wpl * (h + 64)))%Z) in *.
  assert (Hn : (0 <= wpl * (h + 64))%Z) by (apply Z.mul_nonneg_nonneg; lia).
  pose proof PXs as (Hs0 & Hs64' & WFs & _). pose proof (wf_data _ WFs) as Rds. cbn [p_data hdv] in Rds.
  destruct (blk_range C A m md (Z_to_bv 64 pixs) 64 CK HW Lps ltac:(lia)) as [Gps TOPps]. rewrite u_Z2bv in Gps, TOPps by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lps) as (_ & ALp16 & _). rewrite u_Z2bv in ALp16 by lia. pose proof (al16_mod8 _ ALp16) as AL8s.
  assert (Hn1 : (260 * wpl <= n)%Z) by (subst n; nia).
  destruct (blk_range C A m md (Z_to_bv 64 datas) n CK HW Lds ltac:(lia)) as [Gds TOPds]. rewrite u_Z2bv in Gds, TOPds by lia.
  assert (Hs96 : (96 <= s)%Z) by lia. assert (Hs64 : (s < 2 ^ 64)%Z) by lia.
  destruct HNM as ((Gn & TOPn & ALn) & Lnm & NZn & BAn).
  pose proof (hm_len j Hj) as LENj.
  (* [comment removed for export] *)
  destruct (fg_A al_rom regs m s 0 pixs name (hdv (w + 64) (h + 64) 1 cm datas) ret Hs96 Hs64 ltac:(lia) AL8s PXs eq_refl ltac:(lia)
              (W_sok_win C A m md (s - 96) 96 CK HW ltac:(lia) ltac:(cbn; lia)) H2 H1 H10 H11 H12)
    as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q8 & Q9 & Q18 & Q19 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |]. clear RUN1.
  assert (WP1 : W C A (FRG m s ret regs) md /\ POSTM C A s m (FRG m s ret regs)) by (unfold FRG; wp_win CK).
  destruct WP1 as [HW1 PM1]. set (M1 := FRG m s ret regs) in *.
  pose proof (cells_FRG m s ret regs Hs96 Hs64) as CE1. fold M1 in CE1.
  assert (OUT1 : forall x : word, ~ (s - 96 <= u x < s)%Z -> M1 x = m x) by (intros x Hx; subst M1; apply FRG_out; lia).
  assert (PXs1 : PIXat M1 pixs (hdv (w + 64) (h + 64) 1 cm datas)) by (apply (PIXat_frame m); [exact PXs | intros x Hx; apply OUT1; lia]).
  (* [comment removed for export] *)
  assert (HN1 : rd_str SEGS M1 name (hm_name j ++ [Z_to_bv 8 0])).
  { apply rd_str_bytes_at; [| lia | rewrite LENj; lia]. apply (bytes_at_frame m); [exact BAn | | lia | rewrite LENj; lia]. intros x Hx. apply OUT1. rewrite LENj in Hx. lia. }
  destruct (fg_search al_rom r1 M1 name j Hj ltac:(lia) ltac:(lia) HN1 (fun i Hi => W_selnames C A M1 md i HW1 Hi) Q1 Q10 Q11 Q18 Q19) as (r2 & RUN2 & P18 & AG2).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN2 |]. clear RUN2.
  (* [comment removed for export] *)
  destruct (fg_B al_rom r2 M1 pixs ltac:(csr; reflexivity) ltac:(csr; reflexivity)) as (r3 & RUN3 & V1 & V10 & AG3).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN3 |]. clear RUN3.
  assert (HCM1 : cm = 0%Z \/ (CMAPat M1 cm cv /\ cmap_ok cv /\ live A (Z_to_bv 64 cm) = Some 24%Z /\ live A (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z)).
  { destruct HCM as [CM0 | (CM & CMOK & Lcm & Larr)]; [left; exact CM0 | right]. split; [| split; [exact CMOK | split; [exact Lcm | exact Larr]]].
    pose proof CM as (Hc0 & Hc64 & _). destruct (blk_range C A m md (Z_to_bv 64 cm) 24 CK HW Lcm ltac:(lia)) as [Gcm TOPcm]. rewrite u_Z2bv in Gcm, TOPcm by lia.
    apply (CMAPat_frame m); [exact CM|]. intros x Hx. apply OUT1. lia. }
  apply (pixCreateTemplate_W C A M1 md r3 (s - 96) pixs (w + 64) (h + 64) 1 cm datas cv (Z_to_bv 64 0x285e8) S CK HW1 ltac:(csr; reflexivity)
           ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold PCT_STACK, LSF; lia) ltac:(lia) V1 ltac:(red; apply bv_eq; reflexivity)
           ltac:(csr; reflexivity) V10 PXs1 HOK ltac:(lia) ltac:(lia) Lps HCM1 kR bR Hrm Hrk Hrb).
  unfold TKt. intros A1 m2 vm1 r4 HWa CSa PMa OUTa Hrm1.
  replace (Z_to_bv 64 0x285e8) with (0x285e8 : word) by (apply bv_eq; reflexivity).
  pose proof (cellsG_frm C (s - 96) M1 m2 s ret regs CK (proj1 PMa) ltac:(lia) ltac:(lia) Hs96 Hs64 CE1) as CE2.
  assert (PMa' : POSTM C A s m m2) by (eapply POSTM_trans; [exact PM1 | eapply POSTM_mono; [|exact PMa]; lia]).
  destruct OUTa as [[Hres0 LIVEQ] | (pixd & cd & data & Hres & PT)].
  - (* [comment removed for export] *)
    destruct (fg_F al_rom r4 regs m2 s ret Hs96 Hs64 (W_sev_got C A1 m2 _ HWa) (W_sev C A1 m2 _ HWa) CE2 ltac:(csr; reflexivity) Hres0)
      as (r5 & RUN5 & X2 & X1 & X10 & X11 & X12 & XR & AG5).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN5 |]. clear RUN5.
    apply (returnErrorPtr_W C A1 m2 _ r5 s 0x1054a 0x108aa 13 12 ret (Z_to_bv 64 0) S CK HWa X2 Hs16 ltac:(unfold LSF; lia) Hhi X1 Hret
             X10 X11 X12 str_msg_pixd str_pixFHMTGen_1).
    intros m4 r6 HW4 OUT4 GR4 CS4 A10. unfold LSF in OUT4.
    apply (HK A1 m4 vm1 r6 HW4).
    + apply cs_kept_intro; csr; first [reflexivity | solve [apply XR; in_lit] | (rewrite H2; reflexivity)].
    + eapply POSTM_trans; [exact PMa'|]. apply (POSTM_sub C A A1); [apply sub_live_eq; exact LIVEQ|].
      eapply (POSTM_range C A1 m2 _ m4); [exact CK | exact HWa | exact OUT4 | lia | lia | lia].
    + left. split; [exact A10 | exact LIVEQ].
    + exact Hrm1.
  - (* [comment removed for export] *)
    pose proof PT as (Gp & TOPp & ALp & Gd & TOPd & ALd & NEpd & L0p & L0d & L00p & L00d & L1p & L1d & PXd & CMR). fold wpl in TOPd, L1d. fold n in TOPd, L1d.
    assert (SUBa : sub_live A A1).
    { intros q k Lq. destruct CMR as [[_ LEQ] | (ad & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LAcd & LAad & _ & _ & _ & _ & _ & LEQ)].
      - rewrite LEQ; [exact Lq | intros ->; congruence | intros ->; congruence].
      - rewrite LEQ; [exact Lq | intros ->; congruence | intros ->; congruence | intros ->; congruence | intros ->; congruence]. }
    assert (NEsp : pixs <> pixd) by (intros E; rewrite E in Lps; rewrite Lps in L0p; discriminate).
    assert (NEdd : Z_to_bv 64 datas <> Z_to_bv 64 data) by (intros E; rewrite E in Lds; rewrite Lds in L0d; discriminate).
    assert (PXs2 : PIXat m2 pixs (hdv (w + 64) (h + 64) 1 cm datas)).
    { apply (PIXat_frame M1); [exact PXs1|]. intros x Hx. exact (LIVK_at A M1 m2 pixs 64 x (proj2 PMa) Lps ltac:(lia) ltac:(lia) Hx). }
    destruct (fg_C al_rom r4 m2 pixs pixd j (hdv (w + 64) (h + 64) 1 cm datas) (hdv (w + 64) (h + 64) 1 cd data) ltac:(lia) ltac:(lia) AL8s (al16_mod8 _ ALp) NEsp PXs2 PXd
                ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; fold wpl; lia) ltac:(cbn; fold wpl; lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; fold wpl; lia) ltac:(cbn; fold wpl; lia)
                Hres ltac:(csr; reflexivity) ltac:(csr; reflexivity))
      as (r5 & RUN5 & X1 & X8 & X10 & X11 & X12 & X13 & X14 & X15 & X16 & AG5). cbn [p_data p_wpl p_w p_h hdv] in X10, X11, X12, X13, X14, X15. fold wpl in X10, X13, X14, X15.
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN5 |]. clear RUN5.
    replace (w + 64 - 64)%Z with w in X11 by lia. replace (h + 64 - 64)%Z with h in X12 by lia.
    replace (0x287f8 : word) with (Z_to_bv 64 PC_fhmtgen_low_1) by (apply bv_eq; reflexivity).
    apply (DWA C A A1 m2 _ r5 (s - 96)%Z datas data w h j (Z_to_bv 64 0x286ec) S CK HWa SUBa ltac:(csr; reflexivity)
             ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold DWA_STACK; lia) ltac:(lia) X1 ltac:(red; apply bv_eq; reflexivity)
             X10 X11 X12 X13 X14 X15 X16 ltac:(lia) Hw Hh HOK ltac:(lia) ltac:(lia) (SUBa _ _ Lds) L1d L0d L00d NEdd).
    intros m5 r6 HW5 CS5 PM5 FP5 A10_5.
    replace (Z_to_bv 64 0x286ec) with (0x286ec : word) by (apply bv_eq; reflexivity).
    pose proof (cellsG_frm C (s - 96) m2 m5 s ret regs CK (proj1 PM5) ltac:(lia) ltac:(lia) Hs96 Hs64 CE2) as CE5.
    destruct (fg_D al_rom r6 regs m5 s pixd ret Hs96 Hs64 Hret CE5 ltac:(csr; reflexivity) ltac:(csr; reflexivity)) as (r7 & RUN7 & Z2 & Z1 & Z10 & ZR & AG7).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW5)) | exact (mp_lazy _ (w_pure _ _ _ _ HW5)) | exact RUN7 |]. clear RUN7.
    apply (HK A1 m5 vm1 r7 HW5).
    + apply cs_kept_intro; first [solve [apply ZR; in_lit] | (csr; reflexivity)].
    + eapply POSTM_trans; [exact PMa' | eapply POSTM_mono; [|exact PM5]; lia].
    + right. exists pixd, cd, data. split; [exact Z10|].
      apply (pixt_new_frame C A A1 m2 _ m5 (s - 96 - DWA_STACK) (s - 96) pixd (w + 64) (h + 64) 1 cd data cv CK HWa ltac:(unfold DWA_STACK; lia) ltac:(fold wpl; lia) PT).
      intros a Ha1 Ha2. apply FP5; [exact Ha1 | unfold dwa_rbytes; exact Ha2].
    + exact Hrm1.
Qed.

End FhmtW.
