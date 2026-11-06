(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require list.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac WalkTac StartupTac SumWalkTac StoreOk MemSplit Hoare ShapeAlg
  SRealizes RefMemcpyLib RefReadLib FPSteps LibIface LibBudget LibEff MmapSim LibMaskBits
  ZStores SymExec3 SymExec3Sound SymRun3 U1Layout.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContLib StrLib LiveStats ContStmts ContStmts2 U1Facts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts HStmtsU1 HCommonU1 HLib HConstsU1.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsNeeds PrsInv PrsStmts PmBaseU1 PmHyps PmHypsU1 PmCoreU1 PmStepU1. Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep2U1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep2U1.PmUpdU1. From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PmStep2U1 PmLoopU1 PmInstU1 PmStep3U1 PmODefsU1 PmZw.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Abbreviation SEGS := Ubsan.M.loaded_segments.

Module Ly := U1Layout.

Section PM.
Context {AC : AllocCeiling}.
  Context {MI : MallocIface SEGS Ly.L} {ST : StaticsIface SEGS Ly.L}.

  #[local] Notation PMX := (PmBaseU1.PMX MI ST).
  #[local] Notation cfg fx R pc M model := (mkCfg (@mkst fx R (Z_to_bv 64 pc) M (seg_rom SEGS)) model).

  Definition ARM_TABLE : list Z :=
    [0x67bc4; 0x67dd8; 0x67e1c; 0x67c18; 0x67c18; 0x67cf8; 0x67d74; 0x67d08; 0x67c64; 0x67de4; 0x67b50; 0x67e7c; 0x678c0; 0x678c0; 0x678c0; 0x678c0; 0x678c0; 0x678c0; 0x678c0; 0x678c0; 0x678c0; 0x6812c; 0x6812c; 0x678c0; 0x678c0; 0x678c0; 0x678c0; 0x678c0; 0x678c0; 0x678c0; 0x678c0; 0x678c0; 0x678c0; 0x678c0; 0x678d8; 0x678d8; 0x678d8; 0x678d8; 0x678d8; 0x678d8; 0x6812c; 0x67bc4; 0x678d8; 0x678d8; 0x67cf8; 0x6812c; 0x67c64; 0x67b50; 0x678c0; 0x6812c; 0x678c0; 0x6812c; 0x6812c; 0x6812c; 0x6812c; 0x678d8; 0x678c0; 0x678c0; 0x678c0; 0x678c0; 0x678d8; 0x678c0; 0x678c0; 0x678c0; 0x678c0; 0x678c0; 0x678c0; 0x678c0; 0x678c0; 0x678c0; 0x678c0; 0x678c0; 0x678c0; 0x678c0; 0x678c0; 0x678c0; 0x678d8; 0x678d8; 0x6812c; 0x6812c; 0x6812c; 0x678c0; 0x678c0; 0x678c0; 0x678c0; 0x6812c; 0x678d8; 0x6812c; 0x678d8; 0x678d8; 0x678d8; 0x678d8; 0x6812c; 0x6812c; 0x6812c; 0x6812c; 0x6812c; 0x6812c; 0x6812c; 0x6812c; 0x6812c; 0x6812c; 0x678d8; 0x678d8; 0x678c0; 0x6812c; 0x678c0].

  Definition arm_pc (t : Z) : Z := if ((1 <=? t) && (t <=? 107))%bool then nth (Z.to_nat (t - 1)) ARM_TABLE 0x6812c else 0x6812c.

  Lemma rodata_kimg : forall (w : pmw MI ST) A M model c E (lo hi : Z),
    PMX w A M model c -> 0x10000 <= lo -> hi <= 0xe8000 -> kentry_ok SEGS E M (KImg lo hi).
  Proof using AC MI ST.
    intros w A M model c E lo hi X Hlo Hhi. apply kimg_abs; [lia | lia |]. intros i Hi.
    apply (ro_clear_at _ M i (x_roc X)); [lia|]. unfold ro_addr. cbn [ly_img ly_rw ly_relro Ly.L]. rewrite !in_ranges_1. lia.
  Qed.

  Definition ARM_PCS : list Z :=
    [0x678c0; 0x678d8; 0x67b50; 0x67bc4; 0x67c18; 0x67c64; 0x67cf8; 0x67d08; 0x67d74; 0x67dd8; 0x67de4; 0x67e1c; 0x67e7c; 0x6812c].

  Ltac oregs_seeded HRn Qgp Qtp :=
    let G2 := fresh in let G3 := fresh in let G4 := fresh in let G8 := fresh in let G9 := fresh in
    let G18 := fresh in let G19 := fresh in let G20 := fresh in let G21 := fresh in let G25 := fresh in
    rreg HRn 2%bv G2; rreg HRn 3%bv G3; rreg HRn 4%bv G4; rreg HRn 8%bv G8; rreg HRn 9%bv G9;
    rreg HRn 18%bv G18; rreg HRn 19%bv G19; rreg HRn 20%bv G20; rreg HRn 21%bv G21; rreg HRn 25%bv G25;
    unfold oregs, loop_regs; rewrite G2, G3, G4, G8, G9, G18, G19, G20, G21, G25; fixregs; rewrite ?Qgp, ?Qtp;
    rewrite ?SymExec.alu64_add_lit; repeat split; reflexivity.
  #[local] Notation OREGSEED := [(9%bv, EAlu ALU_ADD (EVar 33) (ELit 88)); (18%bv, ELit 1); (19%bv, ELit (2 ^ 61)); (20%bv, ELit 20); (21%bv, EAlu ALU_ADD (EVar 33) (ELit 264)); (25%bv, ELit 5)]%list.

  Ltac disp1 w A M model c R X CONT Qa0 Q27 OR :=
    lazymatch type of Q27 with getr _ _ = Z_to_bv 64 ?tv =>
    let E := fresh "E" in let HR := fresh "HR" in let HK := fresh "HK" in
    pm_seed R w c [getr R 10%bv];
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (10%bv, EVar 39); (27%bv, ELit tv)] R;
    seedHK HK w A M model c E X;
    apply (know_more E M [KImg 0x14694 0x14840]) in HK;
    [ xruns HR HK 40%nat (ARM_PCS ++ STOPS) (SCR [] [] []) 20%N; [ split_scs; try sc_auto1 |];
      postrun;
      let HRn := fresh "HRn" in let R1 := fresh "R1" in
      name_run HRn R1;
      let G2 := fresh "G2" in let G3 := fresh "G3" in let G4 := fresh "G4" in let G8 := fresh "G8" in
      let G22 := fresh "G22" in let G23 := fresh "G23" in let G24 := fresh "G24" in let G26 := fresh "G26" in let G27 := fresh "G27" in
      let GS := fresh "GS" in
      rreg HRn (2%bv) G2; rreg HRn (3%bv) G3; rreg HRn (4%bv) G4; rreg HRn (8%bv) G8;
      rreg HRn (22%bv) G22; rreg HRn (23%bv) G23; rreg HRn (24%bv) G24; rreg HRn (26%bv) G26; rreg HRn (27%bv) G27;
      pose proof (syms_id_sound _ _ _ _ PmInstU1.SREGS HRn eq_refl) as GS;
      clear HRn HR HK; fixregs;
      replace (Z_to_bv 5 (Z.of_N 22)) with (22%bv : reg) in G22 by (apply bv_eq; reflexivity);
      replace (Z_to_bv 5 (Z.of_N 23)) with (23%bv : reg) in G23 by (apply bv_eq; reflexivity);
      replace (Z_to_bv 5 (Z.of_N 24)) with (24%bv : reg) in G24 by (apply bv_eq; reflexivity);
      replace (Z_to_bv 5 (Z.of_N 26)) with (26%bv : reg) in G26 by (apply bv_eq; reflexivity);
      rewrite ?Qa0;
      eapply (CONT R1 ltac:(eapply (PmInstU1.loop_regs_glue w R R1); [exact OR | exact GS | exact G2 | exact G3 | exact G4 | exact G8]));
      [rewrite G22; exact Qa0 | exact G27 | exact G23 | exact G24 | exact G26]
    | repeat apply Forall_cons; try apply Forall_nil; eapply (rodata_kimg w); [exact X | lia | lia] ]
    end.

  Lemma In_range_enum : forall t lo n, lo <= t < lo + Z.of_nat n -> In t (map (fun k => lo + Z.of_nat k) (seq 0 n)).
  Proof using.
    intros t lo n H. apply in_map_iff. exists (Z.to_nat (t - lo)). split; [lia|]. apply in_seq. lia.
  Qed.

  Lemma pm_dispatch : forall (w : pmw MI ST) A M model c (fx : FPState) R (t r : Z) K,
    PMX w A M model c -> oregs w R ->
    getr R 10%bv = Z_to_bv 64 (PrsNeeds.sx32 r) -> 0 <= r < 2 ^ 32 -> getr R 27%bv = Z_to_bv 64 t -> 0 <= t < 2 ^ 32 ->
    (forall R', oregs w R' -> getr R' 22%bv = Z_to_bv 64 (PrsNeeds.sx32 r) -> getr R' 27%bv = Z_to_bv 64 t -> getr R' 23%bv = getr R 23%bv ->
                getr R' 24%bv = getr R 24%bv -> getr R' 26%bv = getr R 26%bv ->
                srealizes SEGS (cfg fx R' (arm_pc t) (wbytes M (Z_to_bv 64 (w_sp w + 712)) (word_to_le_bytes 4 (Z_to_bv 64 r))) model) K) ->
    srealizes SEGS (cfg fx R 0x67890 M model) K.
  Proof using AC MI ST.
    intros w A M model c fx R t r K X OR Qa0 Hr Q27 Ht CONT.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & [Gc2 Gcal] & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof OR as OR'. destruct OR' as (Qsp & Qgp & Qtp & Qs0 & Qs1 & Qs2 & Qs3 & Qs4 & Qs5 & Qs9).
    rewrite <- (PmInstU1.w2lb4_sx32 r) in CONT by lia.
    destruct (Z.lt_ge_cases t 108) as [Hlo|Hhi].
    2: {
         pm_seed R w c [Z_to_bv 64 t; getr R 10%bv; getr R 23%bv; getr R 24%bv; getr R 26%bv].
         seedHR HR E ([(2%bv, EVar 32); (8%bv, EVar 33); (10%bv, EVar 40); (27%bv, EVar 39); (23%bv, EVar 41); (24%bv, EVar 42); (26%bv, EVar 43)] ++ OREGSEED)%list R.
         seedHK HK w A M model c E X.
         apply (know_more E M [KRange (EVar 39) 108 (2 ^ 32)]) in HK.
         2: { repeat apply Forall_cons; try apply Forall_nil. eapply krange_var; [evs; reflexivity | lia | lia]. }
         xruns HR HK 100%nat (ARM_PCS ++ STOPS) (SCR [true] [] []) 50%N.
         { split_scs; try sc_auto1. all: cbn [sc_denot]; evs; rewrite ?w_addm by lia; rewrite ?br_ltu by lia; bool_lia. }
         postrun. name_run HRn R1.
         rreg HRn (22%bv) G22. rreg HRn (23%bv) G23. rreg HRn (24%bv) G24. rreg HRn (26%bv) G26. rreg HRn (27%bv) G27.
         assert (OR1 : oregs w R1) by (oregs_seeded HRn Qgp Qtp). clear HRn HR HK.
         unfold arm_pc in CONT. replace ((1 <=? t) && (t <=? 107))%bool with false in CONT by (symmetry; apply Bool.andb_false_intro2; apply Z.leb_gt; lia).
         rewrite Qa0. eapply (CONT R1 OR1); [rewrite G22; exact Qa0 | exact G27 | exact G23 | exact G24 | exact G26]. }
    destruct (Z.lt_ge_cases t 1) as [H0|H1].
    { assert (t = 0) by lia. subst t. disp1 w A M model c R X CONT Qa0 Q27 OR. }
    pose proof (In_range_enum t 1 107 ltac:(lia)) as HIn. cbn -[Z.add] in HIn. rewrite ?Z.add_0_r in HIn. cbn in HIn.
    repeat match type of HIn with
           | _ \/ _ => destruct HIn as [HIn|HIn]; [subst t; disp1 w A M model c R X CONT Qa0 Q27 OR |]
           | False => destruct HIn
           end.
  Qed.
End PM.
