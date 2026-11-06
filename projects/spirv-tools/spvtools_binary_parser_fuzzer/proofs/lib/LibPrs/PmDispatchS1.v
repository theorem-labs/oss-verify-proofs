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
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac WalkTac StartupTac SumWalkTac StoreOk MemSplit Hoare ShapeAlg
  SRealizes RefMemcpyLib RefReadLib FPSteps LibIface LibBudget LibEff MmapSim LibMaskBits
  ZStores SymExec3 SymExec3Sound SymRun3 S1Layout.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContLib StrLib LiveStats ContStmts S1Facts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts HCommon HLib HConstsS1.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsNeeds PrsInv PrsStmts PmBase PmHyps PmCoreS1 PmStepS1. Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep2S1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep2S1.PmUpd. From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PmStep2S1 PmLoopS1 PmBody1S1 PmStep3S1 PmODefsS1 PmZw PmOLoopS1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Abbreviation SEGS := Plain.M.loaded_segments.

Module Ly := S1Layout.

Section PM.
Context {AC : AllocCeiling}.
  Context {MI : MallocIface SEGS Ly.L} {ST : StaticsIface SEGS Ly.L}.
  Context {G : grammar} {idesc : Z -> Z -> Prop} {odesc edesc : Z -> Z -> Z -> Prop}
          {generates_type is_ext_inst is_nonsemantic : Z -> bool}
          {ds_rep : AS MI -> mem -> Z -> Z -> Z -> list (Z * Z) -> Prop}.
  Variable CL : pm_callees SEGS Ly.L MI ST G tcS1 dcS1 nfcS1 HConstsS1.hc ccS1 kcS1
                  idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep.

  #[local] Notation PMX := (PmBase.PMX MI ST).
  #[local] Notation cfg fx R pc M model := (mkCfg (@mkst fx R (Z_to_bv 64 pc) M (seg_rom SEGS)) model).
  #[local] Notation DL := (cl_ds_laws _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
  #[local] Notation pm_exit := (PmCoreS1.pm_exit MI ST).
  #[local] Notation pmx_ds_room := (PmStepS1.pmx_ds_room CL).
  #[local] Notation pm_tail_68410 := (PmStepS1.pm_tail_68410 CL).
  #[local] Notation cregs_kept := (PmStepS1.cregs_kept CL).
  #[local] Notation pm_put_cstr := (PmStepS1.pm_put_cstr CL).
  #[local] Notation pm_put_num := (PmStepS1.pm_put_num CL).
  #[local] Notation pm_put_u16 := (PmStepS1.pm_put_u16 CL).
  #[local] Notation pm_put_u32 := (PmStepS1.pm_put_u32 CL).
  #[local] Notation pm_put_u64 := (PmStepS1.pm_put_u64 CL).
  #[local] Notation pm_put_int := (PmStepS1.pm_put_int CL).
  #[local] Notation pm_ctor := (PmStepS1.pm_ctor CL).
  #[local] Notation pm_pdiag := (PmStepS1.pm_pdiag CL).
  #[local] Notation pm_pdiag0 := (PmStepS1.pm_pdiag0 CL).
  #[local] Notation pm_pdiagE := (PmStepS1.pm_pdiagE CL).
  #[local] Notation pm_dtor := (PmStepS1.pm_dtor CL).
  #[local] Notation pm_exhausted := (PmStepS1.pm_exhausted CL).
  #[local] Notation pm_fixword := (PmStepS1.pm_fixword CL).
  #[local] Notation pm_is_host_endian := (PmStepS1.pm_is_host_endian CL).
  #[local] Notation pm_binend := (PmStepS1.pm_binend CL).
  #[local] Notation pm_ecw_pb := (PmStep2S1.pm_ecw_pb CL).
  #[local] Notation pm_opcode_split := (PmStep2S1.pm_opcode_split CL).
  #[local] Notation pm_lookup_opcode := (PmStep2S1.pm_lookup_opcode CL).
  #[local] Notation pm_lookup_operand := (PmStep2S1.pm_lookup_operand CL).
  #[local] Notation pm_lookup_ext := (PmStep2S1.pm_lookup_ext CL).
  #[local] Notation pm_idesc_operands := (PmStep3S1.pm_idesc_operands CL).
  #[local] Notation pm_odesc_operands := (PmStep3S1.pm_odesc_operands CL).
  #[local] Notation pm_edesc_operands := (PmStep3S1.pm_edesc_operands CL).
  #[local] Notation pm_push_types := (PmStep3S1.pm_push_types CL).
  #[local] Notation pm_take_first := (PmStep3S1.pm_take_first CL).
  #[local] Notation pm_X1 := (PmOLoopS1.pm_X1 CL).
  #[local] Notation pm_opnd_pb := (PmOLoopS1.pm_opnd_pb CL).
  #[local] Notation pm_copy_loop := (PmOLoopS1.pm_copy_loop CL).
  #[local] Notation pm_push_tail := (PmOLoopS1.pm_push_tail CL).

  #[local] Notation izero := (PmBody1S1.izero).
  #[local] Notation ictx := (PmBody1S1.ictx).
  #[local] Notation nodes := (PmLoopS1.nodes).
  #[local] Notation macct := (PmLoopS1.macct).
  #[local] Notation ipure := (PmODefsS1.ipure (G:=G) (idesc:=idesc)).
  #[local] Notation arm_stmt := (PmODefsS1.arm_stmt (MI:=MI) (ST:=ST) (G:=G) (idesc:=idesc)).

  Definition ARM_TABLE : list Z :=
    [0x67308; 0x67574; 0x675b8; 0x67348; 0x67348; 0x67420; 0x67528; 0x67430; 0x67390; 0x67580; 0x672cc; 0x67618; 0x66f38; 0x66f38; 0x66f38; 0x66f38; 0x66f38; 0x66f38; 0x66f38; 0x66f38; 0x66f38; 0x676b4; 0x676b4; 0x66f38; 0x66f38; 0x66f38; 0x66f38; 0x66f38; 0x66f38; 0x66f38; 0x66f38; 0x66f38; 0x66f38; 0x66f38; 0x66f50; 0x66f50; 0x66f50; 0x66f50; 0x66f50; 0x66f50; 0x676b4; 0x67308; 0x66f50; 0x66f50; 0x67420; 0x676b4; 0x67390; 0x672cc; 0x66f38; 0x676b4; 0x66f38; 0x676b4; 0x676b4; 0x676b4; 0x676b4; 0x66f50; 0x66f38; 0x66f38; 0x66f38; 0x66f38; 0x66f50; 0x66f38; 0x66f38; 0x66f38; 0x66f38; 0x66f38; 0x66f38; 0x66f38; 0x66f38; 0x66f38; 0x66f38; 0x66f38; 0x66f38; 0x66f38; 0x66f38; 0x66f38; 0x66f50; 0x66f50; 0x676b4; 0x676b4; 0x676b4; 0x66f38; 0x66f38; 0x66f38; 0x66f38; 0x676b4; 0x66f50; 0x676b4; 0x66f50; 0x66f50; 0x66f50; 0x66f50; 0x676b4; 0x676b4; 0x676b4; 0x676b4; 0x676b4; 0x676b4; 0x676b4; 0x676b4; 0x676b4; 0x676b4; 0x66f50; 0x66f50; 0x66f38; 0x676b4; 0x66f38].

  Definition arm_pc (t : Z) : Z := if ((1 <=? t) && (t <=? 107))%bool then nth (Z.to_nat (t - 1)) ARM_TABLE 0x676b4 else 0x676b4.

  Lemma rodata_kimg : forall (w : pmw MI ST) A M model c E (lo hi : Z),
    PMX w A M model c -> 0x10000 <= lo -> hi <= 0xe6000 -> kentry_ok SEGS E M (KImg lo hi).
  Proof using AC MI ST.
    intros w A M model c E lo hi X Hlo Hhi. apply kimg_abs; [lia | lia |]. intros i Hi.
    apply (ro_clear_at _ M i (x_roc X)); [lia|]. unfold ro_addr. cbn [ly_img ly_rw ly_relro Ly.L]. rewrite !in_ranges_1. lia.
  Qed.

  Definition ARM_PCS : list Z :=
    [0x67308; 0x67574; 0x675b8; 0x67348; 0x67420; 0x67528; 0x67430; 0x67390; 0x67580; 0x672cc; 0x67618; 0x66f38; 0x66f50; 0x676b4].

  Ltac disp1 w A M model c R X CONT Qa0 Q21 :=
    lazymatch type of Q21 with getr _ _ = Z_to_bv 64 ?tv =>
    let E := fresh "E" in let HR := fresh "HR" in let HK := fresh "HK" in
    pm_seed R w c [getr R 10%bv];
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (10%bv, EVar 39); (21%bv, ELit tv)] R; seedHK HK w A M model c E X;
    apply (know_more E M [KImg 0x14694 0x14840]) in HK;
    [ xruns HR HK 100%nat (ARM_PCS ++ STOPS) (SCR [] [] []) 50%N; [ split_scs; try sc_auto1 |];
      postrun;
      let HRn := fresh "HRn" in let R1 := fresh "R1" in
      name_run HRn R1;
      let G2 := fresh "G2" in let G3 := fresh "G3" in let G4 := fresh "G4" in let G8 := fresh "G8" in let G9 := fresh "G9" in
      let G18 := fresh "G18" in let G21 := fresh "G21" in let G22 := fresh "G22" in let G23 := fresh "G23" in let G25 := fresh "G25" in let GS := fresh "GS" in
      rreg HRn (2%bv) G2; rreg HRn (3%bv) G3; rreg HRn (4%bv) G4; rreg HRn (8%bv) G8; rreg HRn (9%bv) G9; rreg HRn (18%bv) G18;
      rreg HRn (21%bv) G21; rreg HRn (22%bv) G22; rreg HRn (23%bv) G23; rreg HRn (25%bv) G25;
      pose proof (syms_id_sound _ _ _ _ OSREGS HRn eq_refl) as GS;
      clear HRn HR HK; fixregs;
      replace (Z_to_bv 5 (Z.of_N 18)) with (18%bv : reg) in G18 by (apply bv_eq; reflexivity);
      replace (Z_to_bv 5 (Z.of_N 22)) with (22%bv : reg) in G22 by (apply bv_eq; reflexivity);
      replace (Z_to_bv 5 (Z.of_N 23)) with (23%bv : reg) in G23 by (apply bv_eq; reflexivity);
      replace (Z_to_bv 5 (Z.of_N 25)) with (25%bv : reg) in G25 by (apply bv_eq; reflexivity);
      rewrite ?Qa0;
      eapply (CONT R1 ltac:(eapply (oregs_glue w R R1); [eassumption | exact GS | exact G2 | exact G3 | exact G4 | exact G8 | left; exact G9]));
      [rewrite G18; exact Qa0 | exact G21 | exact G22 | exact G23 | exact G25]
    | repeat apply Forall_cons; try apply Forall_nil; eapply (rodata_kimg w); [exact X | lia | lia] ]
    end.

  Lemma In_range_enum : forall t lo n, lo <= t < lo + Z.of_nat n -> In t (map (fun k => lo + Z.of_nat k) (seq 0 n)).
  Proof using.
    intros t lo n H. apply in_map_iff. exists (Z.to_nat (t - lo)). split; [lia|]. apply in_seq. lia.
  Qed.

  Lemma pm_dispatch : forall (w : pmw MI ST) A M model c (fx : FPState) R (t r : Z) K,
    PMX w A M model c -> oregs w R ->
    getr R 10%bv = Z_to_bv 64 (PrsNeeds.sx32 r) -> 0 <= r < 2 ^ 32 -> getr R 21%bv = Z_to_bv 64 t -> 0 <= t < 2 ^ 32 ->
    (forall R', oregs w R' -> getr R' 18%bv = Z_to_bv 64 (PrsNeeds.sx32 r) -> getr R' 21%bv = Z_to_bv 64 t -> getr R' 22%bv = getr R 22%bv ->
                getr R' 23%bv = getr R 23%bv -> getr R' 25%bv = getr R 25%bv ->
                srealizes SEGS (cfg fx R' (arm_pc t) (wbytes M (Z_to_bv 64 (w_sp w + 680)) (word_to_le_bytes 4 (Z_to_bv 64 r))) model) K) ->
    srealizes SEGS (cfg fx R 0x66f08 M model) K.
  Proof using AC MI ST.
    intros w A M model c fx R t r K X OR Qa0 Hr Q21 Ht CONT.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & Gc2 & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof OR as OR'. destruct OR' as (Qsp & Qgp & Qtp & Qs0 & Qs1 & Qs3 & Qs4 & Qs8).
    rewrite <- (PmBody1S1.w2lb4_sx32 r) in CONT by lia.
    destruct (Z.lt_ge_cases t 108) as [Hlo|Hhi].
    2: {
         pm_seed R w c [Z_to_bv 64 t; getr R 10%bv].
         seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (10%bv, EVar 40); (21%bv, EVar 39)] R. seedHK HK w A M model c E X.
         apply (know_more E M [KRange (EVar 39) 108 (2 ^ 32)]) in HK.
         2: { repeat apply Forall_cons; try apply Forall_nil. eapply krange_var; [evs; reflexivity | lia | lia]. }
         xruns HR HK 100%nat (ARM_PCS ++ STOPS) (SCR [true] [] []) 50%N.
         { split_scs; try sc_auto1. all: cbn [sc_denot]; evs; rewrite ?w_addm by lia; rewrite ?br_ltu by lia; bool_lia. }
         postrun. name_run HRn R1.
         rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (9%bv) G9. rreg HRn (18%bv) G18.
         rreg HRn (21%bv) G21. rreg HRn (22%bv) G22. rreg HRn (23%bv) G23. rreg HRn (25%bv) G25.
         pose proof (syms_id_sound _ _ _ _ OSREGS HRn eq_refl) as GS.
         clear HRn HR HK. fixregs.
         replace (Z_to_bv 5 (Z.of_N 18)) with (18%bv : reg) in G18 by (apply bv_eq; reflexivity).
         replace (Z_to_bv 5 (Z.of_N 22)) with (22%bv : reg) in G22 by (apply bv_eq; reflexivity).
         replace (Z_to_bv 5 (Z.of_N 23)) with (23%bv : reg) in G23 by (apply bv_eq; reflexivity).
         replace (Z_to_bv 5 (Z.of_N 25)) with (25%bv : reg) in G25 by (apply bv_eq; reflexivity).
         unfold arm_pc in CONT. replace ((1 <=? t) && (t <=? 107))%bool with false in CONT by (symmetry; apply Bool.andb_false_intro2; apply Z.leb_gt; lia).
         rewrite Qa0. eapply (CONT R1 ltac:(eapply (oregs_glue w R R1); [eassumption | exact GS | exact G2 | exact G3 | exact G4 | exact G8 | left; exact G9]));
           [rewrite G18; exact Qa0 | exact G21 | exact G22 | exact G23 | exact G25]. }
    destruct (Z.lt_ge_cases t 1) as [H0|H1].
    { assert (t = 0) by lia. subst t. disp1 w A M model c R X CONT Qa0 Q21. }
    pose proof (In_range_enum t 1 107 ltac:(lia)) as HIn. cbn -[Z.add] in HIn. rewrite ?Z.add_0_r in HIn. cbn in HIn.
    repeat match type of HIn with
           | _ \/ _ => destruct HIn as [HIn|HIn]; [subst t; disp1 w A M model c R X CONT Qa0 Q21 |]
           | False => destruct HIn
           end.
  Qed.
End PM.
