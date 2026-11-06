(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From stdpp Require list.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Ubsan.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PropExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SeqExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StepTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.WalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StartupTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SumWalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StoreOk OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MemSplit OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Hoare OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ShapeAlg OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SRealizes OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefReadLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.FPSteps OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibIface OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibBudget OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibEff OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MmapSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibMaskBits OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ZStores OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3Sound OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymRun3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.U1Layout.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.CRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.StrLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.LiveStats OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContStmts2 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.U1Facts.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRepFacts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HStmtsU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HCommonU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HFpu OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HConstsU1.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsNeeds OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsInv OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmBaseU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmHyps OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmHypsU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmCoreU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStepU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep2U1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep3U1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmLoopU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmInstU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmODefsU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmZw OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmBody1U1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmExitDiagU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep5U1.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PeLia.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Module PmExitAU1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.

Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PropExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SeqExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StepTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.WalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StartupTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SumWalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StoreOk OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MemSplit OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Hoare OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ShapeAlg OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SRealizes OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefReadLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.FPSteps OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibIface OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibBudget OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibEff OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MmapSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibMaskBits OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ZStores OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3Sound OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymRun3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.U1Layout.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.CRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.StrLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.LiveStats OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContStmts2 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.U1Facts.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRepFacts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HStmtsU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HCommonU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HFpu OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HConstsU1.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsNeeds OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsInv OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmBaseU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmHyps OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmHypsU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmCoreU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStepU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep2U1.PmUpdU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep2U1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep3U1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmLoopU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmInstU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmODefsU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmZw OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmBody1U1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmExitDiagU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep5U1.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PeLia.
Local Ltac lia ::= pe_lia.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Abbreviation SEGS := Ubsan.M.loaded_segments.
Module Ly := U1Layout.

Section PM.
Context {AC : AllocCeiling}.
  Context {MI : MallocIface SEGS Ly.L} {ST : StaticsIface SEGS Ly.L}.
  Context {G : grammar} {idesc : Z -> Z -> Prop} {odesc edesc : Z -> Z -> Z -> Prop}
          {generates_type is_ext_inst is_nonsemantic : Z -> bool}
          {ds_rep : AS MI -> mem -> Z -> Z -> Z -> list (Z * Z) -> Prop}.
  Variable CL : pm_calleesU1 SEGS Ly.L MI ST G tcU1 dcU1 nfcU1 HConstsU1.hc ccU1 kcU1
                  idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep.

  #[local] Notation PMX := (PmBaseU1.PMX MI ST).
  #[local] Notation cfg fx R pc M model := (mkCfg (@mkst fx R (Z_to_bv 64 pc) M (seg_rom SEGS)) model).
  #[local] Notation DL := (cu_ds_laws _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
  #[local] Notation IDP := (cu_idesc_ptr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
  #[local] Notation ODP := (cu_odesc_ptr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
  #[local] Notation GOK := (cu_G _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
  #[local] Notation pm_fixword := (PmStepU1.pm_fixword CL).
  #[local] Notation pm_lookup_operand := (PmStep2U1.pm_lookup_operand CL).
  #[local] Notation pm_tail_676a4 := (PmBody1U1.pm_tail_676a4 CL).
  #[local] Notation loop_mem := (PmStepU1.loop_mem (MI:=MI) (ST:=ST)).
  #[local] Notation loop_regs := (PmStepU1.loop_regs (MI:=MI) (ST:=ST)).
  #[local] Notation izero := (PmInstU1.izero).
  #[local] Notation ictx := (PmInstU1.ictx).
  #[local] Notation nodes := (PmLoopU1.nodes).
  #[local] Notation macct := (PmLoopU1.macct).
  #[local] Notation lacc := (PmLoopU1.lacc).
  #[local] Notation LI := (PmLoopU1.LI (MI:=MI) (ST:=ST)).
  #[local] Notation ipure := (PmODefsU1.ipure (G:=G) (idesc:=idesc)).
  #[local] Notation OLI := (PmODefsU1.OLI (MI:=MI) (ST:=ST) (generates_type:=generates_type)).
  #[local] Notation oregs := (PmODefsU1.oregs (MI:=MI) (ST:=ST)).
  #[local] Notation ifr := (PmODefsU1.ifr (MI:=MI) (ST:=ST)).
  #[local] Notation iacc := (PmODefsU1.iacc (generates_type:=generates_type)).
  #[local] Notation OSREGS := (PmODefsU1.OSREGS).
  #[local] Notation pm_h5 := (PmStep5U1.pm_h5 CL).
  #[local] Notation set_m2 := (PmStep5U1.set_m2).
  #[local] Notation pm_D7 := (PmExitDiagU1.pm_D7 CL).
  #[local] Notation pm_D8 := (PmExitDiagU1.pm_D8 CL).
  #[local] Notation pm_D9 := (PmExitDiagU1.pm_D9 CL).
  #[local] Notation ext_val_zx2 := PmInstU1.ext_val_zx2.
  #[local] Notation w_mul_lit := PmExitDiagU1.w_mul_lit.
  #[local] Notation zbv_add := PmBody1U1.zbv_add.
  #[local] Notation zbv_mul := PmBody1U1.zbv_mul.
  #[local] Notation kword_expr := PmBody1U1.kword_expr.
  #[local] Notation kdisj_expr := PmBody1U1.kdisj_expr.
  Definition pm_generates_type := pm_leafA (MI:=MI) (ST:=ST) _ _ _ (cu_generates_type _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
  Definition pm_is_optional := pm_leafA (MI:=MI) (ST:=ST) _ _ _ (cu_is_optional _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
  Definition pm_fpenc := pm_leafA (MI:=MI) (ST:=ST) _ _ _ (cu_fpenc16 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).

  Ltac fixregs2 := fixregs;
    try replace (Z_to_bv 5 (Z.of_N 10)) with (10%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 11)) with (11%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 12)) with (12%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 13)) with (13%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 15)) with (15%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 18)) with (18%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 21)) with (21%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 22)) with (22%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 23)) with (23%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 26)) with (26%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 27)) with (27%bv : reg) in * by (apply bv_eq; reflexivity).

  #[local] Notation OREGSEED := [(9%bv, EAlu ALU_ADD (EVar 33) (ELit 88)); (18%bv, ELit 1); (19%bv, ELit (2 ^ 61)); (20%bv, ELit 20); (21%bv, EAlu ALU_ADD (EVar 33) (ELit 264)); (25%bv, ELit 5)]%list.
  Tactic Notation "seedOR" ident(HR) constr(E) constr(R) uconstr(extra) :=
    let l := constr:(([(2%bv, EVar 32); (8%bv, EVar 33)] ++ OREGSEED ++ extra) : list (reg * expr)) in
    let l' := eval cbn [app] in l in
    seedHR_ HR E l' R.

  Ltac oregs_of HRn ORn Qgp Qtp :=
    let G2 := fresh "G2" in let G3 := fresh "G3" in let G4 := fresh "G4" in let G8 := fresh "G8" in
    let T9 := fresh "T9" in let T18 := fresh "T18" in let T19 := fresh "T19" in let T20 := fresh "T20" in let T21 := fresh "T21" in let T25 := fresh "T25" in
    rreg HRn (2%bv) G2; rreg HRn (3%bv) G3; rreg HRn (4%bv) G4; rreg HRn (8%bv) G8;
    rreg HRn (9%bv) T9; rreg HRn (18%bv) T18; rreg HRn (19%bv) T19; rreg HRn (20%bv) T20; rreg HRn (21%bv) T21; rreg HRn (25%bv) T25;
    try replace (Z_to_bv 5 (Z.of_N 3)) with (3%bv : reg) in G3 by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 4)) with (4%bv : reg) in G4 by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 8)) with (8%bv : reg) in G8 by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 9)) with (9%bv : reg) in T9 by (apply bv_eq; reflexivity);
    rewrite Qgp in G3; rewrite Qtp in G4; evs_in T9; evs_in T21; rewrite ?w_add in T9 by lia; rewrite ?w_add in T21 by lia;
    lazymatch type of HRn with regs_ok _ _ ?Rn =>
      assert (ORn : oregs _ Rn) by (unfold oregs, loop_regs; rewrite G2, G3, G4, G8, T9, T18, T19, T20, T21, T25; repeat split; reflexivity) end;
    clear G2 G3 G4 G8 T9 T18 T19 T20 T21 T25 HRn.
  Ltac orsplit OR := pose proof OR as OR'; destruct OR' as (Qsp & Qgp & Qtp & Qs0 & Qs1 & Qs2 & Qs3 & Qs4 & Qs5 & Qs9).

  Lemma mod16_mod8 : forall s k, s mod 16 = 0 -> k mod 8 = 0 -> (s + k) mod 8 = 0.
  Proof using.
    intros s k Hs Hk. apply Z.mod_divide; [lia|]. apply Z.divide_add_r; [| apply Z.mod_divide; [lia | exact Hk]].
    apply Z.mod_divide in Hs; [|lia]. destruct Hs as [q Hq]. exists (2 * q). lia.
  Qed.
  Lemma Z_to_bv64_inj : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> Z_to_bv 64 a = Z_to_bv 64 b -> a = b.
  Proof using.
    intros a b Ha Hb E. apply (f_equal bv_unsigned) in E. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod, !Z.mod_small in E by lia. exact E.
  Qed.
  Lemma w_sltu : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
    alu64 ALU_SLTU (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (if a <? b then 1 else 0).
  Proof using.
    intros a b Ha Hb. cbn [alu64 alu]. unfold bv_ltu. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod, !Z.mod_small by lia.
    destruct (a <? b); reflexivity.
  Qed.

  Definition LOOPK (w : pmw MI ST) (K : TSet) (io : Z) : Prop :=
    forall (fx' : FPState) A' M' model' c' R', frm_zero (@fp_csr fx') -> fconsts fx' -> LI w A' M' model' c' R' -> io < c_widx c' ->
      srealizes SEGS (cfg fx' R' 0x67578 M' model') K.

  Definition RNS (w : pmw MI ST) (I : ictxR) A M model c : Prop :=
    PMX w A M model c /\ c_tr c = [] /\ pm_bud (w_n w) c /\ loop_mem w M /\
    (exists rid, cellw SEGS M (w_sp w + 260) 4 rid) /\
    c_icount c + 5 <= c_widx c /\ c_endian c < 2 /\ w_words w <> 0 /\ nodes c + 2 <= c_widx c + 3 /\ macct c /\
    i_io I + i_iwc I = c_widx c /\
    2 * Zlen (t3c (c_m1 c)) <= c_widx c /\ 3 * Zlen (t3c (c_m3 c)) <= c_widx c /\ 2 * Zlen (t3c (c_m2 c)) <= i_io I.

  Definition rns_win (w : pmw MI ST) (a : Z) : Prop :=
    w_sp w + 8 <= a < w_sp w + 24 \/ w_sp w + 128 <= a < w_sp w + 260 \/ w_sp w + 264 <= a < w_sp0 w - 104.

  Lemma rns_frame : forall (w : pmw MI ST) I A M M' model c (W : Z -> Prop),
    RNS w I A M model c -> stores_in W M M' -> (forall a, W a -> rns_win w a) -> RNS w I A M' model c.
  Proof using AC MI ST.
    intros w I A M M' model c W (X & Htr & BUD & LM & (rid & Crid) & REST) STI HW. unfold rns_win in HW.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & [Gc2 Gcal] & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    split.
    { eapply (pmx_frame_stores SEGS Ly.L MI ST ly_img_low ly_rw_img ly_relro_img w A M M' model c W); [exact X | exact STI |].
      intros a Ha. unfold zwin, w_sp0, PM_FRAME. destruct (HW a Ha) as [?|[?|?]]; lia. }
    split; [exact Htr|]. split; [exact BUD|]. split.
    { eapply (loop_mem_frame w M M'); [exact LM | lia | lia | eapply stores_in_agree; [exact STI | unfold zwin; intros a Ha; split; [lia | intros HWa; destruct (HW a HWa) as [?|[?|?]]; lia]]]. }
    split; [| exact REST]. exists rid.
    eapply (cellw_frame M M'); [exact Crid | lia | cbn; lia | eapply stores_in_agree; [exact STI | unfold zwin; cbn; intros a Ha; split; [lia | intros HWa; destruct (HW a HWa) as [?|[?|?]]; lia]]].
  Qed.

  Lemma rns_agree : forall (w : pmw MI ST) I A M M' model c (P : Z -> Prop),
    RNS w I A M model c -> PMX w A M' model c -> CRep.agree_on P M M' ->
    (forall a, (w_sp w + 24 <= a < w_sp w + 128 \/ w_sp w + 260 <= a < w_sp w + 264) -> P a) ->
    RNS w I A M' model c.
  Proof using AC MI ST.
    intros w I A M M' model c P (X & Htr & BUD & LM & (rid & Crid) & REST) X' AG HP.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & [Gc2 Gcal] & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    split; [exact X'|]. split; [exact Htr|]. split; [exact BUD|]. split.
    { eapply (loop_mem_frame w M M'); [exact LM | lia | lia | eapply agree_on_weaken; [exact AG | unfold zwin; intros a Ha; apply HP; lia]]. }
    split; [| exact REST]. exists rid.
    eapply (cellw_frame M M'); [exact Crid | lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold zwin; cbn; intros a Ha; apply HP; lia]].
  Unshelve. all: first [exact SEGS | exact M].
  Qed.

  Lemma oregs_nt_kept : forall (w : pmw MI ST) R R', oregs w R -> nt_kept_u1 R R' -> oregs w R'.
  Proof using AC MI ST.
    intros w R R' OR NK. destruct OR as (Q2 & Q3 & Q4 & Q8 & Q9 & Q18 & Q19 & Q20 & Q21 & Q25). unfold oregs, loop_regs.
    rewrite !NK by ((first [ solve [cbn [In]; repeat (first [left; reflexivity | right])] | cbn; repeat (first [left; reflexivity | right]) ])). repeat split; assumption.
  Qed.
  Lemma oli_regs : forall (w : pmw MI ST) I A M model c R R', OLI w I A M model c R -> oregs w R' -> OLI w I A M model c R'.
  Proof using AC MI ST generates_type.
    intros w I A M model c R R' (OB & REST) OR'. split; [| exact REST].
    destruct OB as (X & Htr & BUD & OR & REST2). split; [exact X|]. split; [exact Htr|]. split; [exact BUD|]. split; [exact OR' | exact REST2].
  Qed.

  Lemma pm_xtail : forall (w : pmw MI ST) c0 K (fx : FPState) (io : Z) A M model c R,
    PMS w c0 K -> frm_zero (@fp_csr fx) -> fconsts fx ->
    PMX w A M model c -> c_tr c = [] -> pm_bud (w_n w) c -> oregs w R -> loop_mem w M ->
    c_icount c + 5 <= c_widx c -> c_endian c < 2 -> w_words w <> 0 -> nodes c + 1 <= c_widx c + 3 -> macct c -> lacc c ->
    io < c_widx c -> LOOPK w K io ->
    srealizes SEGS (cfg fx R 0x69080 M model) K.
  Proof using AC MI ST.
    intros w c0 K fx io A M model c R PS FZ FC X Htr BUD OR LM Hic He2 Hw ACC MACC LACC Hio LK.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & [Gc2 Gcal] & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof (x_scal X) as (Sc1 & Sc2 & Sc3 & Sc4).
    orsplit OR.
    pose proof (x_v1 X) as V1. destruct V1 as (_ & _ & _ & V1len & V1blk & V1f0 & V1f1 & _). unfold O_V1 in V1f0, V1f1.
    assert (Rb1 : 0 <= t3a (c_v1 c) /\ t3a (c_v1 c) + OPND_SZ * t3b (c_v1 c) < 2 ^ 64).
    { destruct V1blk as [[Hb0 Hc0]|(Hb1 & _ & _ & Hb2 & _)]; unfold OPND_SZ in *; [rewrite Hb0; lia | lia]. }
    unfold OPND_SZ in V1f1, Rb1. replace (w_p w + 216 + 8) with (w_p w + 224) in V1f1 by lia.
    pm_seed R w c [Z_to_bv 64 (t3a (c_v1 c)); Z_to_bv 64 (t3a (c_v1 c) + 20 * t3b (c_v1 c))].
    seedOR HR E R (@nil (reg * expr)). seedHK HK w A M model c E X.
    apply (know_more E M [KWord (SA (EVar 33) 216) (N.to_nat 8) (EVar 39); KWord (SA (EVar 33) 224) (N.to_nat 8) (EVar 40);
                           KWord (SA (EVar 32) 96) (N.to_nat 8) (ELit 0xffffffffcccccccd); KWord (SA (EVar 33) 32) (N.to_nat 8) (ELit 0)]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil.
         - eapply kword_var; [eapply fld_cellw; [exact V1f0 | cbn; lia] | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
         - eapply kword_var; [eapply fld_cellw; [exact V1f1 | cbn; lia] | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
         - eapply kword_var; [eapply (loop_mem_cell w _ 96 0xffffffffcccccccd LM); [(first [ solve [cbn [In]; repeat (first [left; reflexivity | right])] | cbn; repeat (first [left; reflexivity | right]) ]) | lia] | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | cbn [edenot]; reflexivity].
         - eapply kword_var; [eapply fld_cellw; [exact (x_insfn X) | cbn; lia] | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | cbn [edenot]; reflexivity]. }
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R1.
    rreg HRn (22%bv) G22. pose proof HRn as HRn'. oregs_of HRn' OR1 Qgp Qtp. clear HRn HR HK. fixregs2.
    lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ => set (M1 := m) in * end.
    assert (ST1 : stores_in (zwin (w_sp w + 264) (w_sp w + 274)) M M1) by (unfold M1; stin).
    assert (X1 : PMX w A M1 model c).
    { eapply (pmx_frame_stores SEGS Ly.L MI ST ly_img_low ly_rw_img ly_relro_img w A M M1 model c (zwin (w_sp w + 264) (w_sp w + 274)));
        [exact X | exact ST1 | unfold zwin, w_sp0, PM_FRAME; intros; lia]. }
    eapply (loop_mem_frame w M M1) in LM; [| lia | lia | eapply stores_in_agree; [exact ST1 | unfold zwin; intros; lia]].
    clear ST1 MS. clearbody M1. clear X.
    eapply (PmLoopU1.pm_latch_ok w fx A M1 model c R1 K X1 OR1 G22).
    intros R2 LR2 Q22. eapply (LK fx A M1 model c R2 FZ FC); [| exact Hio].
    split; [exact X1|]. split; [exact Htr|]. split; [exact BUD|]. split; [exact LR2|]. split; [exact LM|].
    split; [lia|]. split; [exact He2|]. split; [exact Hw|]. split; [exact ACC|]. split; [exact MACC | exact LACC].
  Qed.

  Lemma pm_xh5 : forall (w : pmw MI ST) c0 K (fx : FPState) (I : ictxR) A M model c R (w1 w2 w3 : Z),
    PMS w c0 K -> frm_zero (@fp_csr fx) -> fconsts fx -> ipure I -> RNS w I A M model c -> oregs w R ->
    getr R 15%bv = Z_to_bv 64 w3 -> cell8 SEGS M (w_sp w + 16) w1 -> cell8 SEGS M (w_sp w + 8) w2 ->
    0 <= w1 < 2 ^ 64 -> 0 <= w2 < 2 ^ 64 -> 0 <= w3 < 2 ^ 64 -> w1 mod 2 ^ 32 < 4 -> w3 mod 2 ^ 32 < 16 ->
    2 <= i_iwc I -> LOOPK w K (i_io I) ->
    srealizes SEGS (cfg fx R 0x689f8 M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx I A M model c R w1 w2 w3 PS FZ FC IP (X & Htr & BUD & LM & (rid & Crid) & Hic & He2 & Hw & ACC & MACC & Hsum & LA1 & LA3 & LA2) OR Q15 C16 C8 R1 R2 R3 R1m R3m Hiwc2 LK.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & [Gc2 Gcal] & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof (ipure_ranges I IP) as (Riwc & Rop).
    change 0x689f8 with (hc_nt_entry HConstsU1.hc).
    eapply (pm_h5 w c0 K fx A M model c R rid w1 w2 w3 PS FZ FC X Htr BUD ACC MACC ltac:(lia) OR Q15 C16 C8 R1 R2 R3 R1m R3m LM Crid).
    intros fx' A' R' M' model' m2' FZ' FC' X' BUD' ACC' MACC' ACC2' NK AG.
    change (hc_nt_exit HConstsU1.hc) with 0x69080.
    eapply (pm_xtail w c0 K fx' (i_io I) A' M' model' (set_m2 c m2') R' PS FZ' FC' X' ltac:(cbn; exact Htr) BUD' (oregs_nt_kept w R R' OR NK));
      cbn [set_m2 c_icount c_widx c_endian]; [| exact Hic | exact He2 | exact Hw | exact ACC' | exact MACC' | | lia | exact LK].
    2: { unfold PmLoopU1.lacc. cbn [set_m2 c_m1 c_m2 c_m3 c_widx t3c snd]. lia. }
    eapply (loop_mem_frame w M M'); [exact LM | lia | lia | eapply agree_on_weaken; [exact AG | unfold zwin, w_sp0, PM_FRAME; cbn; intros; lia]].
  Qed.

  Definition WIO : expr := EAlu ALU_ADD (EVar 34) (EMd M_MUL (ELit 4) (EVar 39)).
  Lemma wio_val : forall E words io, ev E 34 = Z_to_bv 64 words -> ev E 39 = Z_to_bv 64 io ->
    0 <= words -> 0 <= io -> words + 4 * io < 2 ^ 64 -> edenot E WIO = Z_to_bv 64 (words + 4 * io).
  Proof using. intros E words io H34 H39 Hw Hi Hhi. cbn [edenot WIO]. rewrite H34, H39. rewrite w_mul by lia. rewrite w_add by lia. reflexivity. Qed.

  Ltac scs_words AW := split_scs; try sc_auto1;
    try (eapply sc_flat; [exact AW | lia | cbn [a_off]; lia | lia | cbn [a_off]; lia]);
    try (cbn [sc_denot]; evs; rewrite ?zbv_mul, ?zbv_add; rewrite ?br_eq, ?br_ne, ?br_ltu, ?br_geu by lia; bool_lia).

  Lemma pm_xrnt_int : forall (w : pmw MI ST) c0 K (fx : FPState) (I : ictxR) A M model c R,
    PMS w c0 K -> frm_zero (@fp_csr fx) -> fconsts fx -> ipure I -> RNS w I A M model c -> oregs w R ->
    i_op I = OP_TYPE_INT -> 4 <= i_iwc I ->
    getr R 23%bv = Z_to_bv 64 (i_io I) -> LOOPK w K (i_io I) ->
    srealizes SEGS (cfg fx R 0x68944 M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx I A M model c R PS FZ FC IP RN OR Hop Hiwc Q23 LK.
    pose proof RN as RN'. destruct RN' as (X & Htr & BUD & LM & _ & Hic & He2 & Hw & ACC & MACC & Hsum & LA1 & LA3 & LA2).
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & [Gc2 Gcal] & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof (x_scal X) as (Sc1 & Sc2 & Sc3 & Sc4). pose proof (ipure_ranges I IP) as (Riwc & Rop).
    pose proof IP as IP'. destruct IP' as (_ & _ & _ & _ & Hg & Hdesc & Rio).
    orsplit OR.
    destruct (Gw Hw) as (W1 & W2 & W3 & W4 & W5).

    destruct (mdef_cell4 M (w_words w + 4 * i_io I + 8) ltac:(eapply mdef_sub; [exact (x_wbuf X Hw) | lia | lia]) ltac:(lia) ltac:(lia)) as (w2 & Cw2).
    destruct (mdef_cell4 M (w_words w + 4 * i_io I + 12) ltac:(eapply mdef_sub; [exact (x_wbuf X Hw) | lia | lia]) ltac:(lia) ltac:(lia)) as (w3 & Cw3).
    pose proof (proj1 Cw2) as Rw2. pose proof (proj1 Cw3) as Rw3. cbn in Rw2, Rw3.
    pose proof (fld_cellw M _ 4 _ (x_endian X) ltac:(lia)) as Ce. unfold O_ENDIAN in Ce.
    assert (He32 : 0 <= c_endian c < 2 ^ 32) by lia.

    pm_seed R w c [Z_to_bv 64 (i_io I); Z_to_bv 64 (c_endian c); Z_to_bv 64 w3; Z_to_bv 64 w2].
    seedOR HR E R [(23%bv, EVar 39)]. seedHK HK w A M model c E X.
    assert (AW : edenot E WIO = Z_to_bv 64 (w_words w + 4 * i_io I)) by (apply wio_val; [evs; reflexivity | evs; reflexivity | lia | lia | lia]).
    apply (know_more E M [KWord (SA (EVar 33) 88) (N.to_nat 4) (EVar 40); KRange (EVar 40) 0 1; KRange (EVar 34) 1 (2 ^ 47); KAlign (EVar 34) 4;
                           KRange (EVar 39) 0 (2 ^ 24); KWord (SA WIO 12) (N.to_nat 4) (EVar 41); KWord (SA WIO 8) (N.to_nat 4) (EVar 42)]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil.
         - eapply kword_var; [exact Ce | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
         - eapply krange_var; [evs; reflexivity | lia | lia].
         - eapply krange_var; [evs; reflexivity | lia | lia].
         - eapply kalign_var; [evs; reflexivity | lia | lia | exact W2].
         - eapply krange_var; [evs; reflexivity | lia | lia].
         - eapply kword_expr; [exact Cw3 | cbn; lia | exact AW | lia | lia | cbn; lia | evs; reflexivity].
         - eapply kword_expr; [exact Cw2 | cbn; lia | exact AW | lia | lia | cbn; lia | evs; reflexivity]. }
    xruns HR HK 100%nat STOPS (SCR [false] [] []) 50%N. { scs_words AW. }
    postrun. name_run HRn R1.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (23%bv) G23.
    pose proof HRn as HRn'. oregs_of HRn' OR1 Qgp Qtp. clear HRn HR HK AW. fixregs2.
    rewrite ?ext_val_sx4 in G10 by lia. rewrite ?ext_val_sx4, ?sx32_small in G11 by lia.
    eapply (pm_fixword w A M model c fx R1 _ K X (ex_intro _ w3 (ex_intro _ (c_endian c) (conj Rw3 (conj G10 (conj He32 G11))))) G1 ltac:(apply bv_eq; vm_compute; reflexivity)).
    intros R2 KEPT (r3 & Rr3 & Hr3). rewrite TablStmts.sx32_prs in Hr3.
    pose proof (oregs_kept w R1 R2 OR1 KEPT) as OR2. keptQ KEPT G2 Qsp_R2. keptQ KEPT G8 Qs0_R2. keptQ KEPT G23 Q23b. clear G1 G2 G8 G10 G11 G23 KEPT OR1.
    pose proof (sx32_range r3 Rr3) as Rsr3.
    clear Qsp Qgp Qtp Qs0 Qs1 Qs2 Qs3 Qs4 Qs5 Qs9. orsplit OR2.

    pm_seed R2 w c [Z_to_bv 64 (i_io I); Z_to_bv 64 (c_endian c); Z_to_bv 64 w3; Z_to_bv 64 w2; Z_to_bv 64 (PrsGrammar.sx32 r3)].
    seedOR HR E R2 [(23%bv, EVar 39); (10%bv, EVar 43)]. seedHK HK w A M model c E X.
    assert (AW : edenot E WIO = Z_to_bv 64 (w_words w + 4 * i_io I)) by (apply wio_val; [evs; reflexivity | evs; reflexivity | lia | lia | lia]).
    apply (know_more E M [KWord (SA (EVar 33) 88) (N.to_nat 4) (EVar 40); KRange (EVar 40) 0 1; KRange (EVar 34) 1 (2 ^ 47); KAlign (EVar 34) 4;
                           KRange (EVar 39) 0 (2 ^ 24); KWord (SA WIO 8) (N.to_nat 4) (EVar 42)]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil.
         - eapply kword_var; [exact Ce | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
         - eapply krange_var; [evs; reflexivity | lia | lia].
         - eapply krange_var; [evs; reflexivity | lia | lia].
         - eapply kalign_var; [evs; reflexivity | lia | lia | exact W2].
         - eapply krange_var; [evs; reflexivity | lia | lia].
         - eapply kword_expr; [exact Cw2 | cbn; lia | exact AW | lia | lia | cbn; lia | evs; reflexivity]. }
    xruns HR HK 100%nat STOPS (SCR [false] [] []) 50%N. { scs_words AW. }
    postrun. name_run HRn R3.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11.
    pose proof HRn as HRn'. oregs_of HRn' OR3 Qgp Qtp. clear HRn HR HK AW. fixregs2.
    rewrite ?ext_val_sx4 in G10 by lia. rewrite ?ext_val_sx4, ?sx32_small in G11 by lia.
    rewrite ?w_sltu by lia. rewrite ?w_add by (destruct (0 <? PrsGrammar.sx32 r3); lia).
    set (va := (if 0 <? PrsGrammar.sx32 r3 then 1 else 0) + 1) in *.
    assert (Rva : 0 <= va <= 2) by (subst va; destruct (0 <? PrsGrammar.sx32 r3); lia).
    lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ => set (M1 := m) in * end.
    assert (ST1 : stores_in (zwin (w_sp w + 16) (w_sp w + 24)) M M1) by (unfold M1; stin).
    assert (RN1 : RNS w I A M1 model c) by (eapply (rns_frame w I A M M1 model c _ RN ST1); unfold rns_win, zwin, w_sp0, PM_FRAME; intros; lia).
    assert (C16 : cell8 SEGS M1 (w_sp w + 16) va) by (split; [cbn; lia | unfold M1; change (N.to_nat 8) with 8%nat; rdback]).
    pose proof RN1 as RN1'. destruct RN1' as (X1 & _).
    clear ST1 MS. clearbody M1. clear X RN Ce Cw2 Cw3. pose proof (x_ms X1) as MS1.
    eapply (pm_fixword w A M1 model c fx R3 _ K X1 (ex_intro _ w2 (ex_intro _ (c_endian c) (conj Rw2 (conj G10 (conj He32 G11))))) G1 ltac:(apply bv_eq; vm_compute; reflexivity)).
    intros R4 KEPT (r2 & Rr2 & Hr2). rewrite TablStmts.sx32_prs in Hr2.
    pose proof (oregs_kept w R3 R4 OR3 KEPT) as OR4. keptQ KEPT G2 Qsp_R4. keptQ KEPT G8 Qs0_R4. clear G1 G2 G8 G10 G11 KEPT OR3 OR2.
    pose proof (sx32_range r2 Rr2) as Rsr2.
    clear Qsp Qgp Qtp Qs0 Qs1 Qs2 Qs3 Qs4 Qs5 Qs9. orsplit OR4.

    pm_seed R4 w c [Z_to_bv 64 (PrsGrammar.sx32 r2)].
    seedOR HR E R4 [(10%bv, EVar 39)]. seedHK HK w A M1 model c E X1.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R5.
    rreg HRn (15%bv) G15. pose proof HRn as HRn'. oregs_of HRn' OR5 Qgp Qtp. clear HRn HR HK. fixregs2.
    lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ => set (M2 := m) in * end.
    assert (ST2 : stores_in (zwin (w_sp w + 8) (w_sp w + 16)) M1 M2) by (unfold M2; stin).
    assert (RN2 : RNS w I A M2 model c) by (eapply (rns_frame w I A M1 M2 model c _ RN1 ST2); unfold rns_win, zwin, w_sp0, PM_FRAME; intros; lia).
    assert (C8 : cell8 SEGS M2 (w_sp w + 8) (PrsGrammar.sx32 r2)) by (split; [cbn; lia | unfold M2; change (N.to_nat 8) with 8%nat; rdback]).
    eapply (cellw_frame M1 M2) in C16; [| lia | cbn; lia | eapply stores_in_agree; [exact ST2 | unfold zwin; cbn; intros; lia]].
    clearbody M2.
    eapply (pm_xh5 w c0 K fx I A M2 model c R5 va (PrsGrammar.sx32 r2) 0 PS FZ FC IP RN2 OR5 G15 C16 C8 ltac:(lia) Rsr2 ltac:(lia) ltac:(rewrite Z.mod_small by lia; lia) ltac:(rewrite Z.mod_small by lia; lia) ltac:(lia) LK).
  Qed.

  Lemma pm_xrnt_float : forall (w : pmw MI ST) c0 K (fx : FPState) (I : ictxR) A M model c R,
    PMS w c0 K -> frm_zero (@fp_csr fx) -> fconsts fx -> ipure I -> RNS w I A M model c -> oregs w R ->
    i_op I = OP_TYPE_FLOAT -> 3 <= i_iwc I -> cellw SEGS M (w_sp w + 248) 2 (i_iwc I) ->
    getr R 23%bv = Z_to_bv 64 (i_io I) -> LOOPK w K (i_io I) ->
    srealizes SEGS (cfg fx R 0x68868 M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx I A M model c R PS FZ FC IP RN OR Hop Hiwc C248 Q23 LK.
    pose proof RN as RN'. destruct RN' as (X & Htr & BUD & LM & _ & Hic & He2 & Hw & ACC & MACC & Hsum & LA1 & LA3 & LA2).
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & [Gc2 Gcal] & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof (x_scal X) as (Sc1 & Sc2 & Sc3 & Sc4). pose proof (ipure_ranges I IP) as (Riwc & Rop).
    pose proof IP as IP'. destruct IP' as (_ & _ & _ & _ & Hg & Hdesc & Rio).
    orsplit OR.
    destruct (Gw Hw) as (W1 & W2 & W3 & W4 & W5).
    destruct (mdef_cell4 M (w_words w + 4 * i_io I + 8) ltac:(eapply mdef_sub; [exact (x_wbuf X Hw) | lia | lia]) ltac:(lia) ltac:(lia)) as (w2 & Cw2).
    pose proof (proj1 Cw2) as Rw2. cbn in Rw2.
    pose proof (fld_cellw M _ 4 _ (x_endian X) ltac:(lia)) as Ce. unfold O_ENDIAN in Ce.
    assert (He32 : 0 <= c_endian c < 2 ^ 32) by lia.
    pose proof (proj1 C248) as Riwc16. cbn in Riwc16.

    pm_seed R w c [Z_to_bv 64 (i_io I); Z_to_bv 64 (c_endian c); Z_to_bv 64 w2].
    seedOR HR E R [(23%bv, EVar 39)]. seedHK HK w A M model c E X.
    assert (AW : edenot E WIO = Z_to_bv 64 (w_words w + 4 * i_io I)) by (apply wio_val; [evs; reflexivity | evs; reflexivity | lia | lia | lia]).
    apply (know_more E M [KWord (SA (EVar 33) 88) (N.to_nat 4) (EVar 40); KRange (EVar 40) 0 1; KRange (EVar 34) 1 (2 ^ 47); KAlign (EVar 34) 4;
                           KRange (EVar 39) 0 (2 ^ 24); KWord (SA WIO 8) (N.to_nat 4) (EVar 41)]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil.
         - eapply kword_var; [exact Ce | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
         - eapply krange_var; [evs; reflexivity | lia | lia].
         - eapply krange_var; [evs; reflexivity | lia | lia].
         - eapply kalign_var; [evs; reflexivity | lia | lia | exact W2].
         - eapply krange_var; [evs; reflexivity | lia | lia].
         - eapply kword_expr; [exact Cw2 | cbn; lia | exact AW | lia | lia | cbn; lia | evs; reflexivity]. }
    xruns HR HK 100%nat STOPS (SCR [false] [] []) 50%N. { scs_words AW. }
    postrun. name_run HRn R1.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (23%bv) G23.
    pose proof HRn as HRn'. oregs_of HRn' OR1 Qgp Qtp. clear HRn HR HK AW. fixregs2.
    rewrite ?ext_val_sx4 in G10 by lia. rewrite ?ext_val_sx4, ?sx32_small in G11 by lia.
    eapply (pm_fixword w A M model c fx R1 _ K X (ex_intro _ w2 (ex_intro _ (c_endian c) (conj Rw2 (conj G10 (conj He32 G11))))) G1 ltac:(apply bv_eq; vm_compute; reflexivity)).
    intros R2 KEPT (r2 & Rr2 & Hr2). rewrite TablStmts.sx32_prs in Hr2.
    pose proof (oregs_kept w R1 R2 OR1 KEPT) as OR2. keptQ KEPT G2 Qsp_R2. keptQ KEPT G8 Qs0_R2. keptQ KEPT G23 Q23b. clear G1 G2 G8 G10 G11 G23 KEPT OR1.
    pose proof (sx32_range r2 Rr2) as Rsr2.
    clear Qsp Qgp Qtp Qs0 Qs1 Qs2 Qs3 Qs4 Qs5 Qs9. orsplit OR2.

    destruct (Z.le_gt_cases (i_iwc I) 3) as [Hle3 | Hge4].
    -
      pm_seed R2 w c [Z_to_bv 64 (PrsGrammar.sx32 r2); Z_to_bv 64 (i_iwc I)].
      seedOR HR E R2 [(10%bv, EVar 39)]. seedHK HK w A M model c E X.
      apply (know_more E M [KWord (SA (EVar 32) 248) (N.to_nat 2) (EVar 40); KRange (EVar 40) 3 3]) in HK.
      2: { repeat apply Forall_cons; try apply Forall_nil.
           - eapply kword_var; [exact C248 | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
           - eapply krange_var; [evs; reflexivity | lia | lia]. }
      xruns HR HK 100%nat STOPS (SCR [true] [] []) 50%N.
      { split_scs; try sc_auto1. all: cbn [sc_denot]; evs; rewrite ?ext_val_zx2 by lia; rewrite ?br_geu, ?br_ltu by lia; try bool_lia. }
      postrun. name_run HRn R3.
      rreg HRn (15%bv) G15. pose proof HRn as HRn'. oregs_of HRn' OR3 Qgp Qtp. clear HRn HR HK. fixregs2.
      lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ => set (M1 := m) in * end.
      assert (ST1 : stores_in (zwin (w_sp w + 8) (w_sp w + 24)) M M1) by (unfold M1; stin).
      assert (RN1 : RNS w I A M1 model c) by (eapply (rns_frame w I A M M1 model c _ RN ST1); unfold rns_win, zwin, w_sp0, PM_FRAME; intros; lia).
      assert (C16 : cell8 SEGS M1 (w_sp w + 16) 3) by (split; [cbn; lia | unfold M1; change (N.to_nat 8) with 8%nat; rdback]).
      assert (C8 : cell8 SEGS M1 (w_sp w + 8) (PrsGrammar.sx32 r2)) by (split; [cbn; lia | unfold M1; change (N.to_nat 8) with 8%nat; rdback]).
      clearbody M1.
      eapply (pm_xh5 w c0 K fx I A M1 model c R3 3 (PrsGrammar.sx32 r2) 0 PS FZ FC IP RN1 OR3 G15 C16 C8 ltac:(lia) Rsr2 ltac:(lia) ltac:(rewrite Z.mod_small by lia; lia) ltac:(rewrite Z.mod_small by lia; lia) ltac:(lia) LK).
    -
      destruct (mdef_cell4 M (w_words w + 4 * i_io I + 12) ltac:(eapply mdef_sub; [exact (x_wbuf X Hw) | lia | lia]) ltac:(lia) ltac:(lia)) as (w3 & Cw3).
      pose proof (proj1 Cw3) as Rw3. cbn in Rw3.
      pm_seed R2 w c [Z_to_bv 64 (i_io I); Z_to_bv 64 (c_endian c); Z_to_bv 64 w3; Z_to_bv 64 (PrsGrammar.sx32 r2); Z_to_bv 64 (i_iwc I)].
      seedOR HR E R2 [(23%bv, EVar 39); (10%bv, EVar 42)]. seedHK HK w A M model c E X.
      assert (AW : edenot E WIO = Z_to_bv 64 (w_words w + 4 * i_io I)) by (apply wio_val; [evs; reflexivity | evs; reflexivity | lia | lia | lia]).
      apply (know_more E M [KWord (SA (EVar 32) 248) (N.to_nat 2) (EVar 43); KRange (EVar 43) 4 (2 ^ 16 - 1);
                             KWord (SA (EVar 33) 88) (N.to_nat 4) (EVar 40); KRange (EVar 40) 0 1; KRange (EVar 34) 1 (2 ^ 47); KAlign (EVar 34) 4;
                             KRange (EVar 39) 0 (2 ^ 24); KWord (SA WIO 12) (N.to_nat 4) (EVar 41);
                             KDisj (SA WIO 12) (ELit 4) (SA (EVar 32) 0) (ELit 864); KDisj (SA WIO 12) (ELit 4) (SA (EVar 33) 0) (ELit 288)]) in HK.
      2: { repeat apply Forall_cons; try apply Forall_nil.
           - eapply kword_var; [exact C248 | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
           - eapply krange_var; [evs; reflexivity | lia | lia].
           - eapply kword_var; [exact Ce | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
           - eapply krange_var; [evs; reflexivity | lia | lia].
           - eapply krange_var; [evs; reflexivity | lia | lia].
           - eapply kalign_var; [evs; reflexivity | lia | lia | exact W2].
           - eapply krange_var; [evs; reflexivity | lia | lia].
           - eapply kword_expr; [exact Cw3 | cbn; lia | exact AW | lia | lia | cbn; lia | evs; reflexivity].
           - eapply kdisj_expr; [exact AW | evs; reflexivity | lia | lia | lia | lia |].
             destruct (W5 (w_words w + 4 * i_io I + 12) ltac:(unfold zwin; lia)) as [Hnw _].
             destruct (W5 (w_words w + 4 * i_io I + 15) ltac:(unfold zwin; lia)) as [Hnw' _]. unfold zwin in Hnw, Hnw'. lia.
           - eapply kdisj_expr; [exact AW | evs; reflexivity | lia | lia | lia | lia |].
             destruct (W5 (w_words w + 4 * i_io I + 12) ltac:(unfold zwin; lia)) as [_ Hnp].
             destruct (W5 (w_words w + 4 * i_io I + 15) ltac:(unfold zwin; lia)) as [_ Hnp']. lia. }
      xruns HR HK 100%nat STOPS (SCR [false; false] [] []) 50%N.
      { scs_words AW. all: cbn [sc_denot]; evs; rewrite ?ext_val_zx2 by lia; rewrite ?br_geu, ?br_ltu by lia; try bool_lia. }
      postrun. name_run HRn R3.
      rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11.
      pose proof HRn as HRn'. oregs_of HRn' OR3 Qgp Qtp. clear HRn HR HK AW. fixregs2.
      rewrite ?ext_val_sx4 in G10 by lia. rewrite ?ext_val_sx4, ?sx32_small in G11 by lia.
      lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ => set (M1 := m) in * end.
      assert (ST1 : stores_in (fun a => zwin (w_sp w + 8) (w_sp w + 24) a \/ zwin (w_sp w + 304) (w_sp w + 312) a) M M1).
      { unfold M1. repeat (first [ apply stores_in_refl
                                 | eapply stores_in_wbytes_more; [ | lia | w2blen; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia
                                                                  | w2blen; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unfold zwin; intros; lia ] ]). }
      assert (RN1 : RNS w I A M1 model c) by (eapply (rns_frame w I A M M1 model c _ RN ST1); unfold rns_win, zwin, w_sp0, PM_FRAME; intros a [Ha|Ha]; lia).
      assert (C16 : cell8 SEGS M1 (w_sp w + 16) 3) by (split; [cbn; lia | unfold M1; change (N.to_nat 8) with 8%nat; rdback]).
      assert (C8 : cell8 SEGS M1 (w_sp w + 8) (PrsGrammar.sx32 r2)) by (split; [cbn; lia | unfold M1; change (N.to_nat 8) with 8%nat; rdback]).
      pose proof RN1 as RN1'. destruct RN1' as (X1 & _).
      clear ST1 MS. clearbody M1. clear X RN Ce Cw2 Cw3 C248. pose proof (x_ms X1) as MS1.
      eapply (pm_fixword w A M1 model c fx R3 _ K X1 (ex_intro _ w3 (ex_intro _ (c_endian c) (conj Rw3 (conj G10 (conj He32 G11))))) G1 ltac:(apply bv_eq; vm_compute; reflexivity)).
      intros R4 KEPT (r3 & Rr3 & Hr3). rewrite TablStmts.sx32_prs in Hr3.
      pose proof (oregs_kept w R3 R4 OR3 KEPT) as OR4. keptQ KEPT G2 Qsp_R4. keptQ KEPT G8 Qs0_R4. clear G1 G2 G8 G10 G11 KEPT OR3 OR2.
      pose proof (sx32_range r3 Rr3) as Rsr3.
      clear Qsp Qgp Qtp Qs0 Qs1 Qs2 Qs3 Qs4 Qs5 Qs9. orsplit OR4.

      pm_seed R4 w c [Z_to_bv 64 (PrsGrammar.sx32 r3)].
      seedOR HR E R4 [(10%bv, EVar 39)]. seedHK HK w A M1 model c E X1.
      xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
      postrun. name_run HRn R5.
      rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
      pose proof HRn as HRn'. oregs_of HRn' OR5 Qgp Qtp. clear HRn HR HK. fixregs2.
      rewrite ?w_add in G12 by lia.
      eapply (pm_lookup_operand w A M1 model c fx R5 34 r3 (w_sp w + 304) 0x68920 K X1 G10 ltac:(lia)
                ltac:(intros XX; discriminate XX) ltac:(intros _; split; [rewrite TablStmts.sx32_prs; exact G11 | split; [exact Rr3 | exact G12]]) G2
                ltac:(lia) ltac:(unfold w_sp0, PM_FRAME; lia) ltac:(apply mod16_mod8; [exact Gsp16 | reflexivity])
                G1 ltac:(apply bv_eq; vm_compute; reflexivity)).
      intros R6 M2 r d KEPT Ga0 Rr Fd Hfound Hdesc2 X2 AG.
      assert (RN2 : RNS w I A M2 model c) by (eapply (rns_agree w I A M1 M2 model c _ RN1 X2 AG); unfold zwin, w_sp0, PM_FRAME; intros; lia).
      eapply (cellw_frame M1 M2) in C16; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold zwin, w_sp0, PM_FRAME; cbn; intros; lia]].
      eapply (cellw_frame M1 M2) in C8; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold zwin, w_sp0, PM_FRAME; cbn; intros; lia]].
      pose proof (oregs_kept w R5 R6 OR5 KEPT) as OR6. keptQ KEPT G2 Qsp6. keptQ KEPT G8 Qs06.
      clear G1 G2 G8 G10 G11 G12 KEPT OR5 OR4.
      pose proof (x_ms X2) as MS2.
      clear Qsp Qgp Qtp Qs0 Qs1 Qs2 Qs3 Qs4 Qs5 Qs9. orsplit OR6.

      destruct (Z.eq_dec r 0) as [-> | Hr0].
      + pose proof (Hdesc2 eq_refl) as HD.
        destruct ((cu_odesc_value _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL) d 34 r3 M2 HD (x_roc X2)) as (Fv & Hd1 & Hd2).
        destruct (ODP d 34 r3 HD) as (_ & Hd40 & Hd4).
        pose proof (fld_cellw M2 _ 4 _ Fv ltac:(lia)) as Cv.
        pm_seed R6 w c [Z_to_bv 64 d; Z_to_bv 64 r3].
        seedOR HR E R6 [(10%bv, ELit 0)]. seedHK HK w A M2 model c E X2.
        apply (know_more E M2 [KWord (SA (EVar 32) 304) (N.to_nat 8) (EVar 39); KWord (SA (EVar 39) 0) (N.to_nat 4) (EVar 40);
                               KRange (EVar 39) 0x10000 (2 ^ 40); KAlign (EVar 39) 4]) in HK.
        2: { repeat apply Forall_cons; try apply Forall_nil.
             - eapply kword_var; [eapply fld_cellw; [exact Fd | cbn; lia] | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
             - eapply kword_var; [rewrite Z.add_0_r; exact Cv | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
             - eapply krange_var; [evs; reflexivity | lia | lia].
             - eapply kalign_var; [evs; reflexivity | lia | lia | exact Hd4]. }
        xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
        postrun. name_run HRn R7.
        rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (8%bv) G8.
        pose proof HRn as HRn'. oregs_of HRn' OR7 Qgp Qtp. clear HRn HR HK. fixregs2.
        eapply (pm_fpenc w A M2 model c fx R7 _ K X2 Logic.I G1 ltac:(apply bv_eq; vm_compute; reflexivity)).
        intros R8 KEPT (r11 & Rr11 & Ga0'). pose proof (oregs_kept w R7 R8 OR7 KEPT) as OR8. keptQ KEPT G2 Qsp_R8. keptQ KEPT G8 Qs0_R8.
        clear G1 G2 G8 KEPT OR7.
        clear Qsp Qgp Qtp Qs0 Qs1 Qs2 Qs3 Qs4 Qs5 Qs9. orsplit OR8.

        pm_seed R8 w c [Z_to_bv 64 r11].
        seedOR HR E R8 [(10%bv, EVar 39)]. seedHK HK w A M2 model c E X2.
        xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
        postrun. name_run HRn R9.
        rreg HRn (15%bv) G15. pose proof HRn as HRn'. oregs_of HRn' OR9 Qgp Qtp. clear HRn HR HK. fixregs2.
        eapply (pm_xh5 w c0 K fx I A M2 model c R9 3 (PrsGrammar.sx32 r2) r11 PS FZ FC IP RN2 OR9 G15 C16 C8 ltac:(lia) Rsr2 ltac:(lia) ltac:(rewrite Z.mod_small by lia; lia) ltac:(rewrite Z.mod_small by lia; lia) ltac:(lia) LK).
      +
        pm_seed R6 w c [Z_to_bv 64 r].
        seedOR HR E R6 [(10%bv, EVar 39)]. seedHK HK w A M2 model c E X2.
        apply (know_more E M2 [KRange (EVar 39) 1 (2 ^ 64 - 1)]) in HK.
        2: { repeat apply Forall_cons; try apply Forall_nil. eapply krange_var; [evs; reflexivity | lia | lia]. }
        xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
        postrun. name_run HRn R7.
        rreg HRn (15%bv) G15. pose proof HRn as HRn'. oregs_of HRn' OR7 Qgp Qtp. clear HRn HR HK. fixregs2.
        eapply (pm_xh5 w c0 K fx I A M2 model c R7 3 (PrsGrammar.sx32 r2) 0 PS FZ FC IP RN2 OR7 G15 C16 C8 ltac:(lia) Rsr2 ltac:(lia) ltac:(rewrite Z.mod_small by lia; lia) ltac:(rewrite Z.mod_small by lia; lia) ltac:(lia) LK).
  Unshelve. all: first [exact SEGS | exact M].
  Qed.

  Lemma pm_xrnt : forall (w : pmw MI ST) c0 K (fx : FPState) (I : ictxR) A M model c R (pw : Z),
    PMS w c0 K -> frm_zero (@fp_csr fx) -> fconsts fx -> ipure I ->
    PMX w A M model c -> c_tr c = [] -> pm_bud (w_n w) c -> oregs w R -> loop_mem w M ->
    ictx w M (i_io I) (i_fw I) (i_iwc I) (i_op I) (i_d I) -> ifr w M ->
    c_icount c + 4 <= i_io I -> c_endian c < 2 -> w_words w <> 0 -> nodes c + 2 <= c_widx c + 3 -> macct c ->
    i_io I + i_iwc I = c_widx c ->
    2 * Zlen (t3c (c_m1 c)) <= c_widx c -> 3 * Zlen (t3c (c_m3 c)) <= c_widx c -> 2 * Zlen (t3c (c_m2 c)) <= i_io I ->
    (generates_type (i_op I) = true -> 2 <= i_iwc I) ->
    (i_op I = OP_TYPE_INT -> 4 <= i_iwc I) -> (i_op I = OP_TYPE_FLOAT -> 3 <= i_iwc I) ->
    getr R 11%bv = Z_to_bv 64 pw -> 0 <= pw < 2 ^ 64 -> getr R 10%bv = Z_to_bv 64 (i_iwc I) -> getr R 23%bv = Z_to_bv 64 (i_io I) ->
    LOOPK w K (i_io I) ->
    srealizes SEGS (cfg fx R 0x68840 M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx I A M model c R pw PS FZ FC IP X Htr BUD OR LM IC IFR Hic He2 Hw ACC MACC Hsum LA1 LA3 LA2 HG5 HInt HFlt Q11 Rpw Q10 Q23 LK.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & [Gc2 Gcal] & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof (x_scal X) as (Sc1 & Sc2 & Sc3 & Sc4). pose proof (ipure_ranges I IP) as (Riwc & Rop).
    orsplit OR.
    pose proof IC as IC'. destruct IC' as (Cio & Cfw & Ciwc & Cop & Fd).
    destruct IFR as (ext & tid & rid & _ & _ & _ & _ & Crid & _).

    pm_seed R w c [Z_to_bv 64 pw; Z_to_bv 64 (i_iwc I); Z_to_bv 64 (i_io I); Z_to_bv 64 (i_op I)].
    seedOR HR E R [(11%bv, EVar 39); (10%bv, EVar 40); (23%bv, EVar 41)]. seedHK HK w A M model c E X.
    apply (know_more E M [KWord (SA (EVar 32) 250) (N.to_nat 2) (EVar 42)]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil.
         eapply kword_var; [exact Cop | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity]. }
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R1.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (22%bv) G22. rreg HRn (23%bv) G23.
    pose proof HRn as HRn'. oregs_of HRn' OR1 Qgp Qtp. clear HRn HR HK. fixregs2. rewrite Qgp in G3. rewrite Qtp in G4.
    rewrite ?ext_val_zx2 in G10, G22 by lia.
    lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ => set (M1 := m) in * end.
    assert (ST1 : stores_in (zwin (w_sp w + 240) (w_sp w + 250)) M M1) by (unfold M1; stin).
    assert (C248 : cellw SEGS M1 (w_sp w + 248) 2 (i_iwc I)) by (split; [cbn; lia | unfold M1; rdback]).
    assert (RN1 : RNS w I A M1 model c).
    { split.
      { eapply (pmx_frame_stores SEGS Ly.L MI ST ly_img_low ly_rw_img ly_relro_img w A M M1 model c (zwin (w_sp w + 240) (w_sp w + 250)));
          [exact X | exact ST1 | unfold zwin, w_sp0, PM_FRAME; intros; lia]. }
      split; [exact Htr|]. split; [exact BUD|]. split.
      { eapply (loop_mem_frame w M M1); [exact LM | lia | lia | eapply stores_in_agree; [exact ST1 | unfold zwin; intros; lia]]. }
      split. { exists rid. eapply (cellw_frame M M1); [exact Crid | lia | cbn; lia | eapply stores_in_agree; [exact ST1 | unfold zwin; cbn; intros; lia]]. }
      repeat match goal with |- _ /\ _ => split end; first [assumption | lia]. }
    pose proof RN1 as RN1'. destruct RN1' as (X1 & _ & _ & LM1 & _).
    clear ST1 MS. clearbody M1. clear X LM Cio Cfw Ciwc Cop Fd Crid.
    assert (Rop32 : 0 <= i_op I < 2 ^ 32) by lia.
    eapply (pm_generates_type w A M1 model c fx R1 _ K X1 (ex_intro _ (i_op I) (conj Rop32 G10)) G1 ltac:(apply bv_eq; vm_compute; reflexivity)).
    intros R2 KEPT (b & Gb & Hb). pose proof (oregs_kept w R1 R2 OR1 KEPT) as OR2. keptQ KEPT G2 Qsp_R2. keptQ KEPT G8 Qs0_R2.
    keptQ KEPT G22 Q22b. keptQ KEPT G23 Q23b. clear G1 G2 G3 G4 G8 G22 G23 KEPT OR1.
    pose proof (x_ms X1) as MS1. clear Qsp Qgp Qtp Qs0 Qs1 Qs2 Qs3 Qs4 Qs5 Qs9. orsplit OR2.
    destruct b; cbn in Gb.
    -
      destruct (Hb eq_refl) as (x' & Rx' & Gx' & Hgt). rewrite G10 in Gx'. apply Z_to_bv64_inj in Gx'; [| lia | lia]. subst x'.
      pose proof (HG5 Hgt) as Hiwc2.
      destruct (Z.eq_dec (i_op I) OP_TYPE_INT) as [HopI | HnI]; [| destruct (Z.eq_dec (i_op I) OP_TYPE_FLOAT) as [HopF | HnF]].
      +
        pose proof Q22b as Q22I. rewrite HopI in Q22I. unfold OP_TYPE_INT in Q22I.
        pm_seed R2 w c [Z_to_bv 64 (i_io I)].
        seedOR HR E R2 [(10%bv, ELit 1); (22%bv, ELit 21); (23%bv, EVar 39)]. seedHK HK w A M1 model c E X1.
        xruns HR HK 100%nat (0x68944 :: 0x68868 :: 0x69080 :: STOPS) (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
        postrun. name_run HRn R3.
        rreg HRn (23%bv) G23. pose proof HRn as HRn'. oregs_of HRn' OR3 Qgp Qtp. clear HRn HR HK. fixregs2.
        eapply (pm_xrnt_int w c0 K fx I A M1 model c R3 PS FZ FC IP RN1 OR3 HopI (HInt HopI) G23 LK).
      +
        pose proof Q22b as Q22F. rewrite HopF in Q22F. unfold OP_TYPE_FLOAT in Q22F.
        pm_seed R2 w c [Z_to_bv 64 (i_io I)].
        seedOR HR E R2 [(10%bv, ELit 1); (22%bv, ELit 22); (23%bv, EVar 39)]. seedHK HK w A M1 model c E X1.
        xruns HR HK 100%nat (0x68944 :: 0x68868 :: 0x69080 :: STOPS) (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
        postrun. name_run HRn R3.
        rreg HRn (23%bv) G23. pose proof HRn as HRn'. oregs_of HRn' OR3 Qgp Qtp. clear HRn HR HK. fixregs2.
        eapply (pm_xrnt_float w c0 K fx I A M1 model c R3 PS FZ FC IP RN1 OR3 HopF (HFlt HopF) C248 G23 LK).
      +
        pm_seed R2 w c [Z_to_bv 64 (i_op I)].
        seedOR HR E R2 [(10%bv, ELit 1); (22%bv, EVar 39)]. seedHK HK w A M1 model c E X1.
        apply (know_more E M1 [KRange (EVar 39) 0 (2 ^ 16)]) in HK.
        2: { repeat apply Forall_cons; try apply Forall_nil. eapply krange_var; [evs; reflexivity | lia | lia]. }
        xruns HR HK 100%nat (0x68944 :: 0x68868 :: 0x69080 :: STOPS) (SCR [false; true] [] []) 50%N.
        { split_scs; try sc_auto1. all: cbn [sc_denot]; evs; unfold OP_TYPE_INT, OP_TYPE_FLOAT in HnF, HnI; rewrite ?br_eq, ?br_ne by lia; try bool_lia. }
        postrun. name_run HRn R3.
        rreg HRn (15%bv) G15. pose proof HRn as HRn'. oregs_of HRn' OR3 Qgp Qtp. clear HRn HR HK. fixregs2.
        lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ => set (M2 := m) in * end.
        assert (ST2 : stores_in (zwin (w_sp w + 8) (w_sp w + 24)) M1 M2) by (unfold M2; stin).
        assert (RN2 : RNS w I A M2 model c) by (eapply (rns_frame w I A M1 M2 model c _ RN1 ST2); unfold rns_win, zwin, w_sp0, PM_FRAME; intros; lia).
        assert (C16 : cell8 SEGS M2 (w_sp w + 16) 0) by (split; [cbn; lia | unfold M2; change (N.to_nat 8) with 8%nat; rdback]).
        assert (C8 : cell8 SEGS M2 (w_sp w + 8) 0) by (split; [cbn; lia | unfold M2; change (N.to_nat 8) with 8%nat; rdback]).
        clearbody M2.
        eapply (pm_xh5 w c0 K fx I A M2 model c R3 0 0 0 PS FZ FC IP RN2 OR3 G15 C16 C8 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite Z.mod_small by lia; lia) ltac:(rewrite Z.mod_small by lia; lia) Hiwc2 LK).
    -
      pm_seed R2 w c (@nil word).
      seedOR HR E R2 [(10%bv, ELit 0)]. seedHK HK w A M1 model c E X1.
      xruns HR HK 100%nat (0x68944 :: 0x68868 :: 0x69080 :: STOPS) (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
      postrun. name_run HRn R3.
      oregs_of HRn OR3 Qgp Qtp. clear HR HK. fixregs2.
      destruct RN1 as (_ & _ & _ & _ & _ & Hic5 & _ & _ & ACC2 & MACC1 & _).
      eapply (pm_xtail w c0 K fx (i_io I) A M1 model c R3 PS FZ FC X1 Htr BUD OR3 LM1 Hic5 He2 Hw ltac:(lia) MACC1 ltac:(unfold PmLoopU1.lacc; lia) ltac:(lia) LK).
  Qed.
End PM.
End PmExitAU1.

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
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts HStmtsU1 HCommonU1 HLib HFpu HConstsU1.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsNeeds PrsInv PrsStmts PmBaseU1 PmHyps PmHypsU1 PmCoreU1 PmStepU1. Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep2U1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep2U1.PmUpdU1. From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PmStep2U1 PmStep3U1 PmLoopU1 PmInstU1 PmODefsU1 PmZw PmBody1U1 PmExitDiagU1 PmStep5U1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmExitU1.PmExitAU1.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PeLia.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Local Ltac lia ::= pe_lia.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Abbreviation SEGS := Ubsan.M.loaded_segments.
Module Ly := U1Layout.

Definition LOOPK {AC : AllocCeiling} {MI : MallocIface SEGS Ly.L} {ST : StaticsIface SEGS Ly.L} := @PmExitAU1.LOOPK AC MI ST.

Section PM.
Context {AC : AllocCeiling}.
  Context {MI : MallocIface SEGS Ly.L} {ST : StaticsIface SEGS Ly.L}.
  Context {G : grammar} {idesc : Z -> Z -> Prop} {odesc edesc : Z -> Z -> Z -> Prop}
          {generates_type is_ext_inst is_nonsemantic : Z -> bool}
          {ds_rep : AS MI -> mem -> Z -> Z -> Z -> list (Z * Z) -> Prop}.
  Variable CL : pm_calleesU1 SEGS Ly.L MI ST G tcU1 dcU1 nfcU1 HConstsU1.hc ccU1 kcU1
                  idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep.

  #[local] Notation PMX := (PmBaseU1.PMX MI ST).
  #[local] Notation cfg fx R pc M model := (mkCfg (@mkst fx R (Z_to_bv 64 pc) M (seg_rom SEGS)) model).
  #[local] Notation DL := (cu_ds_laws _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
  #[local] Notation IDP := (cu_idesc_ptr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
  #[local] Notation ODP := (cu_odesc_ptr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
  #[local] Notation GOK := (cu_G _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
  #[local] Notation pm_fixword := (PmStepU1.pm_fixword CL).
  #[local] Notation pm_lookup_operand := (PmStep2U1.pm_lookup_operand CL).
  #[local] Notation pm_tail_676a4 := (PmBody1U1.pm_tail_676a4 CL).
  #[local] Notation loop_mem := (PmStepU1.loop_mem (MI:=MI) (ST:=ST)).
  #[local] Notation loop_regs := (PmStepU1.loop_regs (MI:=MI) (ST:=ST)).
  #[local] Notation izero := (PmInstU1.izero).
  #[local] Notation ictx := (PmInstU1.ictx).
  #[local] Notation nodes := (PmLoopU1.nodes).
  #[local] Notation macct := (PmLoopU1.macct).
  #[local] Notation lacc := (PmLoopU1.lacc).
  #[local] Notation LI := (PmLoopU1.LI (MI:=MI) (ST:=ST)).
  #[local] Notation ipure := (PmODefsU1.ipure (G:=G) (idesc:=idesc)).
  #[local] Notation OLI := (PmODefsU1.OLI (MI:=MI) (ST:=ST) (generates_type:=generates_type)).
  #[local] Notation oregs := (PmODefsU1.oregs (MI:=MI) (ST:=ST)).
  #[local] Notation ifr := (PmODefsU1.ifr (MI:=MI) (ST:=ST)).
  #[local] Notation iacc := (PmODefsU1.iacc (generates_type:=generates_type)).
  #[local] Notation OSREGS := (PmODefsU1.OSREGS).
  #[local] Notation pm_h5 := (PmStep5U1.pm_h5 CL).
  #[local] Notation set_m2 := (PmStep5U1.set_m2).
  #[local] Notation pm_D7 := (PmExitDiagU1.pm_D7 CL).
  #[local] Notation pm_D8 := (PmExitDiagU1.pm_D8 CL).
  #[local] Notation pm_D9 := (PmExitDiagU1.pm_D9 CL).
  #[local] Notation ext_val_zx2 := PmInstU1.ext_val_zx2.
  #[local] Notation w_mul_lit := PmExitDiagU1.w_mul_lit.
  #[local] Notation zbv_add := PmBody1U1.zbv_add.
  #[local] Notation zbv_mul := PmBody1U1.zbv_mul.
  #[local] Notation kword_expr := PmBody1U1.kword_expr.
  #[local] Notation kdisj_expr := PmBody1U1.kdisj_expr.

  Ltac fixregs2 := fixregs;
    try replace (Z_to_bv 5 (Z.of_N 10)) with (10%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 11)) with (11%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 12)) with (12%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 13)) with (13%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 15)) with (15%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 18)) with (18%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 21)) with (21%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 22)) with (22%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 23)) with (23%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 26)) with (26%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 27)) with (27%bv : reg) in * by (apply bv_eq; reflexivity).

  #[local] Notation OREGSEED := [(9%bv, EAlu ALU_ADD (EVar 33) (ELit 88)); (18%bv, ELit 1); (19%bv, ELit (2 ^ 61)); (20%bv, ELit 20); (21%bv, EAlu ALU_ADD (EVar 33) (ELit 264)); (25%bv, ELit 5)]%list.
  Tactic Notation "seedOR" ident(HR) constr(E) constr(R) uconstr(extra) :=
    let l := constr:(([(2%bv, EVar 32); (8%bv, EVar 33)] ++ OREGSEED ++ extra) : list (reg * expr)) in
    let l' := eval cbn [app] in l in
    seedHR_ HR E l' R.

  Ltac oregs_of HRn ORn Qgp Qtp :=
    let G2 := fresh "G2" in let G3 := fresh "G3" in let G4 := fresh "G4" in let G8 := fresh "G8" in
    let T9 := fresh "T9" in let T18 := fresh "T18" in let T19 := fresh "T19" in let T20 := fresh "T20" in let T21 := fresh "T21" in let T25 := fresh "T25" in
    rreg HRn (2%bv) G2; rreg HRn (3%bv) G3; rreg HRn (4%bv) G4; rreg HRn (8%bv) G8;
    rreg HRn (9%bv) T9; rreg HRn (18%bv) T18; rreg HRn (19%bv) T19; rreg HRn (20%bv) T20; rreg HRn (21%bv) T21; rreg HRn (25%bv) T25;
    try replace (Z_to_bv 5 (Z.of_N 3)) with (3%bv : reg) in G3 by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 4)) with (4%bv : reg) in G4 by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 8)) with (8%bv : reg) in G8 by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 9)) with (9%bv : reg) in T9 by (apply bv_eq; reflexivity);
    rewrite Qgp in G3; rewrite Qtp in G4; evs_in T9; evs_in T21; rewrite ?w_add in T9 by lia; rewrite ?w_add in T21 by lia;
    lazymatch type of HRn with regs_ok _ _ ?Rn =>
      assert (ORn : oregs _ Rn) by (unfold oregs, loop_regs; rewrite G2, G3, G4, G8, T9, T18, T19, T20, T21, T25; repeat split; reflexivity) end;
    clear G2 G3 G4 G8 T9 T18 T19 T20 T21 T25 HRn.
  Ltac orsplit OR := pose proof OR as OR'; destruct OR' as (Qsp & Qgp & Qtp & Qs0 & Qs1 & Qs2 & Qs3 & Qs4 & Qs5 & Qs9).

  #[local] Notation pm_xrnt := (PmExitAU1.pm_xrnt CL).
  #[local] Notation pm_is_optional := (PmExitAU1.pm_is_optional CL).
  #[local] Notation pm_generates_type := (PmExitAU1.pm_generates_type CL).
  Lemma Z_to_bv64_inj : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> Z_to_bv 64 a = Z_to_bv 64 b -> a = b.
  Proof using.
    intros a b Ha Hb E. apply (f_equal bv_unsigned) in E. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod, !Z.mod_small in E by lia. exact E.
  Qed.
  Lemma oli_regs : forall (w : pmw MI ST) I A M model c R R', OLI w I A M model c R -> oregs w R' -> OLI w I A M model c R'.
  Proof using AC MI ST generates_type.
    intros w I A M model c R R' (OB & rest) OR'. split; [| exact rest].
    destruct OB as (X & Htr & BUD & OR & rest2). split; [exact X|]. split; [exact Htr|]. split; [exact BUD|]. split; [exact OR' | exact rest2].
  Qed.

  Lemma flags_lo_byte : forall M (p v : Z),
    fld SEGS M (p + 92) 2 v -> (v = 0 \/ v = 1) -> cellw SEGS M (p + 92) 1 v.
  Proof using.
    intros M p v F Hv. split; [cbn; lia|]. unfold CRep.fld in *.
    pose proof (rdn_firstn SEGS M 2 (Z_to_bv 64 (p + 92)) _ 1 F ltac:(lia)) as R1.
    change (N.to_nat 1) with 1%nat. rewrite R1. destruct Hv as [-> | ->]; reflexivity.
  Qed.

  Lemma Znth_last : forall (xs : list Z), xs <> [] -> Znth (Zlen xs - 1) xs = last xs 0.
  Proof using.
    intros xs Hne. destruct xs as [|x ys _] using rev_ind; [exfalso; exact (Hne eq_refl)|].
    rewrite last_last, Zlen_app, Zlen_cons, Zlen_nil. replace (Zlen ys + (0 + 1) - 1) with (Zlen ys) by lia. apply Znth_app_r1.
  Qed.

  Lemma iacc_exit : forall (I : ictxR) c, iacc I c -> i_io I + 1 <= c_widx c ->
    (t3b (c_v3 c) = [] \/ (t3b (c_v3 c) <> [] /\ 42 <= last (t3b (c_v3 c)) 0)) ->
    2 * Zlen (t3c (c_m1 c)) <= c_widx c /\ 3 * Zlen (t3c (c_m3 c)) <= c_widx c /\ 2 * Zlen (t3c (c_m2 c)) <= i_io I /\
    (generates_type (i_op I) = true -> 2 <= c_widx c - i_io I).
  Proof using generates_type.
    intros I c ((r & Hr & Hm1 & Hr2 & _) & Hm2 & (p & Hp & Hm3 & HpN & HpI) & G5) Hw1 Hopt.
    split; [destruct (Z.eq_dec r 1) as [E|N]; [specialize (Hr2 E); lia | lia] |].
    split.
    { destruct (Z.eq_dec p 0) as [E|N]; [lia|].
      destruct (Z.eq_dec (i_op I) OP_EXT_INST_IMPORT) as [EI|NI]; [| pose proof (HpN NI); lia].
      destruct (HpI EI) as [[Hp0 _]|[(Hp0 & _)|[_ Hd3]]]; [lia | lia | specialize (Hd3 ltac:(lia)); lia]. }
    split; [exact Hm2|].
    intros Hgt. destruct (G5 Hgt) as [Hd | (ys & E)]; [lia|]. exfalso.
    destruct Hopt as [E0 | [_ H42]]; [rewrite E in E0; destruct ys; discriminate|].
    rewrite E, last_last in H42. cbv in H42. apply H42. reflexivity.
  Qed.

  Lemma pm_x684f0 : forall (w : pmw MI ST) c0 K (fx : FPState) (I : ictxR) A M model c R,
    PMS w c0 K -> frm_zero (@fp_csr fx) -> fconsts fx -> ipure I -> OLI w I A M model c R ->
    i_io I + i_iwc I <= c_widx c ->
    (t3b (c_v3 c) = [] \/ (t3b (c_v3 c) <> [] /\ 42 <= last (t3b (c_v3 c)) 0)) ->
    getr R 11%bv = Z_to_bv 64 (i_io I + i_iwc I) -> getr R 22%bv = Z_to_bv 64 (c_widx c) ->
    getr R 23%bv = Z_to_bv 64 (i_io I) -> getr R 10%bv = Z_to_bv 64 (i_iwc I) ->
    LOOPK w K (i_io I) ->
    srealizes SEGS (cfg fx R 0x68594 M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx I A M model c R PS FZ FC IP HOLI Hle Hopt Q11 Q22 Q23 Q10 LK.
    pose proof HOLI as HOLI'. destruct HOLI' as (OB & Hw1 & ACC & CNT & V2L & V3L & ZW & HTY & IACC).
    pose proof OB as OB'. destruct OB' as (X & Htr & BUD & OR & LM & IC & IFR & Hic & He2 & Hw & MACC & FR3).
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & [Gc2 Gcal] & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof (x_scal X) as (Sc1 & Sc2 & Sc3 & Sc4). pose proof (ipure_ranges I IP) as (Riwc & Rop).
    pose proof IP as IP'. destruct IP' as (_ & _ & _ & _ & Hg & Hdesc & Rio).
    orsplit OR.
    destruct (Z.eq_dec (i_io I + i_iwc I) (c_widx c)) as [Hsum | Hne].
    2: {
         pm_seed R w c [Z_to_bv 64 (i_io I + i_iwc I)].
         seedOR HR E R [(11%bv, EVar 39); (22%bv, EVar 38)]. seedHK HK w A M model c E X.
         apply (know_more E M [KRange (EVar 39) 0 (2 ^ 24)]) in HK.
         2: { repeat apply Forall_cons; try apply Forall_nil. eapply krange_var; [evs; reflexivity | lia | lia]. }
         xruns HR HK 100%nat (0x686a0 :: 0x68840 :: 0x68818 :: STOPS) (SCR [true] [] []) 50%N.
         { split_scs; try sc_auto1. all: cbn [sc_denot]; evs; rewrite ?br_eq, ?br_ne by lia; try bool_lia. }
         postrun. name_run HRn R1.
         oregs_of HRn OR1 Qgp Qtp. clear HR HK. fixregs2.
         exact (pm_D9 w c0 K fx I A M model c R1 PS FZ IP (oli_regs w I A M model c R R1 HOLI OR1)). }

    pose proof (nty_exit (i_op I) (t3b (c_v3 c)) (c_widx c - i_io I) HTY) as NTX.
    assert (HInt : i_op I = OP_TYPE_INT -> 4 <= i_iwc I) by (intros Hop; destruct (NTX (or_introl Hop) Hopt) as [H4 _]; specialize (H4 Hop); lia).
    assert (HFlt : i_op I = OP_TYPE_FLOAT -> 3 <= i_iwc I) by (intros Hop; destruct (NTX (or_intror Hop) Hopt) as [_ H3]; lia).
    destruct (iacc_exit I c IACC Hw1 Hopt) as (LA1 & LA3 & LA2 & HG5).
    rewrite Hsum in Q11.
    pose proof (flags_lo_byte M (w_p w) (c_reqconv c) (x_flags X) Sc4) as Crc.
    pose proof (x_v2 X) as V2. destruct V2 as (_ & _ & _ & V2len & V2blk & V2f0 & _). unfold O_V2 in V2f0.
    assert (Rb2 : 0 <= t3a (c_v2 c) < 2 ^ 64) by (destruct V2blk as [[-> _]|(Hb & _ & _ & Hbc & _)]; [lia | lia]).
    destruct (Gw Hw) as (W1 & W2 & W3 & W4 & W5).
    destruct Sc4 as [Hrc | Hrc]; rewrite Hrc in Crc.
    -
      pm_seed R w c [Z_to_bv 64 (i_io I); Z_to_bv 64 (i_iwc I)].
      seedOR HR E R [(11%bv, EVar 38); (22%bv, EVar 38); (23%bv, EVar 39); (10%bv, EVar 40)]. seedHK HK w A M model c E X.
      apply (know_more E M [KWord (SA (EVar 33) 92) (N.to_nat 1) (ELit 0); KRange (EVar 39) 0 (2 ^ 24); KRange (EVar 34) 1 (2 ^ 47); KAlign (EVar 34) 4]) in HK.
      2: { repeat apply Forall_cons; try apply Forall_nil.
           - eapply kword_var; [exact Crc | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | cbn [edenot]; reflexivity].
           - eapply krange_var; [evs; reflexivity | lia | lia].
           - eapply krange_var; [evs; reflexivity | lia | lia].
           - eapply kalign_var; [evs; reflexivity | lia | lia | exact W2]. }
      xruns HR HK 100%nat (0x686a0 :: 0x68840 :: STOPS) (SCR [false] [] []) 50%N.
      { split_scs; try sc_auto1. all: cbn [sc_denot]; evs; rewrite ?zbv_mul, ?zbv_add; rewrite ?br_eq, ?br_ne, ?br_ltu, ?br_geu by lia; try bool_lia. }
      postrun. name_run HRn R1.
      rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (23%bv) G23. pose proof HRn as HRn'. oregs_of HRn' OR1 Qgp Qtp. clear HRn HR HK. fixregs2.
      evs_in G11. rewrite ?zbv_mul, ?zbv_add, ?w_mul_lit, ?SymExec.alu64_add_lit in G11. rewrite ?w_add in G11 by lia.
      try replace (i_io I * 4) with (4 * i_io I) in G11 by lia.
      eapply (pm_xrnt w c0 K fx I A M model c R1 (w_words w + 4 * i_io I) PS FZ FC IP X Htr BUD OR1 LM IC IFR Hic He2 Hw ACC MACC Hsum LA1 LA3 LA2 ltac:(intros Hgt; specialize (HG5 Hgt); lia) HInt HFlt G11 ltac:(lia) G10 G23 LK).
    -
      pm_seed R w c [Z_to_bv 64 (i_io I); Z_to_bv 64 (i_iwc I); Z_to_bv 64 (t3a (c_v2 c))].
      seedOR HR E R [(11%bv, EVar 38); (22%bv, EVar 38); (23%bv, EVar 39); (10%bv, EVar 40)]. seedHK HK w A M model c E X.
      apply (know_more E M [KWord (SA (EVar 33) 92) (N.to_nat 1) (ELit 1); KRange (EVar 39) 0 (2 ^ 24); KWord (SA (EVar 33) 240) (N.to_nat 8) (EVar 41);
                             KWord (SA (EVar 32) 120) (N.to_nat 8) (EAlu ALU_ADD (EVar 33) (ELit 240))]) in HK.
      2: { repeat apply Forall_cons; try apply Forall_nil.
           - eapply kword_var; [exact Crc | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | cbn [edenot]; reflexivity].
           - eapply krange_var; [evs; reflexivity | lia | lia].
           - eapply kword_var; [eapply fld_cellw; [exact V2f0 | cbn; lia] | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
           - eapply kword_var; [eapply (loop_mem_cell w _ 120 (w_p w + 240) LM); [(first [ solve [cbn [In]; repeat (first [left; reflexivity | right])] | cbn; repeat (first [left; reflexivity | right]) ]) | lia] | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; rewrite w_add by lia; reflexivity]. }
      xruns HR HK 100%nat (0x686a0 :: 0x68840 :: STOPS) (SCR [] [] []) 50%N.
      { split_scs; try sc_auto1. all: cbn [sc_denot]; evs; rewrite ?br_eq, ?br_ne by lia; try bool_lia. }
      postrun. name_run HRn R1.
      rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (23%bv) G23. pose proof HRn as HRn'. oregs_of HRn' OR1 Qgp Qtp. clear HRn HR HK. fixregs2.
      evs_in G11.
      eapply (pm_xrnt w c0 K fx I A M model c R1 (t3a (c_v2 c)) PS FZ FC IP X Htr BUD OR1 LM IC IFR Hic He2 Hw ACC MACC Hsum LA1 LA3 LA2 ltac:(intros Hgt; specialize (HG5 Hgt); lia) HInt HFlt G11 ltac:(lia) G10 G23 LK).
  Qed.

  Lemma pm_xexit : forall (w : pmw MI ST) c0 K (fx : FPState) (I : ictxR) A M model c R',
    PMS w c0 K -> frm_zero (@fp_csr fx) -> fconsts fx -> ipure I -> OLI w I A M model c R' -> i_io I + i_iwc I <= c_widx c ->
    getr R' 22%bv = Z_to_bv 64 (c_widx c) -> getr R' 23%bv = Z_to_bv 64 (i_io I) -> getr R' 10%bv = Z_to_bv 64 (i_iwc I) ->
    getr R' 11%bv = Z_to_bv 64 (i_io I + i_iwc I) -> getr R' 13%bv = Z_to_bv 64 (t3a (c_v3 c)) ->
    getr R' 12%bv = Z_to_bv 64 (t3a (c_v3 c) + 4 * Zlen (t3b (c_v3 c))) ->
    LOOPK w K (i_io I) ->
    srealizes SEGS (cfg fx R' 0x68560 M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx I A M model c R PS FZ FC IP HOLI Hle Q22 Q23 Q10 Q11 Q13 Q12 LK.
    pose proof HOLI as HOLI'. destruct HOLI' as (OB & Hw1 & ACC & CNT & V2L & V3L & ZW & HTY & IACC).
    pose proof OB as OB'. destruct OB' as (X & Htr & BUD & OR & LM & IC & IFR & Hic & He2 & Hw & MACC & FR3).
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & [Gc2 Gcal] & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof (x_scal X) as (Sc1 & Sc2 & Sc3 & Sc4). pose proof (ipure_ranges I IP) as (Riwc & Rop).
    pose proof IP as IP'. destruct IP' as (_ & _ & _ & _ & Hg & Hdesc & Rio).
    orsplit OR.
    pose proof IC as IC'. destruct IC' as (Cio & Cfw & Ciwc & Cop & Fd).
    pose proof (x_v3 X) as V3. destruct V3 as (_ & _ & _ & V3len & V3blk & V3f0 & V3f1 & _ & V3el). unfold O_V3 in V3f0, V3f1.
    set (b3 := t3a (c_v3 c)) in *. set (xs := t3b (c_v3 c)) in *.
    assert (Rb3 : 0 <= b3 /\ b3 + 4 * Zlen xs < 2 ^ 64 /\ (xs = [] \/ 16 <= b3) /\ b3 mod 4 = 0).
    { destruct V3blk as [[Hb0 Hc0]|(Hb & Hal & _ & Hbc & _)]; [rewrite Hb0; unfold Zlen in *|].
      - split; [lia|]. split; [lia|]. split; [left; destruct xs; [reflexivity | cbn in V3len; lia] | reflexivity].
      - split; [lia|]. split; [lia|]. split; [right; pose proof (Z.div_mod b3 16 ltac:(lia)); lia|].
        replace b3 with (b3 / 16 * 4 * 4) by (pose proof (Z.div_mod b3 16 ltac:(lia)); lia). apply Z_mod_mult. }
    destruct Rb3 as (Rb3lo & Rb3hi & Hb16 & Hb4).
    pose proof (Zlen_nonneg xs) as Hl0.
    destruct xs as [|x0 xs'] eqn:Exs.
    -
      change (Zlen (@nil Z)) with 0 in Q12. replace (b3 + 4 * 0) with b3 in Q12 by lia.
      pm_seed R w c [Z_to_bv 64 b3; Z_to_bv 64 (i_io I + i_iwc I); Z_to_bv 64 (i_io I); Z_to_bv 64 (i_iwc I)].
      seedOR HR E R [(13%bv, EVar 39); (12%bv, EVar 39); (11%bv, EVar 40); (22%bv, EVar 38); (23%bv, EVar 41); (10%bv, EVar 42)].
      seedHK HK w A M model c E X.
      xruns HR HK 100%nat (0x68594 :: STOPS) (SCR [true] [] []) 50%N.
      { split_scs; try sc_auto1. all: cbn [sc_denot]; evs; rewrite ?br_eq, ?br_ne by lia; try bool_lia. }
      postrun. name_run HRn R1.
      rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (22%bv) G22. rreg HRn (23%bv) G23.
      pose proof HRn as HRn'. oregs_of HRn' OR1 Qgp Qtp. clear HRn HR HK. fixregs2.
      eapply (pm_x684f0 w c0 K fx I A M model c R1 PS FZ FC IP (oli_regs w I A M model c R R1 HOLI OR1) Hle); [left; exact Exs | exact G11 | exact G22 | exact G23 | exact G10 | exact LK].
    -
      assert (Hne : xs <> []) by (rewrite Exs; discriminate). rewrite <- Exs in *. clear x0 xs' Exs.
      assert (Hl1 : 1 <= Zlen xs) by (destruct xs as [|z zs]; [exfalso; exact (Hne eq_refl) | rewrite Zlen_cons; pose proof (Zlen_nonneg zs); lia]).
      destruct Hb16 as [E0 | Hb16]; [exfalso; exact (Hne E0)|].
      destruct (V3el (Zlen xs - 1) ltac:(lia)) as [Rxl Fxl]. rewrite (Znth_last xs Hne) in Rxl, Fxl.
      set (xl := last xs 0) in *.
      assert (Rxl31 : 0 <= xl < 2 ^ 31) by (subst xl; apply Forall_last; [exact FR3 | lia]).
      replace (b3 + 4 * (Zlen xs - 1)) with (b3 + 4 * Zlen xs + -4) in Fxl by lia.
      pm_seed R w c [Z_to_bv 64 b3; Z_to_bv 64 (b3 + 4 * Zlen xs); Z_to_bv 64 xl].
      seedOR HR E R [(13%bv, EVar 39); (12%bv, EVar 40)]. seedHK HK w A M model c E X.
      apply (know_more E M [KWord (SA (EVar 40) (-4)) (N.to_nat 4) (EVar 41); KRange (EVar 40) 20 (2 ^ 64 - 1); KAlign (EVar 40) 4; KRange (EVar 41) 0 (2 ^ 31 - 1)]) in HK.
      2: { repeat apply Forall_cons; try apply Forall_nil.
           - eapply kword_var; [eapply fld_cellw; [exact Fxl | cbn; lia] | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
           - eapply krange_var; [evs; reflexivity | lia | lia].
           - eapply kalign_var; [evs; reflexivity | lia | lia | ].
             replace (b3 + 4 * Zlen xs) with (b3 + Zlen xs * 4) by lia. rewrite Z_mod_plus_full. exact Hb4.
           - eapply krange_var; [evs; reflexivity | lia | lia]. }
      xruns HR HK 100%nat STOPS (SCR [false] [] []) 50%N.
      { split_scs; try sc_auto1. all: cbn [sc_denot]; evs; rewrite ?br_eq, ?br_ne by lia; try bool_lia. }
      postrun. name_run HRn R1.
      rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10.
      pose proof HRn as HRn'. oregs_of HRn' OR1 Qgp Qtp. clear HRn HR HK. fixregs2.
      rewrite ?ext_val_sx4, ?sx32_small in G10 by lia.
      assert (Rxl32 : 0 <= xl < 2 ^ 32) by lia.
      eapply (pm_is_optional w A M model c fx R1 _ K X (ex_intro _ xl (conj Rxl32 G10)) G1 ltac:(apply bv_eq; vm_compute; reflexivity)).
      intros R2 KEPT (b & Gb & Hb). pose proof (oregs_kept w R1 R2 OR1 KEPT) as OR2. keptQ KEPT G2 Qsp_R2. keptQ KEPT G8 Qs0_R2.
      clear G1 G2 G8 KEPT. clear Qsp Qgp Qtp Qs0 Qs1 Qs2 Qs3 Qs4 Qs5 Qs9. orsplit OR2.
      destruct b; cbn in Gb.
      +
        destruct (Hb eq_refl) as (x' & Rx' & Gx'). rewrite G10 in Gx'. apply Z_to_bv64_inj in Gx'; [| lia | lia]. subst x'.
        pm_seed R2 w c [Z_to_bv 64 (i_io I); Z_to_bv 64 (i_iwc I)].
        seedOR HR E R2 [(10%bv, ELit 1)]. seedHK HK w A M model c E X.
        apply (know_more E M [KWord (SA (EVar 32) 216) (N.to_nat 8) (EVar 39); KWord (SA (EVar 32) 234) (N.to_nat 2) (EVar 40);
                               KRange (EVar 39) 0 (2 ^ 24); KRange (EVar 40) 0 (2 ^ 16 - 1)]) in HK.
        2: { repeat apply Forall_cons; try apply Forall_nil.
             - eapply kword_var; [exact Cio | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
             - eapply kword_var; [exact Ciwc | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
             - eapply krange_var; [evs; reflexivity | lia | lia].
             - eapply krange_var; [evs; reflexivity | lia | lia]. }
        xruns HR HK 100%nat (0x68594 :: STOPS) (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
        postrun. name_run HRn R3.
        rreg HRn (10%bv) G10b. rreg HRn (11%bv) G11. rreg HRn (22%bv) G22. rreg HRn (23%bv) G23.
        pose proof HRn as HRn'. oregs_of HRn' OR3 Qgp Qtp. clear HRn HR HK. fixregs2.
        rewrite ?ext_val_zx2 in G10b, G11 by lia. evs_in G11. rewrite ?w_add in G11 by lia. evs_in G22.
        eapply (pm_x684f0 w c0 K fx I A M model c R3 PS FZ FC IP (oli_regs w I A M model c R R3 HOLI OR3) Hle); [right; split; [exact Hne | subst xl xs b3; lia] | exact G11 | exact G22 | exact G23 | exact G10b | exact LK].
      +
        pm_seed R2 w c (@nil word).
        seedOR HR E R2 [(10%bv, ELit 0)]. seedHK HK w A M model c E X.
        xruns HR HK 100%nat (0x68770 :: 0x68594 :: STOPS) (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
        postrun. name_run HRn R3.
        oregs_of HRn OR3 Qgp Qtp. clear HR HK. fixregs2.
        exact (pm_D8 w c0 K fx I A M model c R3 PS FZ IP (oli_regs w I A M model c R R3 HOLI OR3)).
  Qed.
End PM.
