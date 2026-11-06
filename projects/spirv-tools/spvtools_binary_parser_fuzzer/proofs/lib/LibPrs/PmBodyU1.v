(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
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
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsNeeds OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsInv OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmBaseU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmHyps OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmHypsU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmCoreU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStepU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep2U1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep3U1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmLoopU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmInstU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmODefsU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmZw OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmBody1U1.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PeLia.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Module PmBody2U1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.

Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PropExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SeqExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StepTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.WalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StartupTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SumWalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StoreOk OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MemSplit OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Hoare OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ShapeAlg OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SRealizes OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefReadLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.FPSteps OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibIface OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibBudget OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibEff OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MmapSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibMaskBits OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ZStores OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3Sound OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymRun3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.U1Layout.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.CRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.StrLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.LiveStats OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContStmts2 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.U1Facts.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRepFacts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HStmtsU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HCommonU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HFpu OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HConstsU1.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsNeeds OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsInv OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmBaseU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmHyps OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmHypsU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmCoreU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStepU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep2U1.PmUpdU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep2U1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep3U1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmLoopU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmInstU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmBody1U1.PmClearU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmBody1U1.
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
  #[local] Notation pm_put_cstr := (PmStepU1.pm_put_cstr CL).
  #[local] Notation pm_put_u16 := (PmStepU1.pm_put_u16 CL).
  #[local] Notation pm_pdiagQ := (PmStepU1.pm_pdiagQ CL).
  #[local] Notation pm_dtor := (PmStepU1.pm_dtor CL).
  #[local] Notation pm_latch_err := (PmLoopU1.pm_latch_err (MI:=MI) (ST:=ST)).
  #[local] Notation pm_fixword := (PmStepU1.pm_fixword CL).
  #[local] Notation pm_ecw_pbs2 := (PmStep2U1.pm_ecw_pbs2 CL).
  #[local] Notation pm_opcode_split := (PmStep2U1.pm_opcode_split CL).
  #[local] Notation pm_lookup_opcode := (PmStep2U1.pm_lookup_opcode CL).
  #[local] Notation loop_mem := (PmStepU1.loop_mem (MI:=MI) (ST:=ST)).
  #[local] Notation loop_regs := (PmStepU1.loop_regs (MI:=MI) (ST:=ST)).

  #[local] Notation pm_idesc_operands := (PmStep3U1.pm_idesc_operands CL).
  #[local] Notation pm_push_types := (PmStep3U1.pm_push_types CL).
  #[local] Notation GOK := (cu_G _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
  #[local] Notation MAXLEN := (cu_maxlen _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).

  Ltac lrsplit LR := let H := fresh "LRc" in pose proof LR as H;
    destruct H as (?LQ2 & ?LQ3 & ?LQ4 & ?LQ8 & ?LQ9 & ?LQ18 & ?LQ19 & ?LQ20 & ?LQ21 & ?LQ25).
  Tactic Notation "seedLR" ident(HR) constr(E) constr(R) uconstr(extra) :=
    let l := constr:(([(2%bv, EVar 32); (8%bv, EVar 33); (9%bv, EAlu ALU_ADD (EVar 33) (ELit 88)); (18%bv, ELit 1); (19%bv, ELit (2 ^ 61));
                        (20%bv, ELit 20); (21%bv, EAlu ALU_ADD (EVar 33) (ELit 264)); (25%bv, ELit 5)] ++ extra) : list (reg * expr)) in
    let l' := eval cbn [app] in l in
    seedHR_ HR E l' R.

  Ltac lregs HRn LRn Qgp Qtp :=
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
      assert (LRn : loop_regs _ Rn) by (unfold loop_regs; rewrite G2, G3, G4, G8, T9, T18, T19, T20, T21, T25; repeat split; reflexivity) end;
    clear G2 G3 G4 G8 T9 T18 T19 T20 T21 T25 HRn.

  Lemma zbv_add : forall a b, alu64 ALU_ADD (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
  Proof using. intros. exact (PmBody1U1.zbv_add a b). Qed.
  Lemma zbv_mul : forall a b, mul_div M_MUL (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a * b).
  Proof using. intros. exact (PmBody1U1.zbv_mul a b). Qed.

  Lemma op_list_range : forall op l, g_op G op = Some l -> Forall (fun t => 0 <= t < 2 ^ 31) l.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros op l Hg. apply Forall_forall. intros t Ht. eapply (go_range G GOK l t); [left; exists op; exact Hg | exact Ht].
  Qed.

  #[local] Notation IDP := (cu_idesc_ptr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).

  Lemma pm_B2 : forall (w : pmw MI ST) c0 K (fx : FPState) A M model c R (io fw iwc op d : Z) (l : list Z),
    PMS w c0 K -> PMX w A M model c -> c_tr c = [] -> pm_bud (w_n w) c -> loop_regs w R -> loop_mem w M -> izero w M ->
    ictx w M io fw iwc op d -> g_op G op = Some l -> idesc d op ->
    (forall A' M' model' R' (b' cap' : Z),
        PMX w A' M' model' (set_v3 c (b', push_types l [], cap')) -> pm_bud (w_n w) (set_v3 c (b', push_types l [], cap')) ->
        loop_regs w R' -> loop_mem w M' -> izero w M' -> ictx w M' io fw iwc op d ->
        srealizes SEGS (cfg fx R' 0x677d0 M' model') K) ->
    srealizes SEGS (cfg fx R 0x67758 M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx A M model c R io fw iwc op d l PS X Htr BUD LR LM IZ IC Hg Hdesc HEADK.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & [Gc2 Gcal] & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof LR as LR'. destruct LR' as (Qsp & Qgp & Qtp & Qs0 & Qs1 & Qs2 & Qs3 & Qs4 & Qs5 & Qs9).
    pose proof IC as IC'. destruct IC' as (Cio & Cfw & Ciwc & Cop & Fd).
    destruct (IDP d op Hdesc) as (Hd0 & Hd1 & Hd4).
    pose proof (x_v3 X) as V3. destruct V3 as (_ & _ & _ & V3len & V3blk & V3f0 & V3f1 & _). unfold O_V3 in V3f0, V3f1.
    set (b3 := t3a (c_v3 c)) in *. set (xs := t3b (c_v3 c)) in *. set (cap3 := t3c (c_v3 c)) in *.
    assert (Eb3 : b3 = t3a (c_v3 c)) by reflexivity. assert (Ec3 : cap3 = t3c (c_v3 c)) by reflexivity. clearbody b3 xs cap3.
    assert (Hb3 : 0 <= b3 /\ b3 + 4 * cap3 <= 2 ^ 63 /\ (cap3 = 0 \/ 16 <= b3) /\ 0 <= cap3).
    { destruct V3blk as [[Hb0 Hc0]|(Hb0 & Hal0 & Hc0 & Hbc & _)].
      { split; [lia|]; split; [lia|]; split; [left; lia | lia]. }
      split; [lia|]. split; [lia|]. split; [|lia]. right. pose proof (Z.div_mod b3 16 ltac:(lia)). lia. }
    destruct Hb3 as (Hb3lo & Hb3hi & Hb3al & Hc3).
    pose proof (fld_cellw M _ 8 _ V3f0 ltac:(lia)) as C264.
    pose proof (fld_cellw M _ 8 _ V3f1 ltac:(lia)) as C272. replace (w_p w + 264 + 8) with (w_p w + 272) in C272 by lia.
    pose proof (fld_cellw M _ 8 _ Fd ltac:(lia)) as C224.

    pm_seed R w c [Z_to_bv 64 b3; Z_to_bv 64 (Zlen xs); Z_to_bv 64 d].
    seedLR HR E R (@nil (reg * expr)).
    seedHK HK w A M model c E X.
    apply (know_more E M [KWord (SA (EVar 33) 264) (N.to_nat 8) (EVar 39); KWord (SA (EVar 33) 272) (N.to_nat 8) (EAlu ALU_ADD (EVar 39) (EMd M_MUL (ELit 4) (EVar 40)));
                          KWord (SA (EVar 32) 224) (N.to_nat 8) (EVar 41); KRange (EVar 41) 0x10000 (2 ^ 40); KAlign (EVar 41) 4]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil.
         - eapply kword_var; [exact C264 | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
         - eapply kword_var; [exact C272 | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; rewrite zbv_mul, zbv_add; reflexivity].
         - eapply kword_var; [exact C224 | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
         - eapply krange_var; [evs; reflexivity | lia | lia].
         - eapply kalign_var; [evs; reflexivity | lia | lia | exact Hd4]. }
    assert (AFTER : forall R1 (M1 := wbytes M (Z_to_bv 64 (w_p w + 272)) (word_to_le_bytes 8 (Z_to_bv 64 b3))),
              loop_regs w R1 -> getr R1 10%bv = Z_to_bv 64 d -> getr R1 1%bv = Z_to_bv 64 0x67794 ->
              srealizes SEGS (cfg fx R1 0x6c790 M1 model) K).
    { intros R1 M1 LR1 G10 G1. lrsplit LR1.
      assert (ST1 : stores_in (zwin (w_p w + 272) (w_p w + 280)) M M1) by (unfold M1; stin).
      pose proof (pm_v3_clear w A M model c b3 X ltac:(symmetry; exact Eb3)) as X1. change (wbytes M _ _) with M1 in X1. rewrite <- Ec3 in X1.
      set (c1 := set_v3 c (b3, [], cap3)) in *.
      eapply (loop_mem_frame w M M1) in LM; [| lia | lia | eapply stores_in_agree; [exact ST1 | unfold zwin; intros; lia]].
      eapply (izero_agree w M M1) in IZ; [| lia | lia | eapply stores_in_agree; [exact ST1 | unfold zwin; intros; lia]].
      eapply (ictx_agree w M M1) in IC; [| lia | lia | eapply stores_in_agree; [exact ST1 | unfold zwin; intros; lia]].
      clear ST1 HK HR E. clearbody M1. pose proof (x_ms X1) as MS1.
      assert (Htr1 : c_tr c1 = []) by (cbn [c1 set_v3 c_tr]; exact Htr).
      assert (BUD1 : pm_bud (w_n w) c1).
      { destruct BUD as (Bq1 & Bq2 & Bq3 & Bq4 & Bq5 & Bq6 & Bq7 & Bq8 & Bq9). unfold pm_bud. cbn [c1 set_v3 c_m1 c_m2 c_m3 c_v1 c_v2 c_v3 c_tr t3a t3b t3c fst snd].
        rewrite ?Ec3. repeat (split; [assumption|]). exact Bq9. }

      eapply (pm_idesc_operands w A M1 model c1 fx R1 _ K X1 (ex_intro _ d (ex_intro _ op (conj Hdesc G10))) G1 ltac:(apply bv_eq; vm_compute; reflexivity)).
      intros R2 KEPT POST. destruct (POST d op Hdesc G10) as (p & l' & Hg' & RS & Hp4 & Qa0 & Qa1).
      rewrite Hg in Hg'. injection Hg'. intros El. subst l'.
      pose proof (loop_regs_kept w R1 R2 LR1 KEPT) as LR2. clear KEPT POST G1 G10. clear LQ2 LQ3 LQ4 LQ8 LQ9 LQ18 LQ19 LQ20 LQ21 LQ25. lrsplit LR2.
      pose proof RS as RS'. destruct RS' as (Rp0 & Rp1 & _).
      pose proof (go_len_op G GOK op l Hg) as Hll. unfold HRep.Zlength in Hll. change (Zlen l <= g_maxlen G) in Hll. pose proof MAXLEN as Hml.
      assert (Hl0 : 0 <= Zlen l) by (unfold Zlen; lia).

      pm_seed R2 w c1 [Z_to_bv 64 p; Z_to_bv 64 (Zlen l)].
      seedLR HR E R2 [(10%bv, EVar 39); (11%bv, EVar 40)]. seedHK HK w A M1 model c1 E X1.
      xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
      postrun. name_run HRn R3.
      rreg HRn (1%bv) G1. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. pose proof HRn as HRn'. lregs HRn' LR3 LQ3 LQ4.
      rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. clear HRn HR HK. fixregs.
      rewrite LQ3 in G3. rewrite LQ4 in G4. evs_in G10. evs_in G11. rewrite ?w_add in G10 by lia. rewrite ?w_add in G11 by lia.
      lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ => set (M2 := m) in * end.
      assert (ST2 : stores_in (zwin (w_sp w + 304) (w_sp w + 320)) M1 M2) by (unfold M2; stin).
      assert (X2 : PMX w A M2 model c1).
      { eapply (pmx_frame_stores SEGS Ly.L MI ST ly_img_low ly_rw_img ly_relro_img w A M1 M2 model c1 (zwin (w_sp w + 304) (w_sp w + 320)));
          [exact X1 | exact ST2 | unfold zwin, w_sp0, PM_FRAME; intros; lia]. }
      eapply (loop_mem_frame w M1 M2) in LM; [| lia | lia | eapply stores_in_agree; [exact ST2 | unfold zwin; intros; lia]].
      eapply (izero_agree w M1 M2) in IZ; [| lia | lia | eapply stores_in_agree; [exact ST2 | unfold zwin; intros; lia]].
      eapply (ictx_agree w M1 M2) in IC; [| lia | lia | eapply stores_in_agree; [exact ST2 | unfold zwin; intros; lia]].
      assert (Fp : fld SEGS M2 (w_sp w + 304) 8 p) by (unfold M2; rdback).
      assert (Fl : fld SEGS M2 (w_sp w + 304 + 8) 8 (Zlen l)) by (unfold M2; replace (w_sp w + 304 + 8) with (w_sp w + 312) by lia; rdback).
      clear ST2 X1 MS1. clearbody M2. clear M1. pose proof (x_ms X2) as MS2.
      eapply (pm_push_types w c0 K fx A M2 model c1 R3 (w_sp w + 304) p _ l PS X2 Htr1 BUD1 ltac:(cregs_tac G1 G2 G3 G4) G10);
        [unfold O_V3; exact G11 | exact Fp | exact Fl | exact RS | exact Hp4 | lia | exact (op_list_range op l Hg)
        | lia | unfold w_sp0, PM_FRAME; lia | cbn [c1 set_v3 c_v3 t3b fst snd]; unfold V3MAX, Zlen in *; cbn [length Z.of_nat]; lia |].
      intros A3 R4 M3 model3 b' cap' X3 BUD3 KEPT AG.
      pose proof (loop_regs_kept w R3 R4 LR3 KEPT) as LR4. clear G1 G2 G3 G4 G8 G10 G11 KEPT LR3.
      eapply (loop_mem_frame w M2 M3) in LM; [| lia | lia | eapply agree_on_weaken; [exact AG | unfold zwin, w_sp0, PM_FRAME; intros; lia]].
      eapply (izero_agree w M2 M3) in IZ; [| lia | lia | eapply agree_on_weaken; [exact AG | unfold zwin, w_sp0, PM_FRAME; intros; lia]].
      eapply (ictx_agree w M2 M3) in IC; [| lia | lia | eapply agree_on_weaken; [exact AG | unfold zwin, w_sp0, PM_FRAME; cbn; intros; lia]].
      clear AG X2 MS2 Fp Fl. pose proof (x_ms X3) as MS3.
      set (c3 := set_v3 c1 (b', push_types l [], cap')) in *.

      pm_seed R4 w c3 (@nil word). clear LQ2 LQ3 LQ4 LQ8 LQ9 LQ18 LQ19 LQ20 LQ21 LQ25. lrsplit LR4.
      seedLR HR E R4 (@nil (reg * expr)). seedHK HK w A3 M3 model3 c3 E X3.
      xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
      postrun. name_run HRn R5. lregs HRn LR5 LQ3 LQ4. clear HR HK.
      eapply (HEADK A3 M3 model3 R5 b' cap');
        cbn [c3 c1 set_v3 c_m1 c_m2 c_m3 c_v1 c_v2 c_v3 c_tr t3a t3b t3c fst snd] in X3, BUD3 |- *; first [exact X3 | exact BUD3 | exact LR5 | exact LM | exact IZ | exact IC]. }
    destruct (Z.eq_dec (Zlen xs) 0) as [Hz|Hnz].
    -
      xruns HR HK 100%nat (0x67764 :: STOPS) (SCR [true] [] []) 50%N.
      { split_scs; try sc_auto1. all: cbn [sc_denot]; evs; rewrite ?zbv_mul, ?zbv_add; rewrite ?br_eq, ?br_ne, ?br_geu, ?br_ltu by lia; bool_lia. }
      postrun. name_run HRn R1.
      rreg HRn (1%bv) G1. rreg HRn (10%bv) G10. lregs HRn LR1 Qgp Qtp. fixregs. evs_in G10.
      apply (AFTER R1 LR1 G10 G1).
    -
      xruns HR HK 100%nat (0x67764 :: STOPS) (SCR [false] [] []) 50%N.
      { split_scs; try sc_auto1. all: cbn [sc_denot]; evs; rewrite ?zbv_mul, ?zbv_add; rewrite ?br_eq, ?br_ne, ?br_geu, ?br_ltu by lia; bool_lia. }
      postrun. name_run HRn R1.
      rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (25%bv) G25. pose proof HRn as HRn'. lregs HRn' LR1 Qgp Qtp. fixregs.
      evs_in G10. evs_in G11. rewrite ?zbv_mul, ?zbv_add in G10.
      destruct (cd4_gen (fx:=fx) 0x67764 0x67774 10%bv 11%bv M b3 (Z.to_nat (Zlen xs)) R1 (or_intror (conj eq_refl (conj eq_refl (conj eq_refl eq_refl))))
                  ltac:(rewrite G10; f_equal; lia) G11 G25 ltac:(lia) ltac:(lia) ltac:(lia)) as (R1' & RUN & KQ' & G10').
      eapply srz_msteps; [exact (ms_halt _ MS) | exact (ms_lazy _ MS) | exact RUN |].
      assert (KQ : forall r, In r (all_but 10%bv) -> getr R1' r = getr R1 r) by exact KQ'.
      assert (LR1' : loop_regs w R1').
      { lrsplit LR1. unfold loop_regs. rewrite !KQ by (vm_compute; repeat (first [left; reflexivity | right])). repeat split; assumption. }
      assert (G11' : getr R1' 11%bv = Z_to_bv 64 b3) by (rewrite KQ by (vm_compute; repeat (first [left; reflexivity | right])); exact G11).
      clear HRn HR HK KQ KQ' RUN G10 G11 G25 LR1.

      lrsplit LR1'.
      pm_seed R1' w c [Z_to_bv 64 b3; Z_to_bv 64 d].
      seedLR HR E R1' [(11%bv, EVar 39)].
      seedHK HK w A M model c E X.
      apply (know_more E M [KWord (SA (EVar 32) 224) (N.to_nat 8) (EVar 40); KRange (EVar 40) 0x10000 (2 ^ 40); KAlign (EVar 40) 4]) in HK.
      2: { repeat apply Forall_cons; try apply Forall_nil.
           - eapply kword_var; [exact C224 | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
           - eapply krange_var; [evs; reflexivity | lia | lia].
           - eapply kalign_var; [evs; reflexivity | lia | lia | exact Hd4]. }
      xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
      postrun. name_run HRn R2.
      rreg HRn (1%bv) G1. rreg HRn (10%bv) G10. lregs HRn LR2 LQ3 LQ4. fixregs. evs_in G10.
      apply (AFTER R2 LR2 G10 G1).
  Qed.
End PM.
End PmBody2U1.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmExitDiagU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep5U1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmOLoopU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmOLoop2U1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmOHeadU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmDispatchU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmExitU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmHdrDiagU1.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablStmtsHdr.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Module U1_code_67484_67498.

Import Stdlib.ZArith.ZArith.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Ubsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_67484 : bv 32 := 0xf0070453.
Lemma F_67484 : fetch_word Ubsan.M.loaded_segments (0x674c4 : word) = Some W_67484.
Proof. vm_refl. Qed.
Lemma D_67484 : decode_any W_67484 = Some (Fmv FMV_F_X FMT_S 8 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_6748c : bv 32 := 0xf00784d3.
Lemma F_6748c : fetch_word Ubsan.M.loaded_segments (0x674cc : word) = Some W_6748c.
Proof. vm_refl. Qed.
Lemma D_6748c : decode_any W_6748c = Some (Fmv FMV_F_X FMT_S 9 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_67494 : bv 32 := 0xf0080953.
Lemma F_67494 : fetch_word Ubsan.M.loaded_segments (0x674d4 : word) = Some W_67494.
Proof. vm_refl. Qed.
Lemma D_67494 : decode_any W_67494 = Some (Fmv FMV_F_X FMT_S 18 16, 4%Z).
Proof. vm_refl. Qed.
End U1_code_67484_67498.

Module PmHdrU1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.

Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PropExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SeqExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StepTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.WalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StartupTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SumWalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StoreOk OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MemSplit OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Hoare OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ShapeAlg OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SRealizes OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefReadLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.FPSteps OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibIface OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibBudget OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibEff OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MmapSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibMaskBits OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ZStores OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3Sound OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymRun3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.U1Layout.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.CRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.StrLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.LiveStats OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContStmts2 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.U1Facts.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRepFacts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HStmtsU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HCommonU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HFpu OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HConstsU1.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablStmtsHdr.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsNeeds OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsInv OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmBaseU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmHyps OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmHypsU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmCoreU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStepU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmLoopU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmHdrDiagU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmBodyU1.U1_code_67484_67498.
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
  #[local] Notation pm_binend := (PmStepU1.pm_binend CL).
  #[local] Notation pm_is_host_endian := (PmStepU1.pm_is_host_endian CL).
  #[local] Notation pm_D2 := (PmHdrDiagU1.pm_D2 CL).
  #[local] Notation pm_D3 := (PmHdrDiagU1.pm_D3 CL).
  #[local] Notation pm_D4 := (PmHdrDiagU1.pm_D4 CL).
  #[local] Notation hdr_stmt := (PmLoopU1.hdr_stmt (MI:=MI) (ST:=ST)).

  Lemma pm_header_get : forall (w : pmw MI ST) A M model c (fx : FPState) R (ret : Z) K,
    PMX w A M model c -> w_words w <> 0 -> 5 <= w_n w -> c_endian c < 2 ->
    fld SEGS M (w_sp w + 160) 8 (w_words w) -> fld SEGS M (w_sp w + 168) 8 (w_n w) ->
    getr R 10%bv = Z_to_bv 64 (w_sp w + 160) -> getr R 11%bv = Z_to_bv 64 (c_endian c) -> getr R 12%bv = Z_to_bv 64 (w_sp w + 128) ->
    getr R 2%bv = Z_to_bv 64 (w_sp w) -> getr R 1%bv = Z_to_bv 64 ret -> ret_ok (Z_to_bv 64 ret) ->
    (forall R' M' (r : Z), kept R R' -> getr R' 10%bv = Z_to_bv 64 r -> (r = 0 \/ r = -4) ->
        PMX w A M' model (set_scal c (c_widx c) (c_icount c) (c_endian c) (c_reqconv c)) ->
        CRep.agree_on (fun a => w_sp w + 160 <= a < w_sp0 w) M M' ->
        srealizes SEGS (cfg fx R' ret M' model) K) ->
    srealizes SEGS (cfg fx R 0x66680 M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w A M model c fx R ret K X Hw Hn He F160 F168 Ha0 Ha1 Ha2 Hsp Hra Hret CONT.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & [Gc2 Gcal] & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    destruct (Gw Hw) as (W1 & W2 & W3 & W4 & W5). pose proof (x_scal X) as (S1 & S2 & S3 & S4).
    assert (WD : forall t n, w_sp w + 864 - w_STK w <= t -> t + n <= w_sp w + 864 -> mdef M t n).
    { intros t n Ht Hn' i Hi. pose proof (x_wdef X (t + i - (w_sp w + 864 - w_STK w)) ltac:(unfold w_sp0, PM_FRAME; lia)) as D.
      unfold w_sp0, PM_FRAME in D. replace (w_sp w + 864 - w_STK w + (t + i - (w_sp w + 864 - w_STK w))) with (t + i) in D by lia. exact D. }
    destruct (cu_header_get _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL fx R M (w_sp w + 160) (w_sp w + 128) (w_words w) (w_n w) (c_endian c) (w_sp w) (Z_to_bv 64 ret)
                (x_roc X) Ha0 Ha1 Ha2 Hsp F160 ltac:(replace (w_sp w + 160 + 8) with (w_sp w + 168) by lia; exact F168)
                ltac:(split; [exact Hn | lia]) W1 W3
                ltac:(eapply mdef_sub; [exact (x_wbuf X Hw) | lia | lia]) ltac:(lia)
                ltac:(lia) ltac:(lia) ltac:(apply WD; lia) ltac:(lia) ltac:(lia)
                ltac:(apply mod16_8; [exact Gsp16 | reflexivity]) ltac:(apply mod16_8; [exact Gsp16 | reflexivity]) W2
                ltac:(intros a Ha; unfold zwin in *; split; [lia | split; [lia|]]; intros Hx; destruct (W5 a ltac:(unfold zwin; lia)) as [Hnw _]; unfold zwin in Hnw; lia)
                ltac:(intros a Ha; unfold zwin in *; split; [lia|]; intros Hx; destruct (W5 a ltac:(unfold zwin; lia)) as [Hnw _]; unfold zwin in Hnw; lia)
                ltac:(unfold stack_room; apply (mdef_store_ok SEGS M _ 32); [apply WD; lia | lia | lia | lia])
                ltac:(lia) ltac:(lia) Gsp16 Hra Hret)
      as (R' & M' & r & MSx & KP & Hr & Hr04 & FE & DK).
    pose proof (stores_in_of_frame_eq _ M M' FE DK) as SI.
    eapply srz_msteps; [exact (ms_halt _ MS) | exact (ms_lazy _ MS) | exact MSx |].
    eapply (CONT R' M' r KP Hr Hr04).
    - eapply (pmx_stores SEGS Ly.L MI ST ly_img_low ly_rw_img ly_relro_img); [exact X | exact SI | | | | | | lia | lia | lia | exact S4].
      + intros a [Ha|Ha]; unfold zwin, scal_win, w_sp0, PM_FRAME, O_WIDX, O_FLAGS in *; [left; lia | left; lia].
      + eapply fld_keep; [exact SI | exact (x_widx X) | unfold O_WIDX; lia | unfold O_WIDX; cbn; lia | unfold O_WIDX, zwin; cbn; intros; lia].
      + eapply fld_keep; [exact SI | exact (x_icount X) | unfold O_ICOUNT; lia | unfold O_ICOUNT; cbn; lia | unfold O_ICOUNT, zwin; cbn; intros; lia].
      + eapply fld_keep; [exact SI | exact (x_endian X) | unfold O_ENDIAN; lia | unfold O_ENDIAN; cbn; lia | unfold O_ENDIAN, zwin; cbn; intros; lia].
      + eapply fld_keep; [exact SI | exact (x_flags X) | unfold O_FLAGS; lia | unfold O_FLAGS; cbn; lia | unfold O_FLAGS, zwin; cbn; intros; lia].
    - eapply stores_in_agree; [exact SI|]. intros a Ha. unfold zwin. split; [lia | lia].
  Qed.

  Ltac fmv_step MS Fx Dx znext :=
    eapply srz_msteps; [eapply ms_halt; exact MS | eapply ms_lazy; exact MS | | ];
    [ norm_pc; eapply msteps_one; [reflexivity|]; eapply fp_step_fmv_w_x; [exact Fx | reflexivity | exact Dx]
    | lazymatch goal with |- srealizes _ (mkCfg (mkst _ ?pc _ _) _) _ =>
        replace pc with (Z_to_bv 64 znext : word) by (apply bv_eq; vm_compute; reflexivity) end ].

  Lemma pm_hdrB : forall (w : pmw MI ST) c0 K (fx : FPState) A M model c R,
    PMS w c0 K -> PMX w A M model c -> c_tr c = [] -> pm_bud (w_n w) c -> 5 <= w_n w -> c_widx c <= 5 -> c_endian c < 2 -> c_icount c = 0 ->
    frm_zero (@fp_csr fx) ->
    getr R 8%bv = Z_to_bv 64 (w_p w) -> getr R 9%bv = Z_to_bv 64 (w_p w + 88) -> getr R 2%bv = Z_to_bv 64 (w_sp w) ->
    getr R 3%bv = Z_to_bv 64 (ly_gp Ly.L) -> getr R 4%bv = Z_to_bv 64 (ly_tp Ly.L) ->
    (forall (fx1 : FPState) A' M' model' c' R', frm_zero (@fp_csr fx1) -> fconsts fx1 ->
        PMX w A' M' model' c' -> c_tr c' = [] -> pm_bud (w_n w) c' -> c_widx c' = 5 -> 5 <= w_n w -> c_endian c' < 2 -> c_icount c' = 0 ->
        c_m1 c' = c_m1 c -> c_m2 c' = c_m2 c -> c_m3 c' = c_m3 c ->
        loop_regs w R' -> loop_mem w M' -> srealizes SEGS (cfg fx1 R' PM_HEAD M' model') K) ->
    srealizes SEGS (cfg fx R 0x67438 M model) K.
  Proof using AC MI ST.
    intros w c0 K fx A M model c R PS X Htr BUD Hn5 Hw5 He2 Hic FZ Qs0 Qs1 Qsp Qgp Qtp LOOPK.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & [Gc2 Gcal] & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof (x_scal X) as (Sc1 & Sc2 & Sc3 & Sc4).
    pose proof (fld_cellw M _ 8 _ (x_hdrfn X) ltac:(lia)) as Ch.
    pm_seed R w c (@nil word). seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (9%bv, EAlu ALU_ADD (EVar 33) (ELit 88))] R. seedHK HK w A M model c E X.
    apply (know_more E M [KWord (SA (EVar 33) 24) (N.to_nat 8) (ELit 0)]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil.
         eapply kword_var; [exact Ch | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | cbn [edenot]; reflexivity]. }
    xruns HR HK 100%nat (0x674c4 :: STOPS) (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R1.
    rreg HRn (2%bv) A2. rreg HRn (3%bv) A3. rreg HRn (4%bv) A4. rreg HRn (8%bv) A8. rreg HRn (9%bv) A9. rreg HRn (10%bv) A10. rreg HRn (11%bv) A11. rreg HRn (12%bv) A12. rreg HRn (13%bv) A13. rreg HRn (14%bv) A14. rreg HRn (15%bv) A15. rreg HRn (16%bv) A16. rreg HRn (17%bv) A17. rreg HRn (18%bv) A18. rreg HRn (21%bv) A21. rreg HRn (25%bv) A25. rewrite ?w_add in A9, A21 by lia. clear HRn HR HK. rewrite ?w_add by lia.
    lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ => set (M1 := m) end.
    assert (ST1 : stores_in (zwin (w_sp w + 40) (w_sp w + 128)) M M1) by (unfold M1; stin).
    assert (X1 : PMX w A M1 model c).
    { eapply (pmx_frame_stores SEGS Ly.L MI ST ly_img_low ly_rw_img ly_relro_img); [exact X | exact ST1 | unfold zwin, w_sp0, PM_FRAME; intros; lia]. }

    fmv_step MS F_67484 D_67484 0x674c8. rewrite A14.
    pm_seed R1 w c (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (9%bv, EAlu ALU_ADD (EVar 33) (ELit 88)); (10%bv, ELit 83108); (11%bv, ELit 262144); (12%bv, ELit 65536); (13%bv, ELit 18446744072850558976); (14%bv, ELit 1258291200); (15%bv, ELit 18446744072627421184); (16%bv, ELit 1602224128); (17%bv, ELit 1431654400); (18%bv, ELit 1); (25%bv, ELit 5); (21%bv, EAlu ALU_ADD (EVar 33) (ELit 264))] R1.
    seedHK HK w A M1 model c E X1.
    xruns HR HK 100%nat (0x674cc :: STOPS) (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R2. rreg HRn (2%bv) B2. rreg HRn (3%bv) B3. rreg HRn (4%bv) B4. rreg HRn (8%bv) B8. rreg HRn (9%bv) B9. rreg HRn (10%bv) B10. rreg HRn (11%bv) B11. rreg HRn (12%bv) B12. rreg HRn (13%bv) B13. rreg HRn (14%bv) B14. rreg HRn (15%bv) B15. rreg HRn (16%bv) B16. rreg HRn (17%bv) B17. rreg HRn (18%bv) B18. rreg HRn (21%bv) B21. rreg HRn (25%bv) B25. rewrite ?w_add in B9, B21 by lia. clear HRn HR HK.

    fmv_step MS F_6748c D_6748c 0x674d0. rewrite B15.
    pm_seed R2 w c (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (9%bv, EAlu ALU_ADD (EVar 33) (ELit 88)); (10%bv, ELit 83108); (11%bv, ELit 262144); (12%bv, ELit 65536); (13%bv, ELit 18446744072850558976); (14%bv, ELit 858992640); (15%bv, ELit 18446744072627421184); (16%bv, ELit 1602224128); (17%bv, ELit 1431654400); (18%bv, ELit 1); (25%bv, ELit 5); (21%bv, EAlu ALU_ADD (EVar 33) (ELit 264))] R2.
    seedHK HK w A M1 model c E X1.
    xruns HR HK 100%nat (0x674d4 :: STOPS) (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R3. rreg HRn (2%bv) C2. rreg HRn (3%bv) C3. rreg HRn (4%bv) C4. rreg HRn (8%bv) C8. rreg HRn (9%bv) C9. rreg HRn (10%bv) C10. rreg HRn (11%bv) C11. rreg HRn (12%bv) C12. rreg HRn (13%bv) C13. rreg HRn (14%bv) C14. rreg HRn (15%bv) C15. rreg HRn (16%bv) C16. rreg HRn (17%bv) C17. rreg HRn (18%bv) C18. rreg HRn (21%bv) C21. rreg HRn (25%bv) C25. rewrite ?w_add in C9, C21 by lia. clear HRn HR HK.

    fmv_step MS F_67494 D_67494 0x674d8. rewrite C16.
    match goal with |- srealizes _ (mkCfg (@mkst ?f _ _ _ _) _) _ => set (fx1 := f) end.
    pm_seed R3 w c (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (9%bv, EAlu ALU_ADD (EVar 33) (ELit 88)); (10%bv, ELit 83108); (11%bv, ELit 262144); (12%bv, ELit 65536); (13%bv, ELit 18446744072850558976); (14%bv, ELit 858992640); (15%bv, ELit 252645376); (16%bv, ELit 1602224128); (17%bv, ELit 1431654400); (18%bv, ELit 1); (25%bv, ELit 5); (21%bv, EAlu ALU_ADD (EVar 33) (ELit 264))] R3.
    seedHK HK w A M1 model c E X1.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R4.
    rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (9%bv) G9.
    rreg HRn (18%bv) G18. rreg HRn (19%bv) G19. rreg HRn (20%bv) G20. rreg HRn (21%bv) G21. rreg HRn (25%bv) G25.
    rewrite ?w_add in G9, G21 by lia.
    clear HRn HR HK. fixregs. rewrite C3, B3, A3, Qgp in G3. rewrite C4, B4, A4, Qtp in G4.
    lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ => set (M4 := m) end.
    assert (ST4 : stores_in (fun a => zwin (w_sp w + 24) (w_sp w + 128) a \/ zwin (w_p w + 72) (w_p w + 80) a) M M4).
    { eapply stores_in_trans; [eapply stores_in_weaken; [exact ST1 | intros a Ha; left; unfold zwin in *; lia] |].
      unfold M4. do 9 (eapply stores_in_wbytes_more; [ | lia | w2blen; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | w2blen; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unfold zwin; intros; lia ]).
      apply stores_in_refl. }
    assert (X4 : PMX w A M4 model (set_scal c 5 (c_icount c) (c_endian c) (c_reqconv c))).
    { eapply (pmx_stores SEGS Ly.L MI ST ly_img_low ly_rw_img ly_relro_img);
        [exact X | exact ST4 | intros a [Ha|Ha]; unfold scal_win, zwin, O_WIDX, O_FLAGS, w_sp0, PM_FRAME in *; [left; lia | right; lia]
        | unfold M4, M1, O_WIDX; rdback
        | eapply fld_keep; [exact ST4 | exact (x_icount X) | unfold O_ICOUNT; lia | unfold O_ICOUNT; cbn; lia | unfold O_ICOUNT, zwin; cbn; intros; lia]
        | eapply fld_keep; [exact ST4 | exact (x_endian X) | unfold O_ENDIAN; lia | unfold O_ENDIAN; cbn; lia | unfold O_ENDIAN, zwin; cbn; intros; lia]
        | eapply fld_keep; [exact ST4 | exact (x_flags X) | unfold O_FLAGS; lia | unfold O_FLAGS; cbn; lia | unfold O_FLAGS, zwin; cbn; intros; lia]
        | lia | lia | lia | exact Sc4]. }
    assert (FZ1 : frm_zero (@fp_csr fx1)) by (subst fx1; cbn [fp_csr]; exact FZ).
    assert (FC1 : fconsts fx1).
    { subst fx1. unfold fconsts.
      replace (low32 (Z_to_bv 64 1258291200)) with (Z_to_bv 32 0x4b000000 : bv 32) by (apply bv_eq; vm_compute; reflexivity).
      replace (low32 (Z_to_bv 64 18446744072627421184)) with (Z_to_bv 32 0xbf800000 : bv 32) by (apply bv_eq; vm_compute; reflexivity).
      replace (low32 (Z_to_bv 64 1602224128)) with (Z_to_bv 32 0x5f800000 : bv 32) by (apply bv_eq; vm_compute; reflexivity).
      cbn [fp_regs fp_csr].
      split; [|split].
      - apply fholds_set_other; [intros E0; discriminate E0|]. apply fholds_set_other; [intros E0; discriminate E0|]. apply fholds_set_same. lia.
      - apply fholds_set_other; [intros E0; discriminate E0|]. apply fholds_set_same. lia.
      - apply fholds_set_same. lia. }
    eapply (LOOPK fx1 A M4 model _ R4 FZ1 FC1 X4); [cbn [c_tr set_scal]; exact Htr | exact BUD | reflexivity | exact Hn5 | cbn [c_endian set_scal]; exact He2 | cbn [c_icount set_scal]; exact Hic | reflexivity | reflexivity | reflexivity | |].
    - unfold loop_regs. rewrite G2, G3, G4, G8, G9, G18, G19, G20, G21, G25. repeat split; reflexivity.
    - unfold loop_mem, hdr_consts. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; unfold M4, M1; rdback.
  Qed.

#[local] Definition HTPmBodyU1_0 : list (reg * expr) := [(2%bv, EVar 32); (8%bv, EVar 33); (10%bv, EVar 39); (9%bv, EAlu ALU_ADD (EVar 33) (ELit 88))].
  Lemma pm_hdr : forall (w : pmw MI ST) c0 K (fx : FPState),
    PMS w c0 K -> frm_zero (@fp_csr fx) -> hdr_stmt w c0 K fx.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx PS FZ A M model c R X Htr BUD Hw Hw5 Hic Qs0 Qa0 Qsp Qgp Qtp LOOPK.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & [Gc2 Gcal] & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    destruct (Gw Hw) as (W1 & W2 & W3 & W4 & W5). pose proof (x_scal X) as (Sc1 & Sc2 & Sc3 & Sc4).
    destruct (Z.lt_ge_cases (w_n w) 5) as [Hn4|Hn5].
    {
      pm_seed R w c (@nil word). seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (10%bv, EVar 33)] R. seedHK HK w A M model c E X.
      xruns HR HK 100%nat (0x6726c :: STOPS) (SCR [false; false] [] []) 50%N. { split_scs; try sc_auto1. }
      postrun. name_run HRn R1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. clear HRn HR HK. fixregs.
      rewrite Qgp in G3. rewrite Qtp in G4.
      eapply (pm_D2 w c0 K fx A M model c R1); [exact PS | exact X | exact Htr | exact BUD | lia | exact FZ | exact G8 | exact G2 | exact G3 | exact G4]. }
    pm_seed R w c (@nil word). seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (10%bv, EVar 33)] R. seedHK HK w A M model c E X.
    xruns HR HK 100%nat STOPS (SCR [false; true] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R1.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (9%bv) G9. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11.
    rewrite ?w_add in G9, G10, G11 by lia. clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ => set (M1 := m) end.
    assert (ST1 : stores_in (zwin (w_sp w + 160) (w_sp w + 176)) M M1) by (unfold M1; stin).
    assert (X1 : PMX w A M1 model c).
    { eapply (pmx_frame_stores SEGS Ly.L MI ST ly_img_low ly_rw_img ly_relro_img); [exact X | exact ST1 | unfold zwin, w_sp0, PM_FRAME; intros; lia]. }
    eapply (pm_binend w A M1 model c fx R1 _ K X1 Hw ltac:(lia) ltac:(unfold M1; rdback) ltac:(unfold M1; rdback) G10 G11 G2 G1 ltac:(apply bv_eq; vm_compute; reflexivity)).
    clear ST1. intros R2 M2 r e KEPT Hr Rr Re He2 X2 AG.
    keptQ KEPT G2 Qsp'. keptQ KEPT G8 Qs0'. keptQ KEPT G3 Qgp'. keptQ KEPT G4 Qtp'. keptQ KEPT G9 Qs1. clear G1 G2 G3 G4 G8 G9 G10 G11 Qsp Qs0 Qa0 Qgp Qtp KEPT.
    rename Qsp' into Qsp. rename Qs0' into Qs0. rename Qgp' into Qgp. rename Qtp' into Qtp.
    assert (F160 : fld SEGS M2 (w_sp w + 160) 8 (w_words w)).
    { eapply (fld_agree SEGS M1 M2); [lia | cbn; lia | unfold M1; rdback | eapply agree_on_weaken; [exact AG | unfold zwin, w_sp0, PM_FRAME; intros; lia]]. }
    assert (F168 : fld SEGS M2 (w_sp w + 168) 8 (w_n w)).
    { eapply (fld_agree SEGS M1 M2); [lia | cbn; lia | unfold M1; rdback | eapply agree_on_weaken; [exact AG | unfold zwin, w_sp0, PM_FRAME; intros; lia]]. }
    clear AG X1 X. clearbody M1. clear M1 MS. pose proof (x_ms X2) as MS.
    destruct (Z.eq_dec r 0) as [Hr0|Hr0].
    2: {
      pm_seed R2 w (set_scal c (c_widx c) (c_icount c) e (c_reqconv c)) [Z_to_bv 64 r].
      seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (10%bv, EVar 39)] R2. seedHK HK w A M2 model (set_scal c (c_widx c) (c_icount c) e (c_reqconv c)) E X2.
      xruns HR HK 100%nat (0x67300 :: STOPS) (SCR [false] [] []) 50%N. { split_scs; try sc_auto1. }
      postrun. name_run HRn R3. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. clear HRn HR HK. fixregs.
      rewrite Qgp in G3. rewrite Qtp in G4.
      eapply (pm_D3 w c0 K fx A M2 model _ R3); [exact PS | exact X2 | cbn [c_tr set_scal]; exact Htr | exact BUD | exact Hw | lia | exact FZ | exact G8 | exact G2 | exact G3 | exact G4]. }
    subst r. pose proof (He2 eq_refl) as He. clear He2. assert (He32 : 0 <= e < 2 ^ 32) by lia.

    pose proof (fld_cellw M2 _ 4 _ (x_endian X2) ltac:(cbn [c_endian set_scal]; lia)) as Ce. cbn [c_endian set_scal] in Ce. unfold O_ENDIAN in Ce.
    pm_seed R2 w (set_scal c (c_widx c) (c_icount c) e (c_reqconv c)) [Z_to_bv 64 0; Z_to_bv 64 e].
    seedHR HR E HTPmBodyU1_0 R2. seedHK HK w A M2 model (set_scal c (c_widx c) (c_icount c) e (c_reqconv c)) E X2.
    apply (know_more E M2 [KWord (SA (EVar 33) 88) (N.to_nat 4) (EVar 40); KRange (EVar 40) 0 1]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil.
         - eapply kword_var; [exact Ce | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
         - eapply krange_var; [evs; reflexivity | lia | lia]. }
    xruns HR HK 100%nat STOPS (SCR [true] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R3. rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (9%bv) G9. rreg HRn (10%bv) G10.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_is_host_endian w A M2 model _ fx R3 _ K X2 (ex_intro _ e (conj He32 G10)) G1 ltac:(apply bv_eq; vm_compute; reflexivity)).
    intros R4 KEPT (r01 & Hr01 & Ha0). evs_in G9. rewrite ?w_add in G9 by lia.
    keptQ KEPT G2 Qsp'. keptQ KEPT G8 Qs0'. keptQ KEPT G3 Qgp'. keptQ KEPT G4 Qtp'. keptQ KEPT G9 Qs1'. clear G1 G2 G3 G4 G8 G9 G10 Qsp Qs0 Qgp Qtp Qs1 KEPT.
    rename Qsp' into Qsp. rename Qs0' into Qs0. rename Qgp' into Qgp. rename Qtp' into Qtp. rename Qs1' into Qs1.

    pm_seed R4 w (set_scal c (c_widx c) (c_icount c) e (c_reqconv c)) [Z_to_bv 64 r01; Z_to_bv 64 e].
    seedHR HR E HTPmBodyU1_0 R4. seedHK HK w A M2 model (set_scal c (c_widx c) (c_icount c) e (c_reqconv c)) E X2.
    apply (know_more E M2 [KWord (SA (EVar 33) 88) (N.to_nat 4) (EVar 40); KRange (EVar 40) 0 1; KRange (EVar 39) 0 1]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil.
         - eapply kword_var; [exact Ce | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
         - eapply krange_var; [evs; reflexivity | lia | lia].
         - eapply krange_var; [evs; reflexivity | lia | lia]. }
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R5. rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (9%bv) G9.
    rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4. rewrite ?w_add in G9, G10, G12 by lia.
    rewrite (w_xor1 r01 Hr01).
    lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ => set (M3 := m) end.
    assert (ST3 : stores_in (zwin (w_p w + 92) (w_p w + 93)) M2 M3) by (unfold M3; stin).
    set (cc := set_scal c (c_widx c) (c_icount c) e (1 - r01)).
    assert (X3 : PMX w A M3 model cc).
    { eapply (pmx_stores SEGS Ly.L MI ST ly_img_low ly_rw_img ly_relro_img _ _ _ _ _ (set_scal c (c_widx c) (c_icount c) e (c_reqconv c)));
        [exact X2 | exact ST3 | intros a Ha; right; unfold scal_win, zwin, O_WIDX, O_FLAGS in *; lia
        | eapply fld_keep; [exact ST3 | exact (x_widx X2) | unfold O_WIDX; lia | unfold O_WIDX; cbn; lia | unfold O_WIDX, zwin; cbn; intros; lia]
        | eapply fld_keep; [exact ST3 | exact (x_icount X2) | unfold O_ICOUNT; lia | unfold O_ICOUNT; cbn; lia | unfold O_ICOUNT, zwin; cbn; intros; lia]
        | eapply fld_keep; [exact ST3 | exact (x_endian X2) | unfold O_ENDIAN; lia | unfold O_ENDIAN; cbn; lia | unfold O_ENDIAN, zwin; cbn; intros; lia]
        | unfold M3, O_FLAGS; apply (flags_store M2 (w_p w) (c_reqconv c) (1 - r01) (x_flags X2)); [exact Sc4 | lia | lia | lia]
        | cbn [c_widx set_scal]; lia | cbn [c_widx c_icount set_scal]; lia | cbn [c_endian set_scal]; lia | lia]. }
    assert (F160' : fld SEGS M3 (w_sp w + 160) 8 (w_words w)) by (eapply fld_keep; [exact ST3 | exact F160 | lia | cbn; lia | unfold zwin; cbn; intros; lia]).
    assert (F168' : fld SEGS M3 (w_sp w + 168) 8 (w_n w)) by (eapply fld_keep; [exact ST3 | exact F168 | lia | cbn; lia | unfold zwin; cbn; intros; lia]).
    clear ST3 X2 F160 F168 Ce. clearbody M3. pose proof (x_ms X3) as MS3.
    eapply (pm_header_get w A M3 model cc fx R5 _ K X3 Hw Hn5 ltac:(cbn [c_endian cc set_scal]; lia) F160' F168' G10 ltac:(cbn [c_endian cc set_scal]; exact G11) G12 G2 G1 ltac:(apply bv_eq; vm_compute; reflexivity)).
    clear Hr. intros R6 M6 r KEPT Hr6 Hr04 X6 AG6.
    keptQ KEPT G2 Qsp'. keptQ KEPT G8 Qs0'. keptQ KEPT G3 Qgp'. keptQ KEPT G4 Qtp'. keptQ KEPT G9 Qs1'. clear G1 G2 G3 G4 G8 G9 G10 G11 G12 Qsp Qs0 Qgp Qtp Qs1 KEPT.
    rename Qsp' into Qsp. rename Qs0' into Qs0. rename Qgp' into Qgp. rename Qtp' into Qtp. rename Qs1' into Qs1.
    pose proof (x_ms X6) as MS6.
    destruct Hr04 as [-> | ->].
    2: {
      replace (Z_to_bv 64 (-4)) with (Z_to_bv 64 18446744073709551612 : word) in Hr6 by (apply bv_eq; vm_compute; reflexivity).
      pm_seed R6 w (set_scal cc (c_widx cc) (c_icount cc) (c_endian cc) (c_reqconv cc)) (@nil word).
      seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (10%bv, ELit 18446744073709551612)] R6. seedHK HK w A M6 model (set_scal cc (c_widx cc) (c_icount cc) (c_endian cc) (c_reqconv cc)) E X6.
      xruns HR HK 100%nat (0x673bc :: STOPS) (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
      postrun. name_run HRn R7. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. clear HRn HR HK. fixregs.
      rewrite Qgp in G3. rewrite Qtp in G4.
      eapply (pm_D4 w c0 K fx A M6 model _ R7); [exact PS | exact X6 | cbn [c_tr cc set_scal]; exact Htr | exact BUD | exact FZ | exact G8 | exact G2 | exact G3 | exact G4]. }

    pm_seed R6 w (set_scal cc (c_widx cc) (c_icount cc) (c_endian cc) (c_reqconv cc)) (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (10%bv, ELit 0); (9%bv, EAlu ALU_ADD (EVar 33) (ELit 88))] R6. seedHK HK w A M6 model (set_scal cc (c_widx cc) (c_icount cc) (c_endian cc) (c_reqconv cc)) E X6.
    xruns HR HK 100%nat (0x67438 :: STOPS) (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R7. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (9%bv) G9. clear HRn HR HK. fixregs.
    rewrite Qgp in G3. rewrite Qtp in G4. rewrite ?w_add in G9 by lia.
    eapply (pm_hdrB w c0 K fx A M6 model _ R7 PS X6 ltac:(cbn [c_tr cc set_scal]; exact Htr) BUD Hn5 ltac:(cbn [c_widx cc set_scal]; exact Hw5) ltac:(cbn [c_endian cc set_scal]; lia) ltac:(cbn [c_icount cc set_scal]; exact Hic) FZ G8 G9 G2 G3 G4
             ltac:(intros fx1 A' M' model' c' R'; pose proof (LOOPK fx1 A' M' model' c' R') as LK; cbn [c_m1 c_m2 c_m3 cc set_scal] in LK; exact LK)).
  Qed.
End PM.
End PmHdrU1.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HWord.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsGrammar OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep4U1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Module PmArm_LitU1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.

Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PropExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SeqExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StepTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.WalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StartupTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SumWalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StoreOk OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MemSplit OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Hoare OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ShapeAlg OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SRealizes OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefReadLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.FPSteps OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibIface OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibBudget OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibEff OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MmapSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibMaskBits OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ZStores OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3Sound OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymRun3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.U1Layout.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.CRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.StrLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.LiveStats OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContStmts2 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.U1Facts.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRepFacts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HStmtsU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HCommonU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HConstsU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HWord.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsGrammar OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsNeeds OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsInv OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmBaseU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmHyps OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmHypsU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmCoreU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStepU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep2U1.PmUpdU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep2U1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmLoopU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmInstU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep3U1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmZw OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmODefsU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep4U1.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Abbreviation SEGS := Ubsan.M.loaded_segments.

Lemma in_reg_list : forall (r : bv 5) (l : list (bv 5)),
  existsb (fun x => Z.eqb (bv_unsigned x) (bv_unsigned r)) l = true -> In r l.
Proof.
  intros r l; induction l as [|x l IH]; cbn; [discriminate|]. intros H. apply Bool.orb_true_iff in H.
  destruct H as [H|H]; [left; apply bv_eq; apply Z.eqb_eq; exact H | right; apply IH; exact H].
Qed.
Ltac keptQ KEPT G Q ::=
  lazymatch type of G with getr _ ?r = _ => pose proof G as Q; rewrite <- (KEPT r) in Q by (clear; apply in_reg_list; reflexivity) end.

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
  #[local] Notation pm_exit := (PmCoreU1.pm_exit MI ST).
  #[local] Notation pmx_ds_room := (PmStepU1.pmx_ds_room CL).
  #[local] Notation pm_tail_6733c := (PmStepU1.pm_tail_6733c CL).
  #[local] Notation cregs_kept := (PmStepU1.cregs_kept CL).
  #[local] Notation pm_put_cstr := (PmStepU1.pm_put_cstr CL).
  #[local] Notation pm_put_chars := (PmStepU1.pm_put_chars CL).
  #[local] Notation pm_put_num := (PmStepU1.pm_put_num CL).
  #[local] Notation pm_put_u16 := (PmStepU1.pm_put_u16 CL).
  #[local] Notation pm_put_u32 := (PmStepU1.pm_put_u32 CL).
  #[local] Notation pm_put_u64 := (PmStepU1.pm_put_u64 CL).
  #[local] Notation pm_put_int := (PmStepU1.pm_put_int CL).
  #[local] Notation pm_pdiagQ := (PmStepU1.pm_pdiagQ CL).
  #[local] Notation pm_dtor := (PmStepU1.pm_dtor CL).
  #[local] Notation pm_exhausted := (PmStepU1.pm_exhausted CL).
  #[local] Notation pm_fixword := (PmStepU1.pm_fixword CL).
  #[local] Notation pm_is_host_endian := (PmStepU1.pm_is_host_endian CL).
  #[local] Notation pm_binend := (PmStepU1.pm_binend CL).
  #[local] Notation pm_ecw_pbs := (PmStep2U1.pm_ecw_pbs CL).
  #[local] Notation pm_opcode_split := (PmStep2U1.pm_opcode_split CL).
  #[local] Notation pm_lookup_opcode := (PmStep2U1.pm_lookup_opcode CL).
  #[local] Notation pm_lookup_operand := (PmStep2U1.pm_lookup_operand CL).
  #[local] Notation pm_lookup_ext := (PmStep2U1.pm_lookup_ext CL).
  #[local] Notation pm_idesc_operands := (PmStep3U1.pm_idesc_operands CL).
  #[local] Notation pm_odesc_operands := (PmStep3U1.pm_odesc_operands CL).
  #[local] Notation pm_edesc_operands := (PmStep3U1.pm_edesc_operands CL).
  #[local] Notation pm_push_types := (PmStep3U1.pm_push_types CL).
  #[local] Notation pm_take_first := (PmStep3U1.pm_take_first CL).

  #[local] Notation izero := (PmInstU1.izero).
  #[local] Notation ictx := (PmInstU1.ictx).
  #[local] Notation nodes := (PmLoopU1.nodes).
  #[local] Notation macct := (PmLoopU1.macct).
  #[local] Notation GOK := (cu_G _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
  #[local] Notation MAXLEN := (cu_maxlen _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
  #[local] Notation MASKLEN := (cu_mask_len _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
  #[local] Notation ipure := (PmODefsU1.ipure (G:=G) (idesc:=idesc)).
  #[local] Notation arm_stmt := (PmODefsU1.arm_stmt (MI:=MI) (ST:=ST) (G:=G) (idesc:=idesc)).
  #[local] Notation OBASE := (PmODefsU1.OBASE (MI:=MI) (ST:=ST)).
  #[local] Notation oregs := (PmODefsU1.oregs (MI:=MI) (ST:=ST)).
  #[local] Notation ifr := (PmODefsU1.ifr (MI:=MI) (ST:=ST)).
  #[local] Notation popnd := (PmODefsU1.popnd (MI:=MI) (ST:=ST)).
  #[local] Notation pm_find_m3 := (PmStep4U1.pm_find_m3 CL).
  #[local] Notation pm_find_m1 := (PmStep4U1.pm_find_m1 CL).
  #[local] Notation pm_spec_lookup := (PmStep4U1.pm_spec_lookup CL).
  #[local] Notation pm_oty_pb := (PmStep4U1.pm_oty_pb CL).
  Definition pm_is_ext_inst := pm_leafA (MI:=MI) (ST:=ST) _ _ _ (cu_is_ext_inst _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
  Definition pm_is_nonsemantic := pm_leafA (MI:=MI) (ST:=ST) _ _ _ (cu_is_nonsemantic _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
  Definition pm_operand_type_str := pm_leafA (MI:=MI) (ST:=ST) _ _ _ (cu_operand_type_str _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
  Definition pm_strlen := pm_leafA (MI:=MI) (ST:=ST) _ _ _ (cu_strlen _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).

  Ltac oregs_seeded HRn Qgp Qtp :=
    let G2 := fresh in let G3 := fresh in let G4 := fresh in let G8 := fresh in let G9 := fresh in
    let G18 := fresh in let G19 := fresh in let G20 := fresh in let G21 := fresh in let G25 := fresh in
    rreg HRn 2%bv G2; rreg HRn 3%bv G3; rreg HRn 4%bv G4; rreg HRn 8%bv G8; rreg HRn 9%bv G9;
    rreg HRn 18%bv G18; rreg HRn 19%bv G19; rreg HRn 20%bv G20; rreg HRn 21%bv G21; rreg HRn 25%bv G25;
    unfold oregs, loop_regs; rewrite G2, G3, G4, G8, G9, G18, G19, G20, G21, G25; fixregs; rewrite ?Qgp, ?Qtp;
    rewrite ?SymExec.alu64_add_lit; repeat split; reflexivity.
  #[local] Notation OREGSEED := [(9%bv, EAlu ALU_ADD (EVar 33) (ELit 88)); (18%bv, ELit 1); (19%bv, ELit (2 ^ 61)); (20%bv, ELit 20); (21%bv, EAlu ALU_ADD (EVar 33) (ELit 264)); (25%bv, ELit 5)]%list.

#[local] Definition HTPmBodyU1_1 : list (reg * expr) := [(2%bv, EVar 32); (8%bv, EVar 33); (27%bv, EVar 39); (23%bv, EVar 40); (26%bv, EVar 41)].
  Theorem arm_LITINT_U1 : forall t, (t = 6 \/ t = 45) -> arm_stmt t 0x67cf8.
  Proof using AC MI ST G idesc.
    intros t Htt w c0 K fx I A M model c R wv PS FZ FC IP HAE PK CK AACC. specialize (PK fx FZ FC). clear CK.
    pose proof (AE_facts w I A M model c R t wv IP HAE) as (_ & _ & Hoff & V3B & _ & _).
    destruct HAE as (OB & Hw1 & Hw2 & Hn & Hv1 & Hv2 & Hlen & Ht & Hword & Q22 & Q27 & Q24 & Q23 & Q26 & PO & C712).
    pose proof OB as OB'; destruct OB' as (X & Htr & BUD & OR & LM & IC & FR & Hic & Hend & Hwnz & MAC & V3R).
    pose proof (x_geo X) as GEO; pose proof ac_bounds_lit as Hcv; pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & [Gc2 Gcal] & Gap & Gn & Gw); unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof OR as OR'; destruct OR' as (Qsp & Qgp & Qtp & Qs0 & Qs1 & Qs2 & Qs3 & Qs4 & Qs5 & Qs9).
    destruct PO as (_ & C718 & _).
    pm_seed R w c [Z_to_bv 64 t; Z_to_bv 64 (i_io I); Z_to_bv 64 (i_op I)].
    seedHR HR E (HTPmBodyU1_1 ++ OREGSEED)%list R; seedHK HK w A M model c E X.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun; name_run HRn R1.
    rreg HRn (27%bv) G27; rreg HRn (23%bv) G23; rreg HRn (26%bv) G26.
    assert (OR1 : oregs w R1) by (oregs_seeded HRn Qgp Qtp); clear HRn HR HK.
    lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ => set (M1 := m) in * end.
    assert (ST1 : stores_in (zwin (w_sp w + 720) (w_sp w + 732)) M M1) by (unfold M1; stin).
    assert (X1 : PMX w A M1 model c).
    { eapply (pmx_frame_stores SEGS Ly.L MI ST ly_img_low ly_rw_img ly_relro_img w A M M1 model c (zwin (w_sp w + 720) (w_sp w + 732)));
        [exact X | exact ST1 | unfold zwin, w_sp0, PM_FRAME; intros; lia]. }
    assert (AG1 : CRep.agree_on (fun a => w_sp w <= a < w_sp w + 864 /\ ~ zwin (w_sp w + 720) (w_sp w + 732) a) M M1) by
      (eapply stores_in_agree; [exact ST1 | intros b Hb; unfold zwin in *; lia]).
    assert (LM1 : loop_mem w M1) by (eapply (loop_mem_frame w M M1); [exact LM | lia | lia | eapply agree_on_weaken; [exact AG1 | unfold zwin; cbn; intros; lia]]).
    assert (IC1 : ictx w M1 (i_io I) (i_fw I) (i_iwc I) (i_op I) (i_d I)) by (eapply (ictx_agree w M M1); [exact IC | lia | lia | eapply agree_on_weaken; [exact AG1 | unfold zwin; cbn; intros; lia]]).
    assert (FR1 : ifr w M1) by (eapply (ifr_agree w M M1); [exact FR | lia | lia | eapply agree_on_weaken; [exact AG1 | unfold zwin; cbn; intros; lia]]).
    assert (C718' : cellw SEGS M1 (w_sp w + 718) 2 1) by
      (eapply (cellw_frame M M1); [exact C718 | lia | cbn; lia | eapply agree_on_weaken; [exact AG1 | unfold zwin; cbn; intros; lia]]).
    pose proof (x_ms X1) as MS1; clear ST1 AG1; clearbody M1.
    eapply (PK A M1 model c R1 1 []).
    - split; [exact X1|]. split; [exact Htr|]. split; [exact BUD|]. split; [exact OR1|]. split; [exact LM1|]. split; [exact IC1|]. split; [exact FR1|].
      split; [exact Hic|]. split; [exact Hend|]. split; [exact Hwnz|]. split; [exact MAC | exact V3R].
    - exact G27. - exact G23. - exact G26. - exact C718'. - left; lia.
    - reflexivity. - reflexivity. - reflexivity.
    - change (Z.min 1 1) with 1. lia.
    - rewrite app_nil_r. reflexivity. - exact PmZw.seed_free_nil. - rewrite PmZw.Zlen_nil. lia. - left; reflexivity.
    - reflexivity. - left; reflexivity. - left; reflexivity. - intros [].
  Qed.

  Theorem arm_LITFLOAT_U1 : forall t, t = 10 -> arm_stmt t 0x67de4.
  Proof using AC MI ST G idesc.
    intros t Htt w c0 K fx I A M model c R wv PS FZ FC IP HAE PK CK AACC. specialize (PK fx FZ FC). clear CK.
    pose proof (AE_facts w I A M model c R t wv IP HAE) as (_ & _ & Hoff & V3B & _ & _).
    destruct HAE as (OB & Hw1 & Hw2 & Hn & Hv1 & Hv2 & Hlen & Ht & Hword & Q22 & Q27 & Q24 & Q23 & Q26 & PO & C712).
    pose proof OB as OB'; destruct OB' as (X & Htr & BUD & OR & LM & IC & FR & Hic & Hend & Hwnz & MAC & V3R).
    pose proof (x_geo X) as GEO; pose proof ac_bounds_lit as Hcv; pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & [Gc2 Gcal] & Gap & Gn & Gw); unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof OR as OR'; destruct OR' as (Qsp & Qgp & Qtp & Qs0 & Qs1 & Qs2 & Qs3 & Qs4 & Qs5 & Qs9).
    destruct PO as (_ & C718 & _).
    pm_seed R w c [Z_to_bv 64 t; Z_to_bv 64 (i_io I); Z_to_bv 64 (i_op I)].
    seedHR HR E (HTPmBodyU1_1 ++ OREGSEED)%list R; seedHK HK w A M model c E X.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun; name_run HRn R1.
    rreg HRn (27%bv) G27; rreg HRn (23%bv) G23; rreg HRn (26%bv) G26.
    assert (OR1 : oregs w R1) by (oregs_seeded HRn Qgp Qtp); clear HRn HR HK.
    lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ => set (M1 := m) in * end.
    assert (ST1 : stores_in (zwin (w_sp w + 720) (w_sp w + 732)) M M1) by (unfold M1; stin).
    assert (X1 : PMX w A M1 model c).
    { eapply (pmx_frame_stores SEGS Ly.L MI ST ly_img_low ly_rw_img ly_relro_img w A M M1 model c (zwin (w_sp w + 720) (w_sp w + 732)));
        [exact X | exact ST1 | unfold zwin, w_sp0, PM_FRAME; intros; lia]. }
    assert (AG1 : CRep.agree_on (fun a => w_sp w <= a < w_sp w + 864 /\ ~ zwin (w_sp w + 720) (w_sp w + 732) a) M M1) by
      (eapply stores_in_agree; [exact ST1 | intros b Hb; unfold zwin in *; lia]).
    assert (LM1 : loop_mem w M1) by (eapply (loop_mem_frame w M M1); [exact LM | lia | lia | eapply agree_on_weaken; [exact AG1 | unfold zwin; cbn; intros; lia]]).
    assert (IC1 : ictx w M1 (i_io I) (i_fw I) (i_iwc I) (i_op I) (i_d I)) by (eapply (ictx_agree w M M1); [exact IC | lia | lia | eapply agree_on_weaken; [exact AG1 | unfold zwin; cbn; intros; lia]]).
    assert (FR1 : ifr w M1) by (eapply (ifr_agree w M M1); [exact FR | lia | lia | eapply agree_on_weaken; [exact AG1 | unfold zwin; cbn; intros; lia]]).
    assert (C718' : cellw SEGS M1 (w_sp w + 718) 2 1) by
      (eapply (cellw_frame M M1); [exact C718 | lia | cbn; lia | eapply agree_on_weaken; [exact AG1 | unfold zwin; cbn; intros; lia]]).
    pose proof (x_ms X1) as MS1; clear ST1 AG1; clearbody M1.
    eapply (PK A M1 model c R1 1 []).
    - split; [exact X1|]. split; [exact Htr|]. split; [exact BUD|]. split; [exact OR1|]. split; [exact LM1|]. split; [exact IC1|]. split; [exact FR1|].
      split; [exact Hic|]. split; [exact Hend|]. split; [exact Hwnz|]. split; [exact MAC | exact V3R].
    - exact G27. - exact G23. - exact G26. - exact C718'. - left; lia.
    - reflexivity. - reflexivity. - reflexivity.
    - change (Z.min 1 1) with 1. lia.
    - rewrite app_nil_r. reflexivity. - exact PmZw.seed_free_nil. - rewrite PmZw.Zlen_nil. lia. - left; reflexivity.
    - reflexivity. - left; reflexivity. - left; reflexivity. - intros [].
  Qed.
End PM.
End PmArm_LitU1.

Module PmArm_TyScDfU1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.

Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PropExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SeqExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StepTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.WalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StartupTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SumWalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StoreOk OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MemSplit OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Hoare OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ShapeAlg OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SRealizes OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefReadLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.FPSteps OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibIface OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibBudget OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibEff OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MmapSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibMaskBits OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ZStores OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3Sound OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymRun3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.U1Layout.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.CRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.StrLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.LiveStats OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContStmts2 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.U1Facts.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRepFacts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HStmtsU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HCommonU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HConstsU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HWord.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsGrammar OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsNeeds OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsInv OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmBaseU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmHyps OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmHypsU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmCoreU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStepU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep2U1.PmUpdU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep2U1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmLoopU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmInstU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep3U1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmZw OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmODefsU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep4U1.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Abbreviation SEGS := Ubsan.M.loaded_segments.

Lemma in_reg_list : forall (r : bv 5) (l : list (bv 5)),
  existsb (fun x => Z.eqb (bv_unsigned x) (bv_unsigned r)) l = true -> In r l.
Proof.
  intros r l; induction l as [|x l IH]; cbn; [discriminate|]. intros H. apply Bool.orb_true_iff in H.
  destruct H as [H|H]; [left; apply bv_eq; apply Z.eqb_eq; exact H | right; apply IH; exact H].
Qed.
Ltac keptQ KEPT G Q ::=
  lazymatch type of G with getr _ ?r = _ => pose proof G as Q; rewrite <- (KEPT r) in Q by (clear; apply in_reg_list; reflexivity) end.

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
  #[local] Notation pm_exit := (PmCoreU1.pm_exit MI ST).
  #[local] Notation pmx_ds_room := (PmStepU1.pmx_ds_room CL).
  #[local] Notation pm_tail_6733c := (PmStepU1.pm_tail_6733c CL).
  #[local] Notation cregs_kept := (PmStepU1.cregs_kept CL).
  #[local] Notation pm_put_cstr := (PmStepU1.pm_put_cstr CL).
  #[local] Notation pm_put_chars := (PmStepU1.pm_put_chars CL).
  #[local] Notation pm_put_num := (PmStepU1.pm_put_num CL).
  #[local] Notation pm_put_u16 := (PmStepU1.pm_put_u16 CL).
  #[local] Notation pm_put_u32 := (PmStepU1.pm_put_u32 CL).
  #[local] Notation pm_put_u64 := (PmStepU1.pm_put_u64 CL).
  #[local] Notation pm_put_int := (PmStepU1.pm_put_int CL).
  #[local] Notation pm_pdiagQ := (PmStepU1.pm_pdiagQ CL).
  #[local] Notation pm_dtor := (PmStepU1.pm_dtor CL).
  #[local] Notation pm_exhausted := (PmStepU1.pm_exhausted CL).
  #[local] Notation pm_fixword := (PmStepU1.pm_fixword CL).
  #[local] Notation pm_is_host_endian := (PmStepU1.pm_is_host_endian CL).
  #[local] Notation pm_binend := (PmStepU1.pm_binend CL).
  #[local] Notation pm_ecw_pbs := (PmStep2U1.pm_ecw_pbs CL).
  #[local] Notation pm_opcode_split := (PmStep2U1.pm_opcode_split CL).
  #[local] Notation pm_lookup_opcode := (PmStep2U1.pm_lookup_opcode CL).
  #[local] Notation pm_lookup_operand := (PmStep2U1.pm_lookup_operand CL).
  #[local] Notation pm_lookup_ext := (PmStep2U1.pm_lookup_ext CL).
  #[local] Notation pm_idesc_operands := (PmStep3U1.pm_idesc_operands CL).
  #[local] Notation pm_odesc_operands := (PmStep3U1.pm_odesc_operands CL).
  #[local] Notation pm_edesc_operands := (PmStep3U1.pm_edesc_operands CL).
  #[local] Notation pm_push_types := (PmStep3U1.pm_push_types CL).
  #[local] Notation pm_take_first := (PmStep3U1.pm_take_first CL).

  #[local] Notation izero := (PmInstU1.izero).
  #[local] Notation ictx := (PmInstU1.ictx).
  #[local] Notation nodes := (PmLoopU1.nodes).
  #[local] Notation macct := (PmLoopU1.macct).
  #[local] Notation GOK := (cu_G _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
  #[local] Notation MAXLEN := (cu_maxlen _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
  #[local] Notation MASKLEN := (cu_mask_len _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
  #[local] Notation ipure := (PmODefsU1.ipure (G:=G) (idesc:=idesc)).
  #[local] Notation arm_stmt := (PmODefsU1.arm_stmt (MI:=MI) (ST:=ST) (G:=G) (idesc:=idesc)).
  #[local] Notation OBASE := (PmODefsU1.OBASE (MI:=MI) (ST:=ST)).
  #[local] Notation oregs := (PmODefsU1.oregs (MI:=MI) (ST:=ST)).
  #[local] Notation ifr := (PmODefsU1.ifr (MI:=MI) (ST:=ST)).
  #[local] Notation popnd := (PmODefsU1.popnd (MI:=MI) (ST:=ST)).
  #[local] Notation pm_find_m3 := (PmStep4U1.pm_find_m3 CL).
  #[local] Notation pm_find_m1 := (PmStep4U1.pm_find_m1 CL).
  #[local] Notation pm_spec_lookup := (PmStep4U1.pm_spec_lookup CL).
  #[local] Notation pm_oty_pb := (PmStep4U1.pm_oty_pb CL).
  Definition pm_is_ext_inst := pm_leafA (MI:=MI) (ST:=ST) _ _ _ (cu_is_ext_inst _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
  Definition pm_is_nonsemantic := pm_leafA (MI:=MI) (ST:=ST) _ _ _ (cu_is_nonsemantic _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
  Definition pm_operand_type_str := pm_leafA (MI:=MI) (ST:=ST) _ _ _ (cu_operand_type_str _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
  Definition pm_strlen := pm_leafA (MI:=MI) (ST:=ST) _ _ _ (cu_strlen _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).

  Ltac oregs_seeded HRn Qgp Qtp :=
    let G2 := fresh in let G3 := fresh in let G4 := fresh in let G8 := fresh in let G9 := fresh in
    let G18 := fresh in let G19 := fresh in let G20 := fresh in let G21 := fresh in let G25 := fresh in
    rreg HRn 2%bv G2; rreg HRn 3%bv G3; rreg HRn 4%bv G4; rreg HRn 8%bv G8; rreg HRn 9%bv G9;
    rreg HRn 18%bv G18; rreg HRn 19%bv G19; rreg HRn 20%bv G20; rreg HRn 21%bv G21; rreg HRn 25%bv G25;
    unfold oregs, loop_regs; rewrite G2, G3, G4, G8, G9, G18, G19, G20, G21, G25; fixregs; rewrite ?Qgp, ?Qtp;
    rewrite ?SymExec.alu64_add_lit; repeat split; reflexivity.
  #[local] Notation OREGSEED := [(9%bv, EAlu ALU_ADD (EVar 33) (ELit 88)); (18%bv, ELit 1); (19%bv, ELit (2 ^ 61)); (20%bv, ELit 20); (21%bv, EAlu ALU_ADD (EVar 33) (ELit 264)); (25%bv, ELit 5)]%list.

  Lemma sxw_small' : forall v, 0 <= v < 2 ^ 31 -> sxw v = Z_to_bv 64 v.
  Proof using. intros v Hv. unfold sxw. rewrite bv_swrap32_cases by lia. destruct (Z.ltb_spec v (2 ^ 31)); [reflexivity | lia]. Qed.
  Lemma w2le4_sxw : forall v, word_to_le_bytes 4 (sxw v) = word_to_le_bytes 4 (Z_to_bv 64 v).
  Proof using. intros v. unfold sxw. change 4%nat with (N.to_nat 4). change 32%N with (8 * 4)%N. apply word_to_le_bytes_swrap. cbn; lia. Qed.

  Lemma typeid_diag : forall (w : pmw MI ST) c0 K (fx : FPState) A M model c R,
    PMS w c0 K -> frm_zero (@fp_csr fx) -> CHECKK w K fx -> PMX w A M model c -> c_tr c = [] -> pm_bud (w_n w) c ->
    getr R 2%bv = Z_to_bv 64 (w_sp w) -> getr R 3%bv = Z_to_bv 64 (ly_gp Ly.L) -> getr R 4%bv = Z_to_bv 64 (ly_tp Ly.L) ->
    getr R 8%bv = Z_to_bv 64 (w_p w) ->
    srealizes SEGS (cfg fx R 0x68248 M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx A M model c R PS FZ CK X Htr BUD Qsp Qgp Qtp Qs0.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & [Gc2 Gcal] & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof (x_scal X) as (Sc1 & Sc2 & Sc3 & Sc4).
    pm_seed R w c (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R. seedHK HK w A M model c E X.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R1.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_pdiagQ w c0 K fx A M model c R1 (-10) _ []);
      [exact PS | exact X | exact Htr | exact BUD | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | rewrite G12; apply bv_eq; vm_compute; reflexivity | lia |].
    clear Qsp Qs0 Qgp Qtp. intros A1 R1c M1 model1 B1 X1 BUD1 KEPT DS1 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X0 BUD0. pose proof (x_ms X1) as MS1.
    pm_seed R1c w (set_tr c (B1 ++ [])) (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R1c. seedHK HK w A1 M1 model1 (set_tr c (B1 ++ [])) E X1.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R2.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_put_cstr w c0 K fx A1 M1 model1 (set_tr c (B1 ++ [])) R2 (-10) _ 0x12e0d 19 19 _ B1 []);
      [exact PS | exact X1 | reflexivity | exact BUD1 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS1 | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | apply ro_cstr_of_chk; vm_compute; reflexivity | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A2 R2c M2 model2 B2 X2 BUD2 KEPT _ DS2 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X1 BUD1 DS1. pose proof (x_ms X2) as MS2.
    pose proof (dl_err _ _ _ _ _ _ DL _ _ _ _ _ _ DS2) as Herrc. unfold CRep.fld in Herrc.
    assert (Cerr : cell4 SEGS M2 (w_sp w + 304 + 360) ((-10) mod 2 ^ 32)).
    { split; [pose proof (Z.mod_pos_bound (-10) (2 ^ 32)); cbn; lia | exact Herrc]. }
    pm_seed R2c w (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) [sxw ((-10) mod 2 ^ 32)].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R2c. seedHK HK w A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) E X2.
    xruns HR HK 100%nat STOPS (SCR [] [EVar 39] []) 50%N. { split_scs; try sc_auto1. all: sc_rd_sx Cerr. }
    postrun. name_run HRn R2cd. rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (22%bv) G22.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.  rewrite w_add in G10 by lia.
    eapply (pm_dtor w c0 K fx A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) R2cd (-10) _ _ B2 []);
      [exact PS | exact X2 | cbn [c_tr set_tr]; rewrite ?app_nil_r; reflexivity | exact BUD2 | rewrite Zlength_nil; lia | exact DS2 | cregs_tac G1 G2 G3 G4 | exact G10 |].
    intros Ad Rd Md modeld Xd BUDd KEPT AGd.
    keptQ KEPT G2 Qsp'. keptQ KEPT G3 Qgp'. keptQ KEPT G4 Qtp'. keptQ KEPT G8 Qs0'. keptQ KEPT G22 Qs6.
    pose proof (Z.mod_pos_bound (-10) (2 ^ 32) ltac:(lia)) as Hm'.
    assert (Hnz : (-10) mod 2 ^ 32 <> 0) by (rewrite <- (Z.mod_add (-10) 1 (2 ^ 32)) by lia; rewrite Z.mod_small by lia; lia).
    pose proof (x_ms Xd) as MSd.
    try clear E. pm_seed Rd w (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) []) [sxw ((-10) mod 2 ^ 32)].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (22%bv, EVar 39)] Rd. seedHK HK w Ad Md modeld (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) []) E Xd.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn Re. rreg HRn (2%bv) T2. rreg HRn (3%bv) T3. rreg HRn (4%bv) T4. rreg HRn (8%bv) T8. rreg HRn (22%bv) T22.
    clear HRn HR HK. fixregs. rewrite Qgp' in T3. rewrite Qtp' in T4.
    eapply (CK Ad Md modeld (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) []) Re ((-10) mod 2 ^ 32) Xd ltac:(cbn [c_tr set_tr]; reflexivity) BUDd T2 T3 T4 T8 T22 ltac:(lia)).
  Qed.

  Lemma scope_diag : forall (w : pmw MI ST) c0 K (fx : FPState) A M model c R (t : Z),
    PMS w c0 K -> frm_zero (@fp_csr fx) -> CHECKK w K fx -> PMX w A M model c -> c_tr c = [] -> pm_bud (w_n w) c ->
    getr R 2%bv = Z_to_bv 64 (w_sp w) -> getr R 3%bv = Z_to_bv 64 (ly_gp Ly.L) -> getr R 4%bv = Z_to_bv 64 (ly_tp Ly.L) ->
    getr R 8%bv = Z_to_bv 64 (w_p w) -> getr R 27%bv = Z_to_bv 64 t -> 0 <= t < 2 ^ 31 ->
    srealizes SEGS (cfg fx R 0x67c1c M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx A M model c R t PS FZ CK X Htr BUD Qsp Qgp Qtp Qs0 Q27 Ht.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & [Gc2 Gcal] & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof (x_scal X) as (Sc1 & Sc2 & Sc3 & Sc4).
    pm_seed R w c [Z_to_bv 64 t].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (27%bv, EVar 39)] R. seedHK HK w A M model c E X.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R1.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12. rreg HRn (27%bv) G27.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    try replace (Z_to_bv 5 (Z.of_N 27)) with (27%bv : reg) in * by (apply bv_eq; reflexivity). rewrite ?Q27 in *. clear Q27. rename G27 into Q27.
    eapply (pm_pdiagQ w c0 K fx A M model c R1 (-4) _ []);
      [exact PS | exact X | exact Htr | exact BUD | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | rewrite G12; apply bv_eq; vm_compute; reflexivity | lia |].
    clear Qsp Qs0 Qgp Qtp. intros A1 R1c M1 model1 B1 X1 BUD1 KEPT DS1 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp. keptQ KEPT Q27 Q27_. clear Q27. rename Q27_ into Q27.
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X0 BUD0. pose proof (x_ms X1) as MS1.
    pm_seed R1c w (set_tr c (B1 ++ [])) [Z_to_bv 64 t].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (27%bv, EVar 39)] R1c. seedHK HK w A1 M1 model1 (set_tr c (B1 ++ [])) E X1.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R2.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (27%bv) G27.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    try replace (Z_to_bv 5 (Z.of_N 27)) with (27%bv : reg) in * by (apply bv_eq; reflexivity). rewrite ?Q27 in *. clear Q27. rename G27 into Q27.
    clear Q27.
    assert (Hlit2 : 0 <= t < 2 ^ 32) by lia.
    eapply (pm_operand_type_str w A1 M1 model1 (set_tr c (B1 ++ [])) fx R2 _ K X1 (ex_intro _ t (conj Hlit2 G10)) G1 ltac:(apply bv_eq; vm_compute; reflexivity)).
    clear Qsp Qs0 Qgp Qtp. intros R2n KEPT (pnm & nnm & ROnm & Hn256 & Gnm).
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    clear G1 G2 G3 G4 G8 G10 KEPT; try clear G9; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    pose proof ROnm as RO'. destruct RO' as (Rp1 & Rn0 & Rp2 & _).
    pm_seed R2n w (set_tr c (B1 ++ [])) [Z_to_bv 64 pnm].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (10%bv, EVar 39)] R2n. seedHK HK w A1 M1 model1 (set_tr c (B1 ++ [])) E X1.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R3.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (22%bv) G22.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    try replace (Z_to_bv 5 (Z.of_N 22)) with (22%bv : reg) in * by (apply bv_eq; reflexivity). rename G22 into Q22p.
    eapply (pm_strlen w A1 M1 model1 (set_tr c (B1 ++ [])) fx R3 _ K X1 (ex_intro _ pnm (ex_intro _ nnm (conj ROnm G10))) G1 ltac:(apply bv_eq; vm_compute; reflexivity)).
    clear Qsp Qs0 Qgp Qtp. intros R3s KEPT POst. pose proof (POst pnm nnm ROnm G10) as Gsl. clear POst.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp. keptQ KEPT Q22p Q22p_. clear Q22p. rename Q22p_ into Q22p.
    clear G1 G2 G3 G4 G8 G10 KEPT; try clear G9; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    pm_seed R3s w (set_tr c (B1 ++ [])) [Z_to_bv 64 nnm; Z_to_bv 64 pnm].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (10%bv, EVar 39); (22%bv, EVar 40)] R3s. seedHK HK w A1 M1 model1 (set_tr c (B1 ++ [])) E X1.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R4.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    clear Q22p.
    eapply (pm_put_cstr w c0 K fx A1 M1 model1 (set_tr c (B1 ++ [])) R4 (-4) _ pnm nnm nnm _ B1 []);
      [exact PS | exact X1 | reflexivity | exact BUD1 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS1 | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | exact ROnm | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A4 R4c M4 model4 B4 X4 BUD4 KEPT _ DS4 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X3 BUD3 DS3. pose proof (x_ms X4) as MS4.
    pm_seed R4c w (set_tr (set_tr c (B1 ++ [])) (B4 ++ [])) (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R4c. seedHK HK w A4 M4 model4 (set_tr (set_tr c (B1 ++ [])) (B4 ++ [])) E X4.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R5.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_put_cstr w c0 K fx A4 M4 model4 (set_tr (set_tr c (B1 ++ [])) (B4 ++ [])) R5 (-4) _ 0x10c04 5 5 _ B4 []);
      [exact PS | exact X4 | reflexivity | exact BUD4 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS4 | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | apply ro_cstr_of_chk; vm_compute; reflexivity | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A5 R5c M5 model5 B5 X5 BUD5 KEPT _ DS5 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X4 BUD4 DS4. pose proof (x_ms X5) as MS5.
    pose proof (dl_err _ _ _ _ _ _ DL _ _ _ _ _ _ DS5) as Herrc. unfold CRep.fld in Herrc.
    assert (Cerr : cell4 SEGS M5 (w_sp w + 304 + 360) ((-4) mod 2 ^ 32)).
    { split; [pose proof (Z.mod_pos_bound (-4) (2 ^ 32)); cbn; lia | exact Herrc]. }
    pm_seed R5c w (set_tr (set_tr (set_tr c (B1 ++ [])) (B4 ++ [])) (B5 ++ [])) [sxw ((-4) mod 2 ^ 32)].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R5c. seedHK HK w A5 M5 model5 (set_tr (set_tr (set_tr c (B1 ++ [])) (B4 ++ [])) (B5 ++ [])) E X5.
    xruns HR HK 100%nat STOPS (SCR [] [EVar 39] []) 50%N. { split_scs; try sc_auto1. all: sc_rd_sx Cerr. }
    postrun. name_run HRn R5cd. rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (22%bv) G22.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.  rewrite w_add in G10 by lia.
    eapply (pm_dtor w c0 K fx A5 M5 model5 (set_tr (set_tr (set_tr c (B1 ++ [])) (B4 ++ [])) (B5 ++ [])) R5cd (-4) _ _ B5 []);
      [exact PS | exact X5 | cbn [c_tr set_tr]; rewrite ?app_nil_r; reflexivity | exact BUD5 | rewrite Zlength_nil; lia | exact DS5 | cregs_tac G1 G2 G3 G4 | exact G10 |].
    intros Ad Rd Md modeld Xd BUDd KEPT AGd.
    keptQ KEPT G2 Qsp'. keptQ KEPT G3 Qgp'. keptQ KEPT G4 Qtp'. keptQ KEPT G8 Qs0'. keptQ KEPT G22 Qs6.
    pose proof (Z.mod_pos_bound (-4) (2 ^ 32) ltac:(lia)) as Hm'.
    assert (Hnz : (-4) mod 2 ^ 32 <> 0) by (rewrite <- (Z.mod_add (-4) 1 (2 ^ 32)) by lia; rewrite Z.mod_small by lia; lia).
    pose proof (x_ms Xd) as MSd.
    try clear E. pm_seed Rd w (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B4 ++ [])) (B5 ++ [])) []) [sxw ((-4) mod 2 ^ 32)].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (22%bv, EVar 39)] Rd. seedHK HK w Ad Md modeld (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B4 ++ [])) (B5 ++ [])) []) E Xd.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn Re. rreg HRn (2%bv) T2. rreg HRn (3%bv) T3. rreg HRn (4%bv) T4. rreg HRn (8%bv) T8. rreg HRn (22%bv) T22.
    clear HRn HR HK. fixregs. rewrite Qgp' in T3. rewrite Qtp' in T4.
    eapply (CK Ad Md modeld (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B4 ++ [])) (B5 ++ [])) []) Re ((-4) mod 2 ^ 32) Xd ltac:(cbn [c_tr set_tr]; reflexivity) BUDd T2 T3 T4 T8 T22 ltac:(lia)).
  Qed.

  Lemma default_diag : forall (w : pmw MI ST) c0 K (fx : FPState) A M model c R (t : Z),
    PMS w c0 K -> frm_zero (@fp_csr fx) -> CHECKK w K fx -> PMX w A M model c -> c_tr c = [] -> pm_bud (w_n w) c ->
    getr R 2%bv = Z_to_bv 64 (w_sp w) -> getr R 3%bv = Z_to_bv 64 (ly_gp Ly.L) -> getr R 4%bv = Z_to_bv 64 (ly_tp Ly.L) ->
    getr R 8%bv = Z_to_bv 64 (w_p w) -> getr R 27%bv = Z_to_bv 64 t -> 0 <= t < 2 ^ 31 ->
    srealizes SEGS (cfg fx R 0x6812c M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx A M model c R t PS FZ CK X Htr BUD Qsp Qgp Qtp Qs0 Q27 Ht.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & [Gc2 Gcal] & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof (x_scal X) as (Sc1 & Sc2 & Sc3 & Sc4).
    pm_seed R w c [Z_to_bv 64 t].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (27%bv, EVar 39)] R. seedHK HK w A M model c E X.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R1.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12. rreg HRn (27%bv) G27.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    try replace (Z_to_bv 5 (Z.of_N 27)) with (27%bv : reg) in * by (apply bv_eq; reflexivity). rewrite ?Q27 in *. clear Q27. rename G27 into Q27.
    eapply (pm_pdiagQ w c0 K fx A M model c R1 (-4) _ []);
      [exact PS | exact X | exact Htr | exact BUD | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | rewrite G12; apply bv_eq; vm_compute; reflexivity | lia |].
    clear Qsp Qs0 Qgp Qtp. intros A1 R1c M1 model1 B1 X1 BUD1 KEPT DS1 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp. keptQ KEPT Q27 Q27_. clear Q27. rename Q27_ into Q27.
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X0 BUD0. pose proof (x_ms X1) as MS1.
    pm_seed R1c w (set_tr c (B1 ++ [])) [Z_to_bv 64 t].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (27%bv, EVar 39)] R1c. seedHK HK w A1 M1 model1 (set_tr c (B1 ++ [])) E X1.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R2.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12. rreg HRn (27%bv) G27.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    try replace (Z_to_bv 5 (Z.of_N 27)) with (27%bv : reg) in * by (apply bv_eq; reflexivity). rewrite ?Q27 in *. clear Q27. rename G27 into Q27.
    eapply (pm_put_cstr w c0 K fx A1 M1 model1 (set_tr c (B1 ++ [])) R2 (-4) _ 0x14455 40 40 _ B1 []);
      [exact PS | exact X1 | reflexivity | exact BUD1 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS1 | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | apply ro_cstr_of_chk; vm_compute; reflexivity | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A2 R2c M2 model2 B2 X2 BUD2 KEPT _ DS2 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp. keptQ KEPT Q27 Q27_. clear Q27. rename Q27_ into Q27.
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X1 BUD1 DS1. pose proof (x_ms X2) as MS2.
    pm_seed R2c w (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) [Z_to_bv 64 t].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (27%bv, EVar 39)] R2c. seedHK HK w A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) E X2.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R3.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (27%bv) G27.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    try replace (Z_to_bv 5 (Z.of_N 27)) with (27%bv : reg) in * by (apply bv_eq; reflexivity). rewrite ?Q27 in *. clear Q27. rename G27 into Q27.
    clear Q27.
    eapply (pm_put_int w c0 K fx A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) R3 (-4) _ (t) _ B2 []);
      [exact PS | exact X2 | reflexivity | exact BUD2 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS2 | cregs_tac G1 G2 G3 G4
      | exact G10 | rewrite G11; rewrite Z.mod_small by lia; reflexivity | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A3 R3c M3 model3 B3 X3 BUD3 KEPT _ DS3 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X2 BUD2 DS2. pose proof (x_ms X3) as MS3.
    pose proof (dl_err _ _ _ _ _ _ DL _ _ _ _ _ _ DS3) as Herrc. unfold CRep.fld in Herrc.
    assert (Cerr : cell4 SEGS M3 (w_sp w + 304 + 360) ((-4) mod 2 ^ 32)).
    { split; [pose proof (Z.mod_pos_bound (-4) (2 ^ 32)); cbn; lia | exact Herrc]. }
    pm_seed R3c w (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) [sxw ((-4) mod 2 ^ 32)].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R3c. seedHK HK w A3 M3 model3 (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) E X3.
    xruns HR HK 100%nat STOPS (SCR [] [EVar 39] []) 50%N. { split_scs; try sc_auto1. all: sc_rd_sx Cerr. }
    postrun. name_run HRn R3cd. rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (22%bv) G22.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.  rewrite w_add in G10 by lia.
    eapply (pm_dtor w c0 K fx A3 M3 model3 (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) R3cd (-4) _ _ B3 []);
      [exact PS | exact X3 | cbn [c_tr set_tr]; rewrite ?app_nil_r; reflexivity | exact BUD3 | rewrite Zlength_nil; lia | exact DS3 | cregs_tac G1 G2 G3 G4 | exact G10 |].
    intros Ad Rd Md modeld Xd BUDd KEPT AGd.
    keptQ KEPT G2 Qsp'. keptQ KEPT G3 Qgp'. keptQ KEPT G4 Qtp'. keptQ KEPT G8 Qs0'. keptQ KEPT G22 Qs6.
    pose proof (Z.mod_pos_bound (-4) (2 ^ 32) ltac:(lia)) as Hm'.
    assert (Hnz : (-4) mod 2 ^ 32 <> 0) by (rewrite <- (Z.mod_add (-4) 1 (2 ^ 32)) by lia; rewrite Z.mod_small by lia; lia).
    pose proof (x_ms Xd) as MSd.
    try clear E. pm_seed Rd w (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) []) [sxw ((-4) mod 2 ^ 32)].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (22%bv, EVar 39)] Rd. seedHK HK w Ad Md modeld (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) []) E Xd.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn Re. rreg HRn (2%bv) T2. rreg HRn (3%bv) T3. rreg HRn (4%bv) T4. rreg HRn (8%bv) T8. rreg HRn (22%bv) T22.
    clear HRn HR HK. fixregs. rewrite Qgp' in T3. rewrite Qtp' in T4.
    eapply (CK Ad Md modeld (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) []) Re ((-4) mod 2 ^ 32) Xd ltac:(cbn [c_tr set_tr]; reflexivity) BUDd T2 T3 T4 T8 T22 ltac:(lia)).
  Qed.

  Ltac arm_intro :=
    intros w c0 K fx I A M model c R wv PS FZ FC IP HAE PK CK AACC; specialize (PK fx FZ FC); specialize (CK fx FZ FC);
    pose proof (AE_facts w I A M model c R _ wv IP HAE) as (_ & _ & Hoff & V3B & _ & _);
    destruct HAE as (OB & Hw1 & Hw2 & Hn & Hv1 & Hv2 & Hlen & Ht31 & Hword & Q22 & Q27 & Q24 & Q23 & Q26 & PO & C712);
    pose proof OB as OB'; destruct OB' as (X & Htr & BUD & OR & LM & IC & FR & Hic & Hend & Hwnz & MAC & V3R);
    pose proof (x_geo X) as GEO; pose proof ac_bounds_lit as Hcv; pose proof (x_ms X) as MS;
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & [Gc2 Gcal] & Gap & Gn & Gw); unfold w_sp0, PM_FRAME, PARSER_SIZE in *;
    pose proof OR as OR'; destruct OR' as (Qsp & Qgp & Qtp & Qs0 & Qs1 & Qs2 & Qs3 & Qs4 & Qs5 & Qs9);
    destruct PO as (_ & C718 & _).

#[local] Definition HTPmBodyU1_2 : list (reg * expr) := [(2%bv, EVar 32); (8%bv, EVar 33); (22%bv, EVar 39); (27%bv, EVar 40); (23%bv, EVar 41); (26%bv, EVar 42)].
  Theorem arm_TYPEID_U1 : forall t, t = 2 -> arm_stmt t 0x67dd8.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros t Ht. arm_intro.
    assert (Q22' : getr R 22%bv = sxw wv) by (rewrite Q22; symmetry; apply sxw_sx32; lia).
    destruct (Z.eq_dec wv 0) as [Hw0 | Hwn0].
    -
      assert (Q22z : getr R 22%bv = Z_to_bv 64 0) by (rewrite Q22', Hw0; apply (sxw_small' 0); lia).
      pm_seed R w c (@nil word).
      seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (22%bv, ELit 0)] R. seedHK HK w A M model c E X.
      xruns HR HK 100%nat (0x68248 :: STOPS) (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
      postrun. name_run HRn R1.
      rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8.
      clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
      exact (typeid_diag w c0 K fx A M model c R1 PS FZ CK X Htr BUD G2 G3 G4 G8).
    -
      pm_seed R w c [sxw wv; Z_to_bv 64 t; Z_to_bv 64 (i_io I); Z_to_bv 64 (i_op I)].
      seedHR HR E (HTPmBodyU1_2 ++ OREGSEED)%list R. seedHK HK w A M model c E X.
      xruns HR HK 100%nat STOPS (SCR [false] [] []) 50%N.
      { split_scs; try sc_auto1; cbn [sc_denot]; evs; rewrite <- ?(sxw_small' 0) by lia; rewrite br_eq_sxw by lia; bool_lia. }
      postrun. name_run HRn R1.
      rreg HRn (27%bv) G27. rreg HRn (23%bv) G23. rreg HRn (26%bv) G26.
      assert (OR1 : oregs w R1) by (oregs_seeded HRn Qgp Qtp). clear HRn HR HK.
      rewrite w2le4_sxw.
      lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ => set (M1 := m) in * end.
      assert (ST1 : stores_in (zwin (w_sp w + 256) (w_sp w + 260)) M M1) by (unfold M1; stin).
      assert (X1 : PMX w A M1 model c).
      { eapply (pmx_frame_stores SEGS Ly.L MI ST ly_img_low ly_rw_img ly_relro_img w A M M1 model c (zwin (w_sp w + 256) (w_sp w + 260)));
          [exact X | exact ST1 | unfold zwin, w_sp0, PM_FRAME; intros; lia]. }
      assert (AG1 : CRep.agree_on (fun a => w_sp w <= a < w_sp w + 864 /\ ~ zwin (w_sp w + 256) (w_sp w + 260) a) M M1).
      { eapply stores_in_agree; [exact ST1 | intros b Hb; unfold zwin in *; lia]. }
      assert (LM1 : loop_mem w M1) by (eapply (loop_mem_frame w M M1); [exact LM | lia | lia | eapply agree_on_weaken; [exact AG1 | unfold zwin; cbn; intros; lia]]).
      assert (IC1 : ictx w M1 (i_io I) (i_fw I) (i_iwc I) (i_op I) (i_d I)) by (eapply (ictx_agree w M M1); [exact IC | lia | lia | eapply agree_on_weaken; [exact AG1 | unfold zwin; cbn; intros; lia]]).
      assert (FR1 : ifr w M1) by (unfold M1; apply ifr_store4; [exact FR | right; left; reflexivity | lia | lia | lia]).
      assert (C718' : cellw SEGS M1 (w_sp w + 718) 2 1).
      { eapply (cellw_frame M M1); [exact C718 | lia | cbn; lia | eapply agree_on_weaken; [exact AG1 | unfold zwin; cbn; intros; lia]]. }
      pose proof (x_ms X1) as MS1. clear ST1 AG1. clearbody M1.
      eapply (PK A M1 model c R1 1 []).
      + split; [exact X1|]. split; [exact Htr|]. split; [exact BUD|]. split; [exact OR1|]. split; [exact LM1|]. split; [exact IC1|]. split; [exact FR1|].
        split; [exact Hic|]. split; [exact Hend|]. split; [exact Hwnz|]. split; [exact MAC | exact V3R].
      + exact G27. + exact G23. + exact G26. + exact C718'. + left; lia.
      + reflexivity. + reflexivity. + reflexivity.
      + change (Z.min 1 1) with 1. lia.
      + rewrite app_nil_r. reflexivity. + exact PmZw.seed_free_nil. + rewrite PmZw.Zlen_nil. lia. + left; reflexivity.
      + reflexivity. + left; reflexivity. + left; reflexivity. + intros [].
  Qed.

  Theorem arm_SCOPE_U1 : forall t, (t = 4 \/ t = 5) -> arm_stmt t 0x67c18.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros t Ht. arm_intro.
    assert (Q22' : getr R 22%bv = sxw wv) by (rewrite Q22; symmetry; apply sxw_sx32; lia).
    destruct (Z.eq_dec wv 0) as [Hw0 | Hwn0].
    -
      assert (Q22z : getr R 22%bv = Z_to_bv 64 0) by (rewrite Q22', Hw0; apply (sxw_small' 0); lia).
      pm_seed R w c [Z_to_bv 64 t].
      seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (22%bv, ELit 0); (27%bv, EVar 39)] R. seedHK HK w A M model c E X.
      xruns HR HK 100%nat (0x67c1c :: STOPS) (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
      postrun. name_run HRn R1.
      rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (27%bv) G27.
      clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
      try replace (Z_to_bv 5 (Z.of_N 27)) with (27%bv : reg) in G27 by (apply bv_eq; reflexivity).
      exact (scope_diag w c0 K fx A M model c R1 t PS FZ CK X Htr BUD G2 G3 G4 G8 G27 Ht31).
    -
      pm_seed R w c [sxw wv; Z_to_bv 64 t; Z_to_bv 64 (i_io I); Z_to_bv 64 (i_op I)].
      seedHR HR E (HTPmBodyU1_2 ++ OREGSEED)%list R. seedHK HK w A M model c E X.
      xruns HR HK 100%nat STOPS (SCR [true] [] []) 50%N.
      { split_scs; try sc_auto1; cbn [sc_denot]; evs; rewrite <- ?(sxw_small' 0) by lia; rewrite br_ne_sxw by lia; bool_lia. }
      postrun. name_run HRn R1.
      rreg HRn (27%bv) G27. rreg HRn (23%bv) G23. rreg HRn (26%bv) G26.
      assert (OR1 : oregs w R1) by (oregs_seeded HRn Qgp Qtp). clear HRn HR HK.
      eapply (PK A M model c R1 1 []).
      + split; [exact X|]. split; [exact Htr|]. split; [exact BUD|]. split; [exact OR1|]. split; [exact LM|]. split; [exact IC|]. split; [exact FR|].
        split; [exact Hic|]. split; [exact Hend|]. split; [exact Hwnz|]. split; [exact MAC | exact V3R].
      + exact G27. + exact G23. + exact G26. + exact C718. + left; lia.
      + reflexivity. + reflexivity. + reflexivity.
      + change (Z.min 1 1) with 1. lia.
      + rewrite app_nil_r. reflexivity. + exact PmZw.seed_free_nil. + rewrite PmZw.Zlen_nil. lia. + left; reflexivity.
      + reflexivity. + left; reflexivity. + left; reflexivity. + intros [].
  Qed.

  Theorem arm_DEFAULT_U1 : forall t, arm_stmt t 0x6812c.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros t. arm_intro.
    exact (default_diag w c0 K fx A M model c R t PS FZ CK X Htr BUD Qsp Qgp Qtp Qs0 Q27 Ht31).
  Qed.
End PM.
End PmArm_TyScDfU1.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmArm_EnumU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmArm_IdU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmArm_SpecU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmArm_ExtU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmArm_MaskU1.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmArm_RidLibU1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Module PmArm_RidU1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.

Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PropExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SeqExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StepTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.WalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StartupTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SumWalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StoreOk OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MemSplit OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Hoare OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ShapeAlg OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SRealizes OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefReadLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.FPSteps OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibIface OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibBudget OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibEff OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MmapSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibMaskBits OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ZStores OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3Sound OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymRun3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.U1Layout.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.CRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.StrLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.LiveStats OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContStmts2 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.U1Facts.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRepFacts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HStmtsU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HCommonU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HConstsU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HWord.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsGrammar OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsNeeds OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsInv OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmBaseU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmHyps OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmHypsU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmCoreU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStepU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep2U1.PmUpdU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep2U1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmLoopU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmInstU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep3U1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmZw OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmODefsU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep4U1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep5U1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmArm_RidLibU1.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Abbreviation SEGS := Ubsan.M.loaded_segments.

Lemma in_reg_list : forall (r : bv 5) (l : list (bv 5)),
  existsb (fun x => Z.eqb (bv_unsigned x) (bv_unsigned r)) l = true -> In r l.
Proof.
  intros r l; induction l as [|x l IH]; cbn; [discriminate|]. intros H. apply Bool.orb_true_iff in H.
  destruct H as [H|H]; [left; apply bv_eq; apply Z.eqb_eq; exact H | right; apply IH; exact H].
Qed.
Ltac keptQ KEPT G Q ::=
  lazymatch type of G with getr _ ?r = _ => pose proof G as Q; rewrite <- (KEPT r) in Q by (clear; apply in_reg_list; reflexivity) end.

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
  #[local] Notation pm_exit := (PmCoreU1.pm_exit MI ST).
  #[local] Notation pmx_ds_room := (PmStepU1.pmx_ds_room CL).
  #[local] Notation pm_tail_6733c := (PmStepU1.pm_tail_6733c CL).
  #[local] Notation cregs_kept := (PmStepU1.cregs_kept CL).
  #[local] Notation pm_put_cstr := (PmStepU1.pm_put_cstr CL).
  #[local] Notation pm_put_chars := (PmStepU1.pm_put_chars CL).
  #[local] Notation pm_put_num := (PmStepU1.pm_put_num CL).
  #[local] Notation pm_put_u16 := (PmStepU1.pm_put_u16 CL).
  #[local] Notation pm_put_u32 := (PmStepU1.pm_put_u32 CL).
  #[local] Notation pm_put_u64 := (PmStepU1.pm_put_u64 CL).
  #[local] Notation pm_put_int := (PmStepU1.pm_put_int CL).
  #[local] Notation pm_pdiagQ := (PmStepU1.pm_pdiagQ CL).
  #[local] Notation pm_dtor := (PmStepU1.pm_dtor CL).
  #[local] Notation pm_exhausted := (PmStepU1.pm_exhausted CL).
  #[local] Notation pm_fixword := (PmStepU1.pm_fixword CL).
  #[local] Notation pm_is_host_endian := (PmStepU1.pm_is_host_endian CL).
  #[local] Notation pm_binend := (PmStepU1.pm_binend CL).
  #[local] Notation pm_ecw_pbs := (PmStep2U1.pm_ecw_pbs CL).
  #[local] Notation pm_opcode_split := (PmStep2U1.pm_opcode_split CL).
  #[local] Notation pm_lookup_opcode := (PmStep2U1.pm_lookup_opcode CL).
  #[local] Notation pm_lookup_operand := (PmStep2U1.pm_lookup_operand CL).
  #[local] Notation pm_lookup_ext := (PmStep2U1.pm_lookup_ext CL).
  #[local] Notation pm_idesc_operands := (PmStep3U1.pm_idesc_operands CL).
  #[local] Notation pm_odesc_operands := (PmStep3U1.pm_odesc_operands CL).
  #[local] Notation pm_edesc_operands := (PmStep3U1.pm_edesc_operands CL).
  #[local] Notation pm_push_types := (PmStep3U1.pm_push_types CL).
  #[local] Notation pm_take_first := (PmStep3U1.pm_take_first CL).

  #[local] Notation izero := (PmInstU1.izero).
  #[local] Notation ictx := (PmInstU1.ictx).
  #[local] Notation nodes := (PmLoopU1.nodes).
  #[local] Notation macct := (PmLoopU1.macct).
  #[local] Notation GOK := (cu_G _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
  #[local] Notation MAXLEN := (cu_maxlen _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
  #[local] Notation MASKLEN := (cu_mask_len _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
  #[local] Notation ipure := (PmODefsU1.ipure (G:=G) (idesc:=idesc)).
  #[local] Notation arm_stmt := (PmODefsU1.arm_stmt (MI:=MI) (ST:=ST) (G:=G) (idesc:=idesc)).
  #[local] Notation OBASE := (PmODefsU1.OBASE (MI:=MI) (ST:=ST)).
  #[local] Notation oregs := (PmODefsU1.oregs (MI:=MI) (ST:=ST)).
  #[local] Notation ifr := (PmODefsU1.ifr (MI:=MI) (ST:=ST)).
  #[local] Notation popnd := (PmODefsU1.popnd (MI:=MI) (ST:=ST)).
  #[local] Notation pm_find_m3 := (PmStep4U1.pm_find_m3 CL).
  #[local] Notation pm_find_m1 := (PmStep4U1.pm_find_m1 CL).
  #[local] Notation pm_spec_lookup := (PmStep4U1.pm_spec_lookup CL).
  #[local] Notation pm_oty_pb := (PmStep4U1.pm_oty_pb CL).
  Definition pm_is_ext_inst := pm_leafA (MI:=MI) (ST:=ST) _ _ _ (cu_is_ext_inst _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
  Definition pm_is_nonsemantic := pm_leafA (MI:=MI) (ST:=ST) _ _ _ (cu_is_nonsemantic _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
  Definition pm_operand_type_str := pm_leafA (MI:=MI) (ST:=ST) _ _ _ (cu_operand_type_str _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
  Definition pm_strlen := pm_leafA (MI:=MI) (ST:=ST) _ _ _ (cu_strlen _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).

  Ltac oregs_seeded HRn Qgp Qtp :=
    let G2 := fresh in let G3 := fresh in let G4 := fresh in let G8 := fresh in let G9 := fresh in
    let G18 := fresh in let G19 := fresh in let G20 := fresh in let G21 := fresh in let G25 := fresh in
    rreg HRn 2%bv G2; rreg HRn 3%bv G3; rreg HRn 4%bv G4; rreg HRn 8%bv G8; rreg HRn 9%bv G9;
    rreg HRn 18%bv G18; rreg HRn 19%bv G19; rreg HRn 20%bv G20; rreg HRn 21%bv G21; rreg HRn 25%bv G25;
    unfold oregs, loop_regs; rewrite G2, G3, G4, G8, G9, G18, G19, G20, G21, G25; fixregs; rewrite ?Qgp, ?Qtp;
    rewrite ?SymExec.alu64_add_lit; repeat split; reflexivity.
  #[local] Notation OREGSEED := [(9%bv, EAlu ALU_ADD (EVar 33) (ELit 88)); (18%bv, ELit 1); (19%bv, ELit (2 ^ 61)); (20%bv, ELit 20); (21%bv, EAlu ALU_ADD (EVar 33) (ELit 264)); (25%bv, ELit 5)]%list.

  Lemma sxw_small' : forall v, 0 <= v < 2 ^ 31 -> sxw v = Z_to_bv 64 v.
  Proof using. intros v Hv. unfold sxw. rewrite bv_swrap32_cases by lia. destruct (Z.ltb_spec v (2 ^ 31)); [reflexivity | lia]. Qed.
  Lemma w2le4_sxw : forall v, word_to_le_bytes 4 (sxw v) = word_to_le_bytes 4 (Z_to_bv 64 v).
  Proof using. intros v. unfold sxw. change 4%nat with (N.to_nat 4). change 32%N with (8 * 4)%N. apply word_to_le_bytes_swrap. cbn; lia. Qed.
  #[local] Notation set_m1 := (PmArm_RidLibU1.set_m1).
  #[local] Notation pm_m1_setval := (PmArm_RidLibU1.pm_m1_setval (MI:=MI) (ST:=ST)).
  #[local] Notation pm_index_m1 := (PmArm_RidLibU1.pm_index_m1 CL).

  Lemma rid_diag_a : forall (w : pmw MI ST) c0 K (fx : FPState) A M model c R,
    PMS w c0 K -> frm_zero (@fp_csr fx) -> CHECKK w K fx -> PMX w A M model c -> c_tr c = [] -> pm_bud (w_n w) c ->
    getr R 2%bv = Z_to_bv 64 (w_sp w) -> getr R 3%bv = Z_to_bv 64 (ly_gp Ly.L) -> getr R 4%bv = Z_to_bv 64 (ly_tp Ly.L) ->
    getr R 8%bv = Z_to_bv 64 (w_p w) ->
    srealizes SEGS (cfg fx R 0x68270 M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx A M model c R PS FZ CK X Htr BUD Qsp Qgp Qtp Qs0.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & [Gc2 Gcal] & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof (x_scal X) as (Sc1 & Sc2 & Sc3 & Sc4).
    pm_seed R w c (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R. seedHK HK w A M model c E X.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R1.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_pdiagQ w c0 K fx A M model c R1 (-10) _ []);
      [exact PS | exact X | exact Htr | exact BUD | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | rewrite G12; apply bv_eq; vm_compute; reflexivity | lia |].
    clear Qsp Qs0 Qgp Qtp. intros A1 R1c M1 model1 B1 X1 BUD1 KEPT DS1 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X0 BUD0. pose proof (x_ms X1) as MS1.
    pm_seed R1c w (set_tr c (B1 ++ [])) (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R1c. seedHK HK w A1 M1 model1 (set_tr c (B1 ++ [])) E X1.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R2.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_put_cstr w c0 K fx A1 M1 model1 (set_tr c (B1 ++ [])) R2 (-10) _ 0x14224 21 21 _ B1 []);
      [exact PS | exact X1 | reflexivity | exact BUD1 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS1 | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | apply ro_cstr_of_chk; vm_compute; reflexivity | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A2 R2c M2 model2 B2 X2 BUD2 KEPT _ DS2 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X1 BUD1 DS1. pose proof (x_ms X2) as MS2.
    pose proof (dl_err _ _ _ _ _ _ DL _ _ _ _ _ _ DS2) as Herrc. unfold CRep.fld in Herrc.
    assert (Cerr : cell4 SEGS M2 (w_sp w + 304 + 360) ((-10) mod 2 ^ 32)).
    { split; [pose proof (Z.mod_pos_bound (-10) (2 ^ 32)); cbn; lia | exact Herrc]. }
    pm_seed R2c w (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) [sxw ((-10) mod 2 ^ 32)].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R2c. seedHK HK w A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) E X2.
    xruns HR HK 100%nat STOPS (SCR [] [EVar 39] []) 50%N. { split_scs; try sc_auto1. all: sc_rd_sx Cerr. }
    postrun. name_run HRn R2cd. rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (22%bv) G22.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.  rewrite w_add in G10 by lia.
    eapply (pm_dtor w c0 K fx A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) R2cd (-10) _ _ B2 []);
      [exact PS | exact X2 | cbn [c_tr set_tr]; rewrite ?app_nil_r; reflexivity | exact BUD2 | rewrite Zlength_nil; lia | exact DS2 | cregs_tac G1 G2 G3 G4 | exact G10 |].
    intros Ad Rd Md modeld Xd BUDd KEPT AGd.
    keptQ KEPT G2 Qsp'. keptQ KEPT G3 Qgp'. keptQ KEPT G4 Qtp'. keptQ KEPT G8 Qs0'. keptQ KEPT G22 Qs6.
    pose proof (Z.mod_pos_bound (-10) (2 ^ 32) ltac:(lia)) as Hm'.
    assert (Hnz : (-10) mod 2 ^ 32 <> 0) by (rewrite <- (Z.mod_add (-10) 1 (2 ^ 32)) by lia; rewrite Z.mod_small by lia; lia).
    pose proof (x_ms Xd) as MSd.
    try clear E. pm_seed Rd w (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) []) [sxw ((-10) mod 2 ^ 32)].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (22%bv, EVar 39)] Rd. seedHK HK w Ad Md modeld (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) []) E Xd.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn Re. rreg HRn (2%bv) T2. rreg HRn (3%bv) T3. rreg HRn (4%bv) T4. rreg HRn (8%bv) T8. rreg HRn (22%bv) T22.
    clear HRn HR HK. fixregs. rewrite Qgp' in T3. rewrite Qtp' in T4.
    eapply (CK Ad Md modeld (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) []) Re ((-10) mod 2 ^ 32) Xd ltac:(cbn [c_tr set_tr]; reflexivity) BUDd T2 T3 T4 T8 T22 ltac:(lia)).
  Qed.

  Lemma rid_diag_b : forall (w : pmw MI ST) c0 K (fx : FPState) A M model c R (wv : Z),
    PMS w c0 K -> frm_zero (@fp_csr fx) -> CHECKK w K fx -> PMX w A M model c -> c_tr c = [] -> pm_bud (w_n w) c ->
    getr R 2%bv = Z_to_bv 64 (w_sp w) -> getr R 3%bv = Z_to_bv 64 (ly_gp Ly.L) -> getr R 4%bv = Z_to_bv 64 (ly_tp Ly.L) ->
    getr R 8%bv = Z_to_bv 64 (w_p w) -> cellw SEGS M (w_sp w + 260) 4 wv ->
    srealizes SEGS (cfg fx R 0x67e34 M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx A M model c R wv PS FZ CK X Htr BUD Qsp Qgp Qtp Qs0 C260.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & [Gc2 Gcal] & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof (x_scal X) as (Sc1 & Sc2 & Sc3 & Sc4).
    pose proof (proj1 C260) as Hwv. cbn in Hwv.
    pm_seed R w c (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R. seedHK HK w A M model c E X.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R1.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_pdiagQ w c0 K fx A M model c R1 (-10) _ []);
      [exact PS | exact X | exact Htr | exact BUD | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | rewrite G12; apply bv_eq; vm_compute; reflexivity | lia |].
    clear Qsp Qs0 Qgp Qtp. intros A1 R1c M1 model1 B1 X1 BUD1 KEPT DS1 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    eapply (cellw_frame _ M1) in C260; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X0 BUD0. pose proof (x_ms X1) as MS1.
    pm_seed R1c w (set_tr c (B1 ++ [])) (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R1c. seedHK HK w A1 M1 model1 (set_tr c (B1 ++ [])) E X1.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R2.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_put_cstr w c0 K fx A1 M1 model1 (set_tr c (B1 ++ [])) R2 (-10) _ 0x126e9 3 3 _ B1 []);
      [exact PS | exact X1 | reflexivity | exact BUD1 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS1 | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | apply ro_cstr_of_chk; vm_compute; reflexivity | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A2 R2c M2 model2 B2 X2 BUD2 KEPT _ DS2 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    eapply (cellw_frame _ M2) in C260; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X1 BUD1 DS1. pose proof (x_ms X2) as MS2.
    pm_seed R2c w (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) [sxw wv].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R2c. seedHK HK w A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) E X2.
    xruns HR HK 100%nat STOPS (SCR [] [EVar 39] []) 50%N. { split_scs; try sc_auto1. all: sc_rd_sx C260. }
    postrun. name_run HRn R3.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_put_u32 w c0 K fx A2 M2 model2 (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) R3 (-10) _ (wv) _ B2 []);
      [exact PS | exact X2 | reflexivity | exact BUD2 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS2 | cregs_tac G1 G2 G3 G4
      | exact G10 | rewrite G11; apply sxw_sx32; lia | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A3 R3c M3 model3 B3 X3 BUD3 KEPT _ DS3 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    eapply (cellw_frame _ M3) in C260; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X2 BUD2 DS2. pose proof (x_ms X3) as MS3.
    pm_seed R3c w (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R3c. seedHK HK w A3 M3 model3 (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) E X3.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R4.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_put_cstr w c0 K fx A3 M3 model3 (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) R4 (-10) _ 0x1340d 26 26 _ B3 []);
      [exact PS | exact X3 | reflexivity | exact BUD3 | first [rewrite Zlength_nil; lia | cbn; unfold Zlength; cbn; lia] | exact DS3 | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | apply ro_cstr_of_chk; vm_compute; reflexivity | lia | unfold DS_MAXLEN; lia |].
    clear Qsp Qs0 Qgp Qtp. intros A4 R4c M4 model4 B4 X4 BUD4 KEPT _ DS4 AG.
    keptQ KEPT G2 Qsp. keptQ KEPT G8 Qs0. keptQ KEPT G3 Qgp. keptQ KEPT G4 Qtp.
    clear G1 G2 G3 G4 G8 KEPT AG; try clear G9; try clear G10; try clear G11; try clear G12; try clear G13; try clear G14; try clear G15.
    try clear X3 BUD3 DS3. pose proof (x_ms X4) as MS4.
    pose proof (dl_err _ _ _ _ _ _ DL _ _ _ _ _ _ DS4) as Herrc. unfold CRep.fld in Herrc.
    assert (Cerr : cell4 SEGS M4 (w_sp w + 304 + 360) ((-10) mod 2 ^ 32)).
    { split; [pose proof (Z.mod_pos_bound (-10) (2 ^ 32)); cbn; lia | exact Herrc]. }
    pm_seed R4c w (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) (B4 ++ [])) [sxw ((-10) mod 2 ^ 32)].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R4c. seedHK HK w A4 M4 model4 (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) (B4 ++ [])) E X4.
    xruns HR HK 100%nat STOPS (SCR [] [EVar 39] []) 50%N. { split_scs; try sc_auto1. all: sc_rd_sx Cerr. }
    postrun. name_run HRn R4cd. rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (22%bv) G22.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.  rewrite w_add in G10 by lia.
    eapply (pm_dtor w c0 K fx A4 M4 model4 (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) (B4 ++ [])) R4cd (-10) _ _ B4 []);
      [exact PS | exact X4 | cbn [c_tr set_tr]; rewrite ?app_nil_r; reflexivity | exact BUD4 | rewrite Zlength_nil; lia | exact DS4 | cregs_tac G1 G2 G3 G4 | exact G10 |].
    intros Ad Rd Md modeld Xd BUDd KEPT AGd.
    keptQ KEPT G2 Qsp'. keptQ KEPT G3 Qgp'. keptQ KEPT G4 Qtp'. keptQ KEPT G8 Qs0'. keptQ KEPT G22 Qs6.
    pose proof (Z.mod_pos_bound (-10) (2 ^ 32) ltac:(lia)) as Hm'.
    assert (Hnz : (-10) mod 2 ^ 32 <> 0) by (rewrite <- (Z.mod_add (-10) 1 (2 ^ 32)) by lia; rewrite Z.mod_small by lia; lia).
    pose proof (x_ms Xd) as MSd.
    try clear E. pm_seed Rd w (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) (B4 ++ [])) []) [sxw ((-10) mod 2 ^ 32)].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (22%bv, EVar 39)] Rd. seedHK HK w Ad Md modeld (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) (B4 ++ [])) []) E Xd.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn Re. rreg HRn (2%bv) T2. rreg HRn (3%bv) T3. rreg HRn (4%bv) T4. rreg HRn (8%bv) T8. rreg HRn (22%bv) T22.
    clear HRn HR HK. fixregs. rewrite Qgp' in T3. rewrite Qtp' in T4.
    eapply (CK Ad Md modeld (set_tr (set_tr (set_tr (set_tr (set_tr c (B1 ++ [])) (B2 ++ [])) (B3 ++ [])) (B4 ++ [])) []) Re ((-10) mod 2 ^ 32) Xd ltac:(cbn [c_tr set_tr]; reflexivity) BUDd T2 T3 T4 T8 T22 ltac:(lia)).
  Qed.

  Definition pm_generates_type := pm_leafA (MI:=MI) (ST:=ST) _ _ _ (cu_generates_type _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).

  Theorem arm_RESULTID_U1 : arm_stmt 3 0x67e1c.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx I A M model c R wv PS FZ FC IP HAE PK CK AACC. specialize (CK fx FZ FC).
    pose proof (AE_facts w I A M model c R 3 wv IP HAE) as (_ & _ & Hoff & V3B & _ & _).
    destruct HAE as (OB & Hw1 & Hw2 & Hn & Hv1 & Hv2 & Hlen & Ht & Hword & Q22 & Q27 & Q24 & Q23 & Q26 & PO & C712).
    pose proof OB as OB'. destruct OB' as (X & Htr & BUD & OR & LM & IC & FR & Hic & Hend & Hwnz & MAC & V3R).
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & [Gc2 Gcal] & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof OR as OR'. destruct OR' as (Qsp & Qgp & Qtp & Qs0 & Qs1 & Qs2 & Qs3 & Qs4 & Qs5 & Qs9).
    pose proof (ipure_ranges I IP) as (Riwc & Rop).
    destruct PO as (_ & C718 & _).
    assert (Q22' : getr R 22%bv = sxw wv) by (rewrite Q22; symmetry; apply sxw_sx32; lia).
    destruct (Z.eq_dec wv 0) as [Hw0 | Hwn0].
    -
      assert (Q22z : getr R 22%bv = Z_to_bv 64 0) by (rewrite Q22', Hw0; apply (sxw_small' 0); lia).
      pm_seed R w c (@nil word).
      seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (22%bv, ELit 0)] R. seedHK HK w A M model c E X.
      xruns HR HK 100%nat (0x68270 :: STOPS) (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
      postrun. name_run HRn R1.
      rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8.
      clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
      exact (rid_diag_a w c0 K fx A M model c R1 PS FZ CK X Htr BUD G2 G3 G4 G8).
    -
      pm_seed R w c [sxw wv; Z_to_bv 64 (i_op I); Z_to_bv 64 (i_io I)].
      seedHR HR E ([(2%bv, EVar 32); (8%bv, EVar 33); (22%bv, EVar 39); (26%bv, EVar 40); (23%bv, EVar 41); (27%bv, ELit 3)] ++ OREGSEED)%list R. seedHK HK w A M model c E X.
      apply (know_more E M [KWord (SA (EVar 32) 88) (N.to_nat 8) (EAlu ALU_ADD (EVar 33) (ELit 96))]) in HK.
      2: { repeat apply Forall_cons; try apply Forall_nil.
           eapply kword_var; [eapply (loop_mem_cell w M 88); [exact LM | (first [ solve [cbn [In]; repeat (first [left; reflexivity | right])] | cbn; repeat (first [left; reflexivity | right]) ]) | lia] | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; rewrite w_add by lia; reflexivity]. }
      xruns HR HK 100%nat STOPS (SCR [false] [] []) 50%N.
      { split_scs; try sc_auto1; cbn [sc_denot]; evs; rewrite <- ?(sxw_small' 0) by lia; rewrite br_eq_sxw by lia; bool_lia. }
      postrun. name_run HRn R1.
      rreg HRn (1%bv) G1. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (22%bv) G22. rreg HRn (23%bv) G23. rreg HRn (27%bv) G27. rreg HRn (26%bv) G26.
      assert (OR1 : oregs w R1) by (oregs_seeded HRn Qgp Qtp).
      pose proof OR1 as OR'. destruct OR' as (G2 & G3 & G4 & G8 & _). clear HRn HR HK.
      rewrite w_add in G10, G11 by lia. rewrite w2le4_sxw.
      lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ => set (M1 := m) in * end.
      assert (ST1 : stores_in (zwin (w_sp w + 260) (w_sp w + 264)) M M1) by (unfold M1; stin).
      assert (X1 : PMX w A M1 model c).
      { eapply (pmx_frame_stores SEGS Ly.L MI ST ly_img_low ly_rw_img ly_relro_img w A M M1 model c (zwin (w_sp w + 260) (w_sp w + 264)));
          [exact X | exact ST1 | unfold zwin, w_sp0, PM_FRAME; intros; lia]. }
      assert (AG1 : CRep.agree_on (fun a => w_sp w <= a < w_sp w + 864 /\ ~ zwin (w_sp w + 260) (w_sp w + 264) a) M M1).
      { eapply stores_in_agree; [exact ST1 | intros b Hb; unfold zwin in *; lia]. }
      assert (LM1 : loop_mem w M1) by (eapply (loop_mem_frame w M M1); [exact LM | lia | lia | eapply agree_on_weaken; [exact AG1 | unfold zwin; cbn; intros; lia]]).
      assert (IC1 : ictx w M1 (i_io I) (i_fw I) (i_iwc I) (i_op I) (i_d I)) by (eapply (ictx_agree w M M1); [exact IC | lia | lia | eapply agree_on_weaken; [exact AG1 | unfold zwin; cbn; intros; lia]]).
      assert (FR1 : ifr w M1) by (unfold M1; apply ifr_store4; [exact FR | right; right; reflexivity | lia | lia | lia]).
      assert (C718' : cellw SEGS M1 (w_sp w + 718) 2 1).
      { eapply (cellw_frame M M1); [exact C718 | lia | cbn; lia | eapply agree_on_weaken; [exact AG1 | unfold zwin; cbn; intros; lia]]. }
      assert (C260 : cellw SEGS M1 (w_sp w + 260) 4 wv) by (split; [cbn; lia | unfold M1; rdback]).
      pose proof (x_ms X1) as MS1. clear ST1 AG1. clearbody M1.
      eapply (pm_find_m1 w A M1 model c fx R1 (w_sp w + 260) wv 0x67e30 K X1 ltac:(unfold O_M1; exact G10) G11 C260 ltac:(lia) ltac:(lia) G1 ltac:(apply bv_eq; vm_compute; reflexivity)).
      intros R2 p KEPT Hp Hfound.
      keptQ KEPT G2 Qsp2. keptQ KEPT G8 Qs02. keptQ KEPT G3 Qgp2. keptQ KEPT G4 Qtp2.
      keptQ KEPT G22 Q22b. keptQ KEPT G23 Q23b. keptQ KEPT G27 Q27b. keptQ KEPT G26 Q26b.
      pose proof (oregs_kept w R1 R2 OR1 KEPT) as OR2. pose proof OR2 as OR'. destruct OR' as (_ & _ & _ & _ & Ps1 & Ps2 & Ps3 & Ps4 & Ps5 & Ps9).
      clear KEPT G1 G2 G3 G4 G8 G10 G11 G22 G23 G27 G26 OR1.
      destruct Hfound as [-> | (Hp0 & Hp47 & Hpal & v0 & Hin0 & Cv0)].
      2: {
           pm_seed R2 w c [Z_to_bv 64 p].
           seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (10%bv, EVar 39)] R2. seedHK HK w A M1 model c E X1.
           apply (know_more E M1 [KRange (EVar 39) 1 (2 ^ 47)]) in HK.
           2: { repeat apply Forall_cons; try apply Forall_nil. eapply krange_var; [evs; reflexivity | lia | lia]. }
           xruns HR HK 100%nat (0x67e34 :: STOPS) (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
           postrun. name_run HRn R3.
           rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8.
           clear HRn HR HK. fixregs. rewrite Qgp2 in G3. rewrite Qtp2 in G4.
           exact (rid_diag_b w c0 K fx A M1 model c R3 wv PS FZ CK X1 Htr BUD G2 G3 G4 G8 C260). }

      pm_seed R2 w c [Z_to_bv 64 (i_op I)].
      seedHR HR E ([(2%bv, EVar 32); (8%bv, EVar 33); (10%bv, ELit 0); (26%bv, EVar 39)] ++ OREGSEED)%list R2. seedHK HK w A M1 model c E X1.
      apply (know_more E M1 [KRange (EVar 39) 0 65535]) in HK.
      2: { repeat apply Forall_cons; try apply Forall_nil. eapply krange_var; [evs; reflexivity | lia | lia]. }
      xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
      postrun. name_run HRn R3.
      rreg HRn (1%bv) G1. rreg HRn (10%bv) G10. rreg HRn (26%bv) G26.
      assert (OR3 : oregs w R3) by (oregs_seeded HRn Qgp2 Qtp2).
      pose proof OR3 as OR'. destruct OR' as (G2 & G3 & G4 & G8 & _).
      pose proof (syms_id_sound _ _ _ _ [22; 23; 27]%bv HRn eq_refl) as GK3. clear HRn HR HK. fixregs.
      rewrite ?ext_val_zx2 in G10 by lia.
      assert (Rop32 : 0 <= i_op I < 2 ^ 32) by lia.
      eapply (pm_generates_type w A M1 model c fx R3 _ K X1 (ex_intro _ (i_op I) (conj Rop32 G10)) G1 ltac:(apply bv_eq; vm_compute; reflexivity)).
      intros R4 KEPT (b & Gb & _). pose proof (oregs_kept w R3 R4 OR3 KEPT) as OR4. keptQ KEPT G2 Qsp4. keptQ KEPT G8 Qs04. keptQ KEPT G3 Qgp4. keptQ KEPT G4 Qtp4.
      assert (GK4 : forall r', In r' [22; 23; 26; 27]%bv -> getr R4 r' = getr R2 r').
      { intros r' Hr'. rewrite (KEPT r') by (revert Hr'; clear; intros Hr'; apply in_reg_list; cbn in Hr'; decompose [or] Hr'; try contradiction; subst r'; reflexivity).
        revert Hr'. clear - GK3 Q26b G26. intros Hr'. cbn in Hr'. decompose [or] Hr'; try contradiction; subst r'; first [apply GK3; (first [solve [clear; cbn; tauto] | cbn; tauto]) | rewrite G26, Q26b; reflexivity]. }
      clear G1 G2 G3 G4 G8 G10 G26 KEPT OR3.
      pose proof FR1 as FR1'. destruct FR1' as (ext & tid & rid & _ & _ & _ & Ctid & _ & _ & _ & _). pose proof (proj1 Ctid) as Rtid. cbn in Rtid.

      assert (TAILE : forall Rx (vs : Z), oregs w Rx -> getr Rx 22%bv = Z_to_bv 64 (PrsGrammar.sx32 vs) -> 0 <= vs < 2 ^ 32 ->
                getr Rx 10%bv = Z_to_bv 64 (w_p w + O_M1) -> getr Rx 11%bv = Z_to_bv 64 (w_sp w + 260) ->
                getr Rx 1%bv = Z_to_bv 64 0x684c4 ->
                getr Rx 27%bv = Z_to_bv 64 3 -> getr Rx 23%bv = Z_to_bv 64 (i_io I) -> getr Rx 26%bv = Z_to_bv 64 (i_op I) ->
                srealizes SEGS (cfg fx Rx (ku_idx_u32 ccU1) M1 model) K).
      { intros Rx vs ORx X22 Rvs X10 X11 X1r X27 X23 X26.
        pose proof ORx as ORx'. destruct ORx' as (Ysp & Ygp & Ytp & Ys0 & _).
        pose proof Hn as Hn'. unfold PmLoopU1.nodes in Hn'.
        eapply (pm_index_m1 w c0 K fx A M1 model c Rx wv (w_sp w + 260) 0x684c4 PS FZ FC X1 Htr BUD MAC ltac:(pose proof (proj1 AACC eq_refl); lia)
                  ltac:(split; [exact X1r | split; [apply bv_eq; vm_compute; reflexivity | split; [lia | split; [exact Ysp | split; [exact Ygp | exact Ytp]]]]])
                  X10 X11 C260 ltac:(apply PmStepU1.mod16_4; [exact Gsp16 | reflexivity]) ltac:(lia) ltac:(unfold w_sp0, PM_FRAME; lia)).
        intros fx' A' R' M' model' p v m1' FZ' FC' X' BUD' MAC' LEN KEPT Hpr Hin Rv AG'.
        pose proof (oregs_kept w Rx R' ORx KEPT) as OR'. pose proof (x_ai X') as AI'. pose proof (x_ms X') as MS'.
        keptQ KEPT X22 Y22. keptQ KEPT X27 Y27. keptQ KEPT X23 Y23. keptQ KEPT X26 Y26. pose proof OR' as OR''. destruct OR'' as (Ysp' & Ygp' & Ytp' & Ys0' & Zs1 & Zs2 & Zs3 & Zs4 & Zs5 & Zs9).
        clear KEPT.

        pose proof (x_m1 X') as U'. cbn [set_m1 c_m1 t3a t3b t3c fst snd] in U'. destruct m1' as [[bl' bc'] ents']. cbn [t3a t3b t3c fst snd] in U', Hin, LEN.
        pose proof U' as U0. destruct U0 as [_ _ _ _ _ _ _ _ _ _ _ _ _ _ Unode' _].
        destruct (Unode' p wv v Hin) as (Hlive & Hq0 & Hq47 & Hqal & _).
        destruct (ai_live_block MI A' M' model' p 24 AI' Hlive) as (_ & _ & _ & Hpc & _).
        pose proof (live_mdef SEGS Ly.L MI A' M' model' p 24 AI' Hlive) as HDp.
        destruct (in_split _ _ Hin) as (l1 & l2 & Eents).

        pm_seed R' w c [Z_to_bv 64 p; Z_to_bv 64 (PrsGrammar.sx32 vs); Z_to_bv 64 (i_io I); Z_to_bv 64 (i_op I)].
        seedHR HR E ([(2%bv, EVar 32); (8%bv, EVar 33); (10%bv, EAlu ALU_ADD (EVar 39) (ELit 20)); (22%bv, EVar 40); (23%bv, EVar 41); (27%bv, ELit 3); (26%bv, EVar 42)] ++ OREGSEED)%list R'.
        seedHK HK w A' M' model' (set_m1 c (bl', bc', ents')) E X'.
        apply (know_more E M' [KWr (SA (EVar 39) 20) (ELit 4)]) in HK.
        2: { repeat apply Forall_cons; try apply Forall_nil. eapply kwr_mdef; [evs; reflexivity | eapply mdef_sub; [exact HDp | lia | lia] | lia | lia | lia | lia]. }
        xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
        postrun. name_run HRn R5.
        rreg HRn (23%bv) H23. rreg HRn (27%bv) H27. rreg HRn (26%bv) H26.
        assert (OR5 : oregs w R5) by (oregs_seeded HRn Ygp' Ytp'). clear HRn HR HK. fixregs.
        rewrite ?w_add by lia. rewrite PmInstU1.w2lb4_sx32 by lia.
        lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ => set (M3 := m) in * end.
        assert (ST3 : stores_in (zwin (p + 20) (p + 24)) M' M3) by (unfold M3; stin).
        pose proof (pm_m1_setval w A' M' model' (set_m1 c (bl', bc', ents')) l1 l2 p wv v vs X' ltac:(cbn; exact Eents) Rvs) as X3.
        cbn [set_m1 c_m1 c_m2 c_m3 c_v1 c_v2 c_v3 c_tr c_widx c_icount c_endian c_reqconv t3a t3b t3c fst snd] in X3. fold M3 in X3.
        assert (Elen : Zlen (l1 ++ (p, (wv, vs)) :: l2) = Zlen ents') by (rewrite Eents; unfold Zlen; rewrite !length_app; reflexivity).
        assert (AGf : CRep.agree_on (fun a => w_sp w <= a < w_sp w + 864) M' M3).
        { eapply stores_in_agree; [exact ST3 | intros b0 Hb0; unfold zwin; lia]. }
        assert (AG23 : CRep.agree_on (fun a => w_sp w <= a < w_sp w + 864) M1 M3).
        { intros a Ha. rewrite (AGf a Ha). apply AG'. unfold w_sp0, PM_FRAME. lia. }
        eapply (PK fx' FZ' FC' A' M3 model' _ R5 1 []).
        + split; [exact X3|]. split; [exact Htr|]. split.
          { clear - BUD' Elen Eents. unfold pm_bud in BUD' |- *. cbn [set_m1 c_m1 c_m2 c_m3 c_v1 c_v2 c_v3 c_tr t3a t3b t3c fst snd] in BUD' |- *.
            unfold HRep.Zlength in *. unfold Zlen in Elen. rewrite !Elen. exact BUD'. }
          split; [exact OR5|].
          split; [eapply (loop_mem_frame w M1 M3); [exact LM1 | lia | lia | eapply agree_on_weaken; [exact AG23 | unfold zwin; cbn; intros; lia]] |].
          split; [eapply (ictx_agree w M1 M3); [exact IC1 | lia | lia | eapply agree_on_weaken; [exact AG23 | unfold zwin; cbn; intros; lia]] |].
          split; [eapply (ifr_agree w M1 M3); [exact FR1 | lia | lia | eapply agree_on_weaken; [exact AG23 | unfold zwin; cbn; intros; lia]] |].
          cbn [c_icount c_endian c_v3 c_m1 c_m2 c_m3]. split; [exact Hic|]. split; [exact Hend|]. split; [exact Hwnz|]. split; [| exact V3R].
          clear - MAC' Elen Eents. unfold PmLoopU1.macct in MAC' |- *. cbn [set_m1 c_m1 c_m2 c_m3 t3a t3b t3c fst snd] in MAC' |- *. unfold Zlen in *. rewrite !Elen. exact MAC'.
        + exact H27. + exact H23. + exact H26.
        + eapply (cellw_frame M1 M3); [exact C718' | lia | cbn; lia | eapply agree_on_weaken; [exact AG23 | unfold zwin; cbn; intros; lia]].
        + left; lia.
        + reflexivity. + reflexivity. + reflexivity.
        + unfold PmLoopU1.nodes. cbn [set_m1 c_m1 c_m2 c_m3 t3c snd]. unfold Zlen in *. rewrite ?Elen. cbn [t3c snd] in LEN. lia.
        + cbn [set_m1 c_v3]. rewrite app_nil_r. reflexivity.
        + exact PmZw.seed_free_nil.
        + rewrite PmZw.Zlen_nil. lia.
        + left; reflexivity.
        + reflexivity.
        + right. split; [reflexivity|]. cbn [set_m1 c_m1 t3c snd]. unfold Zlen in *. rewrite ?Elen. cbn [t3c snd] in LEN. lia.
        + left; reflexivity.
        + intros []. }

      pose proof (proj1 C260) as Rwv2.
      assert (Q23d : getr R4 23%bv = Z_to_bv 64 (i_io I)) by (rewrite (GK4 23%bv) by (clear; cbn; tauto); exact Q23b).
      assert (Q27d : getr R4 27%bv = Z_to_bv 64 3) by (rewrite (GK4 27%bv) by (clear; cbn; tauto); exact Q27b).
      assert (Q26d : getr R4 26%bv = Z_to_bv 64 (i_op I)) by (rewrite (GK4 26%bv) by (clear; cbn; tauto); exact Q26b).
      assert (C88 : cellw SEGS M1 (w_sp w + 88) 8 (w_p w + 96)) by (eapply (loop_mem_cell w M1 88); [exact LM1 | (first [ solve [cbn [In]; repeat (first [left; reflexivity | right])] | cbn; repeat (first [left; reflexivity | right]) ]) | lia]).
      pose proof OR4 as OR'. destruct OR' as (_ & _ & _ & _ & Fs1 & Fs2 & Fs3 & Fs4 & Fs5 & Fs9).
      destruct b; cbn in Gb.
      +
        pm_seed R4 w c [Z_to_bv 64 wv; Z_to_bv 64 tid; Z_to_bv 64 (i_io I); Z_to_bv 64 (i_op I)].
        seedHR HR E ([(2%bv, EVar 32); (8%bv, EVar 33); (10%bv, ELit 1); (23%bv, EVar 41); (27%bv, ELit 3); (26%bv, EVar 42)] ++ OREGSEED)%list R4.
        seedHK HK w A M1 model c E X1.
        apply (know_more E M1 [KWord (SA (EVar 32) 260) (N.to_nat 4) (EVar 39); KWord (SA (EVar 32) 256) (N.to_nat 4) (EVar 40); KWord (SA (EVar 32) 88) (N.to_nat 8) (EAlu ALU_ADD (EVar 33) (ELit 96))]) in HK.
        2: { repeat apply Forall_cons; try apply Forall_nil.
             - eapply kword_var; [exact C260 | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
             - eapply kword_var; [exact Ctid | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
             - eapply kword_var; [exact C88 | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; rewrite w_add by lia; reflexivity]. }
        xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
        postrun. name_run HRn R5.
        rreg HRn (1%bv) G1. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (22%bv) G22b. rreg HRn (23%bv) G23. rreg HRn (27%bv) G27. rreg HRn (26%bv) G26.
        assert (OR5 : oregs w R5) by (oregs_seeded HRn Qgp4 Qtp4). clear HRn HR HK. fixregs.
        rewrite ?ext_val_sx4 in G22b by lia. rewrite ?w_add in G10, G11 by lia. change 435516 with (ku_idx_u32 ccU1).
        apply (TAILE R5 wv OR5 G22b ltac:(lia) ltac:(unfold O_M1; exact G10) G11 G1 G27 G23 G26).
      +
        pm_seed R4 w c [Z_to_bv 64 wv; Z_to_bv 64 tid; Z_to_bv 64 (i_io I); Z_to_bv 64 (i_op I)].
        seedHR HR E ([(2%bv, EVar 32); (8%bv, EVar 33); (10%bv, ELit 0); (23%bv, EVar 41); (27%bv, ELit 3); (26%bv, EVar 42)] ++ OREGSEED)%list R4.
        seedHK HK w A M1 model c E X1.
        apply (know_more E M1 [KWord (SA (EVar 32) 260) (N.to_nat 4) (EVar 39); KWord (SA (EVar 32) 256) (N.to_nat 4) (EVar 40); KWord (SA (EVar 32) 88) (N.to_nat 8) (EAlu ALU_ADD (EVar 33) (ELit 96))]) in HK.
        2: { repeat apply Forall_cons; try apply Forall_nil.
             - eapply kword_var; [exact C260 | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
             - eapply kword_var; [exact Ctid | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
             - eapply kword_var; [exact C88 | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; rewrite w_add by lia; reflexivity]. }
        xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
        postrun. name_run HRn R5.
        rreg HRn (1%bv) G1. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (22%bv) G22b. rreg HRn (23%bv) G23. rreg HRn (27%bv) G27. rreg HRn (26%bv) G26.
        assert (OR5 : oregs w R5) by (oregs_seeded HRn Qgp4 Qtp4). clear HRn HR HK. fixregs.
        rewrite ?ext_val_sx4 in G22b by lia. rewrite ?w_add in G10, G11 by lia. change 435516 with (ku_idx_u32 ccU1).
        apply (TAILE R5 tid OR5 G22b ltac:(lia) ltac:(unfold O_M1; exact G10) G11 G1 G27 G23 G26).
  Qed.
End PM.
End PmArm_RidU1.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmArm_TylU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmArm_StrU1.

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
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep2U1.PmUpdU1. From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PmStep2U1 PmStep3U1 PmLoopU1 PmInstU1 PmODefsU1 PmZw PmBody1U1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmBodyU1.PmBody2U1. From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PmExitDiagU1 PmStep5U1 PmOLoopU1 PmOLoop2U1. Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmOHeadU1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmOHeadU1.PmOLoop3U1. From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PmDispatchU1 PmOHeadU1 PmExitU1 PmHdrDiagU1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmBodyU1.PmHdrU1. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmBodyU1.PmArm_LitU1. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmBodyU1.PmArm_TyScDfU1. From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PmArm_EnumU1 PmArm_IdU1 PmArm_SpecU1 PmArm_ExtU1 PmArm_MaskU1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmBodyU1.PmArm_RidU1. From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PmArm_TylU1 PmArm_StrU1.
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
  Context {G : grammar} {idesc : Z -> Z -> Prop} {odesc edesc : Z -> Z -> Z -> Prop}
          {generates_type is_ext_inst is_nonsemantic : Z -> bool}
          {ds_rep : AS MI -> mem -> Z -> Z -> Z -> list (Z * Z) -> Prop}.
  Variable CL : pm_calleesU1 SEGS Ly.L MI ST G tcU1 dcU1 nfcU1 HConstsU1.hc ccU1 kcU1
                  idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep.

  #[local] Notation PMX := (PmBaseU1.PMX MI ST).
  #[local] Notation cfg fx R pc M model := (mkCfg (@mkst fx R (Z_to_bv 64 pc) M (seg_rom SEGS)) model).
  #[local] Notation GOK := (cu_G _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
  #[local] Notation loop_mem := (PmStepU1.loop_mem (MI:=MI) (ST:=ST)).
  #[local] Notation loop_regs := (PmStepU1.loop_regs (MI:=MI) (ST:=ST)).
  #[local] Notation izero := (PmInstU1.izero).
  #[local] Notation ictx := (PmInstU1.ictx).
  #[local] Notation ipure := (PmODefsU1.ipure (G:=G) (idesc:=idesc)).
  #[local] Notation arm_stmt := (PmODefsU1.arm_stmt (MI:=MI) (ST:=ST) (G:=G) (idesc:=idesc)).
  #[local] Notation arm_pc := (PmDispatchU1.arm_pc).
  #[local] Notation OLI := (PmODefsU1.OLI (MI:=MI) (ST:=ST) (generates_type:=generates_type)).
  #[local] Notation iacc := (PmODefsU1.iacc (generates_type:=generates_type)).
  #[local] Notation pm_B1 := (PmBody1U1.pm_B1 CL).
  #[local] Notation pm_B2 := (PmBody2U1.pm_B2 CL).
  #[local] Notation pm_D7 := (PmExitDiagU1.pm_D7 CL).
  #[local] Notation pm_oloop := (PmOHeadU1.pm_oloop CL).
  #[local] Notation pm_xexit := (PmExitU1.pm_xexit CL).
  #[local] Notation pm_main := (PmLoopU1.pm_main CL).
  #[local] Notation LOOPK := (PmExitU1.LOOPK (MI:=MI) (ST:=ST)).

  Lemma bfilter_app : forall (P : Z -> Prop) (H : forall x, base.Decision (P x)) (a b : list Z),
    base.filter P (a ++ b) = base.filter P a ++ base.filter P b.
  Proof using.
    intros P H a b. induction a as [|x a IH]; [rewrite bfilter_nil; reflexivity|]. cbn [app]. rewrite !bfilter_cons, IH.
    destruct (base.decide (P x)); reflexivity.
  Qed.
  Lemma push_types_nil_cons : forall z r, push_types (z :: r) [] = push_types r [] ++ (if negb (z =? OT_NONE) then [z] else []).
  Proof using.
    intros z r. unfold push_types. cbn [app rev]. rewrite bfilter_app, bfilter_cons, bfilter_nil.
    destruct (base.decide (Is_true (negb (z =? OT_NONE)))) as [Hd|Hd]; destruct (negb (z =? OT_NONE)) eqn:E; try reflexivity;
      exfalso; [exact Hd | apply Hd; exact Logic.I].
  Qed.
  Lemma push_types_nil_snoc : forall r z, push_types (r ++ [z]) [] = (if negb (z =? OT_NONE) then [z] else []) ++ push_types r [].
  Proof using.
    intros r z. unfold push_types. cbn [app]. rewrite rev_app_distr. cbn [rev app]. rewrite bfilter_cons.
    destruct (base.decide (Is_true (negb (z =? OT_NONE)))) as [Hd|Hd]; destruct (negb (z =? OT_NONE)) eqn:E; try reflexivity;
      exfalso; [exact Hd | apply Hd; exact Logic.I].
  Qed.

  Lemma zw_init : forall l, op_list_ok l -> zw_stack_ok (push_types l []).
  Proof using.
    intros l [SF H47]. destruct l as [|z r _] using rev_ind.
    - change (push_types [] []) with (@nil Z ++ @nil Z). apply zw_stack_ok_intro; [exact seed_free_nil | left; reflexivity].
    - rewrite removelast_last in SF. rewrite push_types_nil_snoc.
      destruct (push_types_split r []) as (top & Etop & _ & Hin). cbn [app] in Etop. rewrite Etop.
      assert (SFt : seed_free top) by (intros t Ht; exact (SF t (Hin t Ht))).
      destruct (negb (z =? OT_NONE)) eqn:Ez.
      + destruct (zw_seed z) eqn:Es.
        * change ([z] ++ top) with ([z] ++ top). apply zw_stack_ok_intro; [exact SFt|].
          unfold zw_seed, zw_type in Es. unfold_OT.
          pose proof (H47 z ltac:(apply in_app_iff; right; left; reflexivity)) as Hz47. unfold_OT.
          destruct (Z.eqb_spec z 9); [subst; right; left; reflexivity|].
          destruct (Z.eqb_spec z 47); [exfalso; exact (Hz47 ltac:(assumption))|].
          destruct (Z.eqb_spec z 54); [subst; right; right; right; left; reflexivity|].
          destruct (Z.eqb_spec z 8); [subst; right; right; left; reflexivity|].
          cbn in Es. discriminate.
        * change ([z] ++ top) with ([] ++ ([z] ++ top)). apply zw_stack_ok_intro; [| left; reflexivity].
          intros t [<-|Ht]; [exact Es | exact (SFt t Ht)].
      + cbn [app]. change top with ([] ++ top). apply zw_stack_ok_intro; [exact SFt | left; reflexivity].
  Qed.

  Lemma pm_body : forall (w : pmw MI ST) c0 K (fx : FPState),
    PMS w c0 K -> frm_zero (@fp_csr fx) -> fconsts fx -> (forall t, arm_stmt t (arm_pc t)) -> body_stmt w c0 K fx.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx PS FZ FC ARMS A M model c R HLI Hlt Qa1 Qa0 LK.
    pose proof HLI as HLI'. destruct HLI' as (X & Htr & BUD & LR & LM & Hw5 & He2 & HwN & ACC & MACC & LACC).
    pose proof (x_scal X) as (Sc1 & Sc2 & Sc3 & Sc4).
    eapply (pm_B1 w c0 K fx A M model c R PS FZ FC HLI Hlt Qa1 Qa0).
    intros A1 M1 model1 c1 R1 fw iwc op d X1 Htr1 BUD1 LR1 LM1 IZ1 IC1 Eiwc Eop Hiwc Rfw [l Hg] Hdesc Ewidx Eic Eend Erc Ev1 Ev2 Em1 Em2 Em3 Ev3 Ev1c.
    eapply (pm_B2 w c0 K fx A1 M1 model1 c1 R1 (c_widx c) fw iwc op d l PS X1 Htr1 BUD1 LR1 LM1 IZ1 IC1 Hg Hdesc).
    intros A2 M2 model2 R2 b' cap' X2 BUD2 LR2 LM2 IZ2 IC2.
    destruct (push_types_split l []) as (xs & Exs & Hxl & Hin). cbn [app] in Exs. rewrite Exs in X2, BUD2.
    set (I := ICTX (c_widx c) fw iwc op d l).
    set (c2 := set_v3 c1 (b', xs, cap')) in *.
    assert (IP : ipure I).
    { unfold PmODefsU1.ipure. cbn [I i_io i_fw i_iwc i_op i_d i_l]. repeat split; first [assumption | lia]. }
    pose proof (ipure_ranges I IP) as (Riwc & Rop). cbn [I i_iwc i_op] in Riwc, Rop.
    pose proof (go_op_zw G GOK op l Hg) as OLOK.
    pose proof (go_len_op G GOK op l Hg) as Hll. unfold HRep.Zlength in Hll. change (Zlen l <= g_maxlen G) in Hll.
    pose proof (cu_maxlen _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL) as Hml.
    assert (Hrange : Forall (fun x => 0 <= x < 2 ^ 31) l).
    { apply Forall_forall. intros x Hx. eapply (go_range G GOK l x); [left; exists op; exact Hg | exact Hx]. }
    assert (FRxs : Forall (fun x => 0 <= x < 2 ^ 31) xs).
    { apply Forall_forall. intros x Hx. exact (proj1 (Forall_forall _ _) Hrange x (Hin x Hx)). }
    pose proof (Zlen_nonneg xs) as Hxs0. pose proof (zw_next_range xs) as Hzn.
    assert (LK' : LOOPK w K (i_io I)) by (unfold PmExitU1.LOOPK; cbn [I i_io]; exact LK).
    apply (pm_oloop w c0 K I PS IP ARMS
             (fun fx3 A3 M3 model3 c3 R3 FZ3 FC3 HOLI Hle Q22 Q23 Q10 Q11 Q13 Q12 => pm_xexit w c0 K fx3 I A3 M3 model3 c3 R3 PS FZ3 FC3 IP HOLI Hle Q22 Q23 Q10 Q11 Q13 Q12 LK')
             (fun fx3 A3 M3 model3 c3 R3 FZ3 FC3 HOLI Hlt3 Hnil Q22 Q23 Q10 => pm_D7 w c0 K fx3 I A3 M3 model3 c3 R3 PS FZ3 IP HOLI Hlt3 Hnil Q22 Q23 Q10)
             fx A2 M2 model2 c2 R2 FZ FC).

    unfold PmODefsU1.OLI, OBASE, omeas, PmLoopU1.nodes, PmLoopU1.macct, PmLoopU1.lacc in *.
    cbn [I i_io i_fw i_iwc i_op i_d i_l c2 set_v3 c_widx c_icount c_endian c_reqconv c_tr c_m1 c_m2 c_m3 c_v1 c_v2 c_v3 t3a t3b t3c fst snd] in *.
    rewrite ?Ewidx, ?Eic, ?Eend, ?Erc, ?Ev1, ?Ev2, ?Em1, ?Em2, ?Em3 in *.
    split.
    { split; [exact X2|]. split; [exact Htr1|]. split; [exact BUD2|]. split; [exact (loop_regs_oregs w R2 LR2)|]. split; [exact LM2|].
      split; [exact IC2|]. split; [exact (izero_ifr w M2 IZ2)|]. split; [lia|]. split; [lia|]. split; [exact HwN|]. split; [exact MACC | exact FRxs]. }
    split; [lia|]. split; [lia|].
    split. { change (Zlen [fw]) with 1 in *. replace (c_widx c + iwc - (c_widx c + 1)) with (iwc - 1) by lia. rewrite Z.max_r by lia. lia. }
    split. { change (Zlen [fw]) with 1. lia. }
    split; [lia|].
    split; [rewrite <- Exs; exact (zw_init l OLOK)|].
    split.
    {   destruct (Z.eq_dec op OP_TYPE_INT) as [EI|NI]; [| destruct (Z.eq_dec op OP_TYPE_FLOAT) as [EF|NF]; [| exact (nty_other op xs _ NI NF)]].
      - rewrite EI in Hg |- *. rewrite (go_typeint G GOK l Hg) in Exs. rewrite <- Exs. apply nty_init_int. lia.
      - rewrite EF in Hg |- *. rewrite (go_typefloat G GOK l Hg) in Exs. rewrite <- Exs. apply nty_init_float. lia. }

    unfold PmODefsU1.iacc. cbn [I i_io i_op c2 set_v3 c_widx c_m1 c_m2 c_m3 c_v3 t3b t3c fst snd]. rewrite ?Em1, ?Em2, ?Em3, ?Ewidx.
    destruct LACC as (L1 & L2 & L3).
    split.
    { exists 0. split; [lia|]. split; [lia|]. split; [intros; lia|].
      pose proof (ridc_push_types_nil l) as RP1. rewrite Exs in RP1.
      pose proof (ridc_le1_of_count l ((proj1 (cu_rid1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL)) op l Hg)). lia. }
    split; [lia|].
    split.
    { exists 0. split; [lia|]. split; [lia|]. split; [intros _; reflexivity|].
      intros EI. left. split; [reflexivity|]. rewrite EI in Hg. rewrite (cu_import _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL) in Hg.
      injection Hg. intros <-. rewrite <- Exs. reflexivity. }
    intros Hgt. right. destruct ((cu_gt_rid _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL) op l Hgt Hg) as (r & ->).
    exists (push_types r []). rewrite <- Exs, push_types_nil_cons. reflexivity.
  Qed.

  Theorem parse_module_U1_of_arms : (forall t, arm_stmt t (arm_pc t)) -> parse_module_stmt SEGS Ly.L MI ST kcU1.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros ARMS. apply pm_main.
    - intros w c0 K fx PS FZ. exact (PmHdrDiagU1.pm_D1 CL w c0 K fx PS FZ).
    - intros w c0 K fx PS FZ. exact (PmHdrU1.pm_hdr CL w c0 K fx PS FZ).
    - intros w c0 K fx PS FZ FC. exact (pm_body w c0 K fx PS FZ FC ARMS).
  Qed.

  Lemma arms_all : forall t, arm_stmt t (arm_pc t).
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros t. pose proof (PmArm_RidU1.arm_RESULTID_U1 CL) as RID. pose proof (PmArm_StrU1.arm_LITSTR_U1 CL) as LS. unfold OT_LITERAL_STRING in LS.
    pose proof (PmArm_TylU1.arm_TYPEDLIT_U1 CL) as TL. unfold OT_TYPED_LITERAL_NUMBER, OT_OPTIONAL_TYPED_LITERAL_INTEGER in TL. unfold PmDispatchU1.arm_pc.
    destruct (Z.lt_ge_cases t 1) as [H0|H1].
    { replace ((1 <=? t) && (t <=? 107))%bool with false by (symmetry; apply Bool.andb_false_iff; left; apply Z.leb_gt; lia). apply (PmArm_TyScDfU1.arm_DEFAULT_U1 CL). }
    destruct (Z.lt_ge_cases 107 t) as [H2|H3].
    { replace ((1 <=? t) && (t <=? 107))%bool with false by (symmetry; apply Bool.andb_false_iff; right; apply Z.leb_gt; lia). apply (PmArm_TyScDfU1.arm_DEFAULT_U1 CL). }
    pose proof (PmDispatchU1.In_range_enum t 1 107 ltac:(lia)) as HIn. vm_compute in HIn.
    repeat match type of HIn with
           | _ \/ _ => destruct HIn as [HIn|HIn];
               [subst t; lazymatch goal with |- arm_stmt ?tt ?pc => let v := eval vm_compute in pc in change pc with v end;
                first [ exact RID | apply TL; lia | apply LS; lia
                      | apply (PmArm_IdU1.arm_ID_U1 CL); lia | apply PmArm_LitU1.arm_LITINT_U1; lia | apply PmArm_LitU1.arm_LITFLOAT_U1; reflexivity
                      | apply (PmArm_TyScDfU1.arm_TYPEID_U1 CL); reflexivity | apply (PmArm_TyScDfU1.arm_SCOPE_U1 CL); lia
                      | apply (PmArm_EnumU1.arm_SRCLANG_U1 CL); reflexivity | exact (PmArm_ExtU1.arm_EXTNUM_U1 CL) | exact (PmArm_SpecU1.arm_SPECOP_U1 CL)
                      | apply (PmArm_MaskU1.arm_MASK_U1 CL); (first [solve [clear; cbn; tauto] | cbn; tauto]) | apply (PmArm_EnumU1.arm_ENUM_U1 CL); apply PmArm_EnumU1.in_enum_types; reflexivity
                      | apply (PmArm_TyScDfU1.arm_DEFAULT_U1 CL) ] |]
           | False => destruct HIn
           end.
  Qed.

  Theorem parse_module_U1 : parse_module_stmt SEGS Ly.L MI ST kcU1.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL. exact (parse_module_U1_of_arms arms_all). Qed.
End PM.
