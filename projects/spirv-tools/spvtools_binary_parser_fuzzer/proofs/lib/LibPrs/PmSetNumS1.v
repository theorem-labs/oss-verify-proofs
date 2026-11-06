(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From stdpp Require list.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Plain.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PropExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SeqExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StepTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.WalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StartupTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SumWalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StoreOk OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MemSplit OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Hoare OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ShapeAlg OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SRealizes OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefReadLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.FPSteps OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibIface OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibBudget OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibEff OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MmapSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibMaskBits OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ZStores OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3Sound OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymRun3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.S1Layout.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.CRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.StrLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.LiveStats OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContStmts3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.S1Facts.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRepFacts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HCommon OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HConstsS1.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsNeeds OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsInv OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmBase OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmHyps OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmCoreS1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStepS1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep2S1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmLoopS1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmBody1S1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep3S1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmODefsS1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmZw OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep4S1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep5S1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmDispatchS1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmArm_RidS1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmArm_StrLibS1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Module S1_code_69b20_69b24.

Import Stdlib.ZArith.ZArith.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_69b20 : bv 32 := 0x00008067.
Lemma F_69b20 : fetch_word Plain.M.loaded_segments (0x69b60 : word) = Some W_69b20.
Proof. vm_refl. Qed.
Lemma D_69b20 : decode_any W_69b20 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
End S1_code_69b20_69b24.

Module S1_code_69b5c_69b60.

Import Stdlib.ZArith.ZArith.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_69b5c : bv 32 := 0x00008067.
Lemma F_69b5c : fetch_word Plain.M.loaded_segments (0x69b9c : word) = Some W_69b5c.
Proof. vm_refl. Qed.
Lemma D_69b5c : decode_any W_69b5c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
End S1_code_69b5c_69b60.

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
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContLib StrLib LiveStats ContStmts ContStmts3 S1Facts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts HCommon HLib HConstsS1.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsNeeds PrsInv PrsStmts PmBase PmHyps PmCoreS1 PmStepS1. Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep2S1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep2S1.PmUpd. From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PmStep2S1 PmLoopS1 PmBody1S1 PmStep3S1 PmODefsS1 PmZw PmStep4S1 PmStep5S1 PmDispatchS1 PmArm_RidS1 PmArm_StrLibS1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmSetNumS1.S1_code_69b20_69b24. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmSetNumS1.S1_code_69b5c_69b60.
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
  #[local] Notation pm_v3_pb := (PmStep4S1.pm_v3_pb CL).
  #[local] Notation pm_oty_pb := (PmStep4S1.pm_oty_pb CL).
  #[local] Notation pm_find_m1 := (PmStep4S1.pm_find_m1 CL).
  #[local] Notation pm_find_m3 := (PmStep4S1.pm_find_m3 CL).
  #[local] Notation pm_spec_lookup := (PmStep4S1.pm_spec_lookup CL).
  #[local] Notation pm_h5 := (PmStep5S1.pm_h5 CL).
  #[local] Notation pmx_room_ms := (PmArm_StrLibS1.pmx_room_ms CL).
  #[local] Notation pm_makestring := (PmArm_StrLibS1.pm_makestring CL).
  #[local] Notation pm_del_tr := (PmArm_StrLibS1.pm_del_tr CL).
  #[local] Notation pm_import := (PmArm_StrLibS1.pm_import CL).
  #[local] Notation pm_put_string := (PmArm_StrLibS1.pm_put_string CL).
  #[local] Notation pm_emplace_m3 := (PmArm_StrLibS1.pm_emplace_m3 CL).
  #[local] Notation ls_pdiag0x := (PmArm_StrLibS1.ls_pdiag0x CL).
  #[local] Notation ls_put_cstrx := (PmArm_StrLibS1.ls_put_cstrx CL).
  #[local] Notation ls_sdtor := (PmArm_StrLibS1.ls_sdtor CL).
  #[local] Notation ls_etail := (PmArm_StrLibS1.ls_etail CL).
  #[local] Notation ls_exh := (PmArm_StrLibS1.ls_exh CL).
  #[local] Notation ls_toolong := (PmArm_StrLibS1.ls_toolong CL).
  #[local] Notation ls_badimport := (PmArm_StrLibS1.ls_badimport CL).

  Ltac fixregs2 := fixregs;
    try replace (Z_to_bv 5 (Z.of_N 10)) with (10%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 11)) with (11%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 12)) with (12%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 13)) with (13%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 18)) with (18%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 21)) with (21%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 22)) with (22%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 23)) with (23%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 25)) with (25%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 26)) with (26%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 27)) with (27%bv : reg) in * by (apply bv_eq; reflexivity).

  Ltac fixregs3 := fixregs2;
    try replace (Z_to_bv 5 (Z.of_N 1)) with (1%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 2)) with (2%bv : reg) in * by (apply bv_eq; reflexivity).

  Definition cregs_at (w : pmw MI ST) (d : Z) (R : bvmap 5 word) (ret : Z) : Prop :=
    getr R 1%bv = Z_to_bv 64 ret /\ ret_ok (Z_to_bv 64 ret) /\ 0 <= ret < 2 ^ 64 /\
    getr R 2%bv = Z_to_bv 64 (w_sp w - d) /\ getr R 3%bv = Z_to_bv 64 (ly_gp Ly.L) /\ getr R 4%bv = Z_to_bv 64 (ly_tp Ly.L).

  Lemma mod16_sub : forall x d, x mod 16 = 0 -> d mod 16 = 0 -> (x - d) mod 16 = 0.
  Proof using. intros x d Hx Hd. rewrite Zminus_mod, Hx, Hd. reflexivity. Qed.

  Lemma pmx_callB_at : forall (w : pmw MI ST) A M model c R (d ret S : Z),
    PMX w A M model c -> cregs_at w d R ret -> 0 <= d -> d mod 16 = 0 -> 0 <= S -> d + S <= w_STK w - PM_FRAME ->
    callB MI ST A (w_s w) R M model (w_sp w - d) ret S.
  Proof using AC MI ST.
    intros w A M model c R d ret S X (C1 & C2 & C3 & C4 & C5 & C6) Hd Hd16 HS HdS. pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & _). unfold w_sp0, PM_FRAME in *.
    constructor.
    - exact (x_ai X). - exact (x_ms X). - exact (pmx_img_ro_clear w X). - exact (x_sx X). - exact (x_sxh X).
    - constructor; try assumption; [apply mod16_sub; assumption | lia].
    - lia.
    - unfold stack_room. pose proof (x_wdef X) as WD. unfold w_sp0, PM_FRAME in WD.
      replace (w_sp w - d - S) with ((w_sp w + 880 - w_STK w) + (w_STK w - 880 - d - S)) by lia.
      apply (mdef_store_ok_off SEGS M _ (w_STK w)); [exact WD | lia | lia | lia | rewrite Z2Nat.id by lia; lia].
    - intros a Ha. split.
      + apply (x_wown X). unfold w_sp0, PM_FRAME, zwin in *. lia.
      + apply (x_win_sx X). unfold w_sp0, PM_FRAME, zwin in *. lia.
    - exact (x_own_sx X).
    - exact (x_err_sx X).
  Qed.

  Lemma pmx_low_stores : forall (w : pmw MI ST) A M M' model c (W : Z -> Prop),
    PMX w A M model c -> stores_in W M M' ->
    (forall a, W a -> w_sp0 w - w_STK w <= a < w_sp0 w - 104) ->
    PMX w A M' model c.
  Proof using AC MI ST.
    intros w A M M' model c W X SI HW. pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & _). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof (x_scal X) as (S1 & S2 & S3 & S4).
    rewrite <- (set_scal_id c).
    eapply (pmx_stores SEGS Ly.L MI ST ly_img_low ly_rw_img ly_relro_img); [exact X | exact SI | | | | | | lia | lia | lia | exact S4].
    - intros a Ha. left. unfold w_sp0, PM_FRAME. pose proof (HW a Ha). lia.
    - eapply fld_keep; [exact SI | exact (x_widx X) | unfold O_WIDX; lia | unfold O_WIDX; cbn; lia | unfold O_WIDX, zwin; cbn; intros a Ha Hx; pose proof (HW _ Hx); lia].
    - eapply fld_keep; [exact SI | exact (x_icount X) | unfold O_ICOUNT; lia | unfold O_ICOUNT; cbn; lia | unfold O_ICOUNT, zwin; cbn; intros a Ha Hx; pose proof (HW _ Hx); lia].
    - eapply fld_keep; [exact SI | exact (x_endian X) | unfold O_ENDIAN; lia | unfold O_ENDIAN; cbn; lia | unfold O_ENDIAN, zwin; cbn; intros a Ha Hx; pose proof (HW _ Hx); lia].
    - eapply fld_keep; [exact SI | exact (x_flags X) | unfold O_FLAGS; lia | unfold O_FLAGS; cbn; lia | unfold O_FLAGS, zwin; cbn; intros a Ha Hx; pose proof (HW _ Hx); lia].
  Qed.

  #[local] Notation pmx_dsS := (pmx_ds SEGS Ly.L MI ST ly_img_low ly_rw_img ly_relro_img ly_errno_img ly_rw_not_relro ly_errno_rw).
  #[local] Notation blksP B := (fun a => exists q k, In (q, k) B /\ q <= a < q + k).

  Lemma pmx_dsx : forall (w : pmw MI ST) A M model c A' M' model' (d S ds : Z) (B B' rest : list (Z * Z)) (J : Z -> Prop),
    PMX w A M model c -> c_tr c = B ++ rest ->
    ainv MI A' M' model' -> mstd model' -> m_fs model' = m_fs model -> m_fds model' = m_fds model ->
    eff MI A A' M M' (w_sp w - d - S, w_sp w - d) (fun a => ds_foot ds B a \/ ds_foot ds B' a \/ J a \/ False) ->
    0 <= d -> 0 <= S -> d + S <= w_STK w - PM_FRAME ->
    w_sp w - d <= ds -> ds + DS_SIZE <= w_sp w ->
    junk_ok MI A J -> mdef M' ds DS_SIZE ->
    (forall q k, In (q, k) B -> In (q, k) (live MI A)) -> (forall q k, In (q, k) B' -> In (q, k) (live MI A')) ->
    blk_xfer B B' (live MI A) (live MI A') -> Zlength B <= 1 -> Zlength B' <= 1 ->
    PMX w A' M' model' (set_tr c (B' ++ rest))
    /\ CRep.agree_on (fun a => w_sp w - d <= a < w_sp0 w /\ ~ zwin ds (ds + DS_SIZE) a) M M'.
  Proof using AC MI ST.
    intros w A M model c A' M' model' d S ds B B' rest J X Htr AI' MS' FS' FDS' EF Hd HS HdS Hds0 Hds1 HJ Hdef HBl HB'l XFER HB HB'.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ai X) as AI.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & Gc2 & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, DS_SIZE in *.
    assert (HI : forall x, alloc_ceiling <= x -> ~ in_ranges (ly_img Ly.L) x) by (intros x Hx Hi; pose proof (ly_img_low _ Hi); lia).
    assert (LOWB : forall q k a, In (q, k) (live MI A) -> q <= a < q + k -> a < alloc_ceiling).
    { intros q k a Hq Ha. destruct (ai_live_block MI A M model q k AI Hq) as (_ & _ & _ & Hqc & _). lia. }
    assert (LOWB' : forall q k a, In (q, k) (live MI A') -> q <= a < q + k -> a < alloc_ceiling).
    { intros q k a Hq Ha. destruct (ai_live_block MI A' M' model' q k AI' Hq) as (_ & _ & _ & Hqc & _). lia. }

    assert (EF1 : eff MI A A' M M' (w_sp w - d - S, w_sp w - d) (fun a => (blksP B a \/ blksP B' a \/ J a) \/ zwin ds (ds + 392) a)).
    { eapply eff_weaken; [exact EF|]. unfold ds_foot, DS_SIZE. intros a [[H|H]|[[H|H]|[H|[]]]]; tauto. }
    assert (EF2 : eff MI A A' M M' (w_sp w - (d + S), w_sp w) (fun a => (blksP B a \/ blksP B' a \/ J a) \/ zwin ds (ds + 392) a)).
    { eapply eff_widen; [exact EF1 | cbn; lia | cbn; lia]. }
    assert (EF3 : eff MI A A' M M' (w_sp w - (d + S), w_sp w) (fun a => blksP B a \/ blksP B' a \/ J a)).
    { eapply (eff_drop SEGS Ly.L MI ly_img_low ly_rw_img A A' M M' model'); [exact EF2 | exact AI' | |].
      - intros a Ha. unfold zwin, W_of in *. cbn. lia.
      - intros a Ha _. unfold zwin in Ha. pose proof (Hdef (a - ds) ltac:(lia)) as D. replace (ds + (a - ds)) with a in D by lia. exact D. }

    assert (EF4 : eff MI A A' M M' (w_sp w - (d + S), w_sp w) (fun a => ds_foot (w_sp w) B a \/ ds_foot (w_sp w) B' a \/ J a \/ False)).
    { eapply eff_weaken; [exact EF3|]. unfold ds_foot. intros a [H|[H|H]]; tauto. }
    assert (Hfdef : mdef M' (w_sp w) 392).
    { eapply (mdef_via_eff SEGS Ly.L MI ly_img_low ly_rw_img ly_errno_rw); [exact EF3 | left; lia | lia | lia | | |].
      - intros i Hi. eapply (hi_unowned MI ly_img_low ly_rw_img); [exact AI | lia].
      - intros i Hi [(q & k & Hq & Hqa)|[(q & k & Hq & Hqa)|Hj]].
        + pose proof (LOWB q k _ (HBl q k Hq) Hqa). lia.
        + pose proof (LOWB' q k _ (HB'l q k Hq) Hqa). lia.
        + pose proof (proj1 (HJ _ Hj)). lia.
      - intros i Hi. pose proof (x_wdef X (w_sp w + i - (w_sp w + 880 - w_STK w)) ltac:(unfold w_sp0, PM_FRAME; lia)) as D. unfold w_sp0, PM_FRAME in D.
        replace (w_sp w + 880 - w_STK w + (w_sp w + i - (w_sp w + 880 - w_STK w))) with (w_sp w + i) in D by lia. exact D. }
    split.
    - eapply (pmx_dsS w A M model c A' M' model' (d + S) (w_sp w) B B' rest J (fun _ => False));
        [exact X | exact Htr | exact AI' | exact MS' | exact FS' | exact FDS' | exact EF4 | unfold PM_FRAME; lia | lia | unfold DS_SIZE, w_sp0, PM_FRAME; lia
        | exact HJ | intros a [] | unfold DS_SIZE; exact Hfdef | exact XFER | exact HB | exact HB'].
    - eapply (agree_via_eff SEGS Ly.L MI); [exact EF|]. intros a [Ha Hno].
      split; [lia|]. split; [eapply (hi_unowned MI ly_img_low ly_rw_img); [exact AI | lia]|].
      split; [eapply (hi_unowned MI ly_img_low ly_rw_img); [exact AI' | lia]|].
      split; [pose proof (x_wdef X (a - (w_sp w + 880 - w_STK w)) ltac:(unfold w_sp0, PM_FRAME; lia)) as D; unfold w_sp0, PM_FRAME in D;
             replace (w_sp w + 880 - w_STK w + (a - (w_sp w + 880 - w_STK w))) with a in D by lia; exact D |].
      split.
      + unfold ds_foot, DS_SIZE. intros [[H|(q & k & Hq & Hqa)]|[[H|(q & k & Hq & Hqa)]|[Hj|[]]]].
        * exact (Hno H). * pose proof (LOWB q k a (HBl q k Hq) Hqa). lia.
        * exact (Hno H). * pose proof (LOWB' q k a (HB'l q k Hq) Hqa). lia.
        * pose proof (proj1 (HJ a Hj)). lia.
      + split; [unfold W_of; cbn; lia | intros He; exact (HI a ltac:(lia) (ly_errno_img a He))].
  Qed.

  Definition dframe_ok (w : pmw MI ST) (d : Z) : Prop :=
    DS_SIZE <= d /\ d mod 16 = 0 /\ d + dc_stack dcS1 <= w_STK w - PM_FRAME.

  Lemma pm_dsx_step : forall (w : pmw MI ST) c0 K A M model c A' R R' M' model' (d : Z) B B' rest (J : Z -> Prop),
    PMS w c0 K -> PMX w A M model c -> c_tr c = B ++ rest -> pm_bud (w_n w) c -> Zlength rest <= 1 -> dframe_ok w d ->
    Zlength B <= 1 -> (forall q k, In (q, k) B -> In (q, k) (live MI A)) ->
    retB MI ST A' (w_s w) R R' M' model model' ->
    Zlength B' <= 1 -> (forall q k, In (q, k) B' -> In (q, k) (live MI A') /\ 0 < k <= DS_MAXBLK) ->
    mdef M' (w_sp w - d) DS_SIZE ->
    blk_xfer B B' (live MI A) (live MI A') -> junk_ok MI A J ->
    eff MI A A' M M' (w_sp w - d - dc_stack dcS1, w_sp w - d) (fun a => ds_foot (w_sp w - d) B a \/ ds_foot (w_sp w - d) B' a \/ J a \/ False) ->
    PMX w A' M' model' (set_tr c (B' ++ rest)) /\ pm_bud (w_n w) (set_tr c (B' ++ rest))
    /\ CRep.agree_on (fun a => w_sp w - d + DS_SIZE <= a < w_sp0 w) M M'.
  Proof using AC MI ST.
    intros w c0 K A M model c A' R R' M' model' d B B' rest J PS X Htr BUD Hrest (HD1 & HD2 & HD3) HB HBl RB HB' HB'l Hdef XFER HJ EF.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & _).
    destruct RB as [AI' MS' FS' FDS' SX' KEPT]. cbn [dc_stack dcS1] in *.
    destruct (pmx_dsx w A M model c A' M' model' d 12288 (w_sp w - d) B B' rest J X Htr AI' MS' FS' FDS' EF ltac:(unfold DS_SIZE in HD1; lia) ltac:(lia)
                ltac:(unfold PM_FRAME in *; lia) ltac:(lia) ltac:(lia) HJ Hdef HBl ltac:(intros q k Hq; exact (proj1 (HB'l q k Hq))) XFER HB HB') as [X' AG].
    split; [exact X'|]. split.
    - destruct BUD as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9). repeat (split; [assumption|]). cbn [set_tr c_tr].
      rewrite Htr in B8, B9. unfold Zlength in *. rewrite length_app in *. rewrite Nat2Z.inj_add in *. split; [lia|].
      intros b Hb. apply in_app_iff in Hb. destruct Hb as [Hb|Hb].
      + destruct b as [q k]. destruct (HB'l q k Hb). unfold DS_MAXBLK in *. cbn. lia.
      + apply B9. apply in_app_iff. right. exact Hb.
    - eapply agree_on_weaken; [exact AG|]. intros a Ha. cbn beta in *. unfold zwin, DS_SIZE, w_sp0 in *. lia.
  Qed.

  Lemma mod16_mod8 : forall y, y mod 16 = 0 -> y mod 8 = 0.
  Proof using.
    intros y Hy. rewrite (Z_div_mod_eq_full y 16). rewrite Hy, Z.add_0_r.
    replace (16 * (y / 16)) with ((2 * (y / 16)) * 8) by lia. apply Z_mod_mult.
  Qed.

  Lemma pm_ctor_at : forall (w : pmw MI ST) c0 K (fx : FPState) A M model c R (d err ppos pstr1 pstr2 ret : Z) (rest : list (Z * Z)),
    PMS w c0 K -> PMX w A M model c -> c_tr c = rest -> pm_bud (w_n w) c -> Zlength rest <= 1 -> dframe_ok w d ->
    cregs_at w d R ret ->
    getr R 10%bv = Z_to_bv 64 (w_sp w - d) -> getr R 11%bv = Z_to_bv 64 ppos -> getr R 12%bv = Z_to_bv 64 (w_cons w) ->
    getr R 13%bv = Z_to_bv 64 pstr1 -> getr R 14%bv = Z_to_bv 64 (err mod 2 ^ 64) -> getr R 15%bv = Z_to_bv 64 pstr2 ->
    - 2 ^ 31 <= err < 0 ->
    w_sp w - d + DS_SIZE <= ppos -> ppos + 24 <= w_sp w -> w_sp w - d + DS_SIZE <= pstr1 -> pstr1 + 24 <= w_sp w -> w_sp w - d + DS_SIZE <= pstr2 -> pstr2 + 24 <= w_sp w ->
    fld SEGS M pstr1 2 0 -> fld SEGS M pstr2 2 0 ->
    (forall A' R' M' model' B',
        PMX w A' M' model' (set_tr c (B' ++ rest)) -> pm_bud (w_n w) (set_tr c (B' ++ rest)) ->
        kept R R' -> ds_rep A' M' (w_sp w - d) err 0 B' ->
        CRep.agree_on (fun a => w_sp w - d + DS_SIZE <= a < w_sp0 w) M M' ->
        srealizes SEGS (cfg fx R' ret M' model') K) ->
    srealizes SEGS (cfg fx R (dc_ctor dcS1) M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx A M model c R d err ppos pstr1 pstr2 ret rest PS X Htr BUD Hrest HDF CR Ha0 Ha1 Ha2 Ha3 Ha4 Ha5 Herr T1 T1' T2 T2' T3 T3' F1 F2 CONT.
    pose proof HDF as (HD1 & HD2 & HD3). cbn [dc_stack dcS1] in HD3.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ai X) as AI.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & Gc2 & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, DS_SIZE in *.
    assert (WD : forall t n, w_sp w + 880 - w_STK w <= t -> t + n <= w_sp w + 880 -> mdef M t n).
    { intros t n Ht Hn i Hi. pose proof (x_wdef X (t + i - (w_sp w + 880 - w_STK w)) ltac:(unfold w_sp0, PM_FRAME; lia)) as D.
      unfold w_sp0, PM_FRAME in D. replace (w_sp w + 880 - w_STK w + (t + i - (w_sp w + 880 - w_STK w))) with (t + i) in D by lia. exact D. }
    assert (ASP : forall a n, w_sp w - d <= a -> a + n <= w_sp w + 880 -> above_sp MI A (w_sp w - d) a n).
    { intros a n Ha Hn. split; [lia|]. split; [lia|]. intros i Hi. eapply (hi_unowned MI ly_img_low ly_rw_img); [exact AI | lia]. }
    eapply (cl_ds_ctor _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL fx A (w_s w) R M model (w_sp w - d) ret (w_sp w - d) ppos (w_cons w) pstr1 err pstr2 K).
    - eapply pmx_callB_at; [exact X | exact CR | lia | exact HD2 | cbn [dc_stack dcS1]; lia | cbn [dc_stack dcS1]; unfold PM_FRAME; lia].
    - exact (x_roc X).
    - exact Ha0. - exact Ha1. - exact Ha2. - exact Ha3. - exact Ha4. - exact Ha5. - exact Herr.
    - apply ASP; unfold DS_SIZE; lia.
    - apply mod16_mod8. apply mod16_sub; [exact Gsp16 | exact HD2].
    - apply WD; unfold DS_SIZE; lia.
    - apply ASP; lia.
    - apply WD; lia.
    - apply ASP; lia.
    - exact F1.
    - apply WD; lia.
    - apply ASP; lia.
    - exact F2.
    - apply WD; lia.
    - split; [left; lia | intros a Ha; cbn [dc_stack dcS1] in Ha; unfold zwin in *; lia].
    - lia.
    - exact (x_consf X).
    - intros a Ha. unfold zwin, DS_SIZE in *. repeat split; lia.
    - eapply pmx_ds_room; [exact PS | exact X | exact BUD].
    - intros A' R' M' model' B' RB DS' XFER EF.
      pose proof (dl_blocks _ _ _ _ _ _ DL _ _ _ _ _ _ DS') as [HB'len HB'in].
      pose proof (dl_def _ _ _ _ _ _ DL _ _ _ _ _ _ DS') as (Hdef' & _).
      destruct (pm_dsx_step w c0 K A M model c A' R R' M' model' d [] B' rest (fun _ => False) PS X Htr BUD Hrest HDF
                 ltac:(rewrite Zlength_nil; lia) ltac:(intros q k [])
                 RB HB'len HB'in Hdef' XFER ltac:(intros a [])
                 ltac:(eapply eff_weaken; [exact EF | intros a Ha; right; left; exact Ha]))
        as (X' & BUD' & AG).
      eapply CONT; [exact X' | exact BUD' | exact (rb_kept _ _ _ _ _ _ _ _ _ _ _ RB) | exact DS' | exact AG].
  Qed.

  Lemma pm_put_cstr_at : forall (w : pmw MI ST) c0 K (fx : FPState) A M model c R (d err len p n m ret : Z) (B rest : list (Z * Z)),
    PMS w c0 K -> PMX w A M model c -> c_tr c = B ++ rest -> pm_bud (w_n w) c -> Zlength rest <= 1 -> dframe_ok w d ->
    ds_rep A M (w_sp w - d) err len B ->
    cregs_at w d R ret ->
    getr R 10%bv = Z_to_bv 64 (w_sp w - d) -> getr R 11%bv = Z_to_bv 64 p -> getr R 12%bv = Z_to_bv 64 m ->
    ro_cstr SEGS Ly.L p n -> 0 <= m <= n -> len + m <= DS_MAXLEN ->
    (forall A' R' M' model' B',
        PMX w A' M' model' (set_tr c (B' ++ rest)) -> pm_bud (w_n w) (set_tr c (B' ++ rest)) ->
        kept R R' -> getr R' 10%bv = Z_to_bv 64 (w_sp w - d) ->
        ds_rep A' M' (w_sp w - d) err (len + m) B' ->
        CRep.agree_on (fun a => w_sp w - d + DS_SIZE <= a < w_sp0 w) M M' ->
        srealizes SEGS (cfg fx R' ret M' model') K) ->
    srealizes SEGS (cfg fx R (dc_put_cstr dcS1) M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx A M model c R d err len p n m ret B rest PS X Htr BUD Hrest HDF DS CR Ha0 Ha1 Ha2 RO Hm Hlen CONT.
    pose proof HDF as (HD1 & HD2 & HD3). cbn [dc_stack dcS1] in HD3.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ai X) as AI. destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & _). unfold w_sp0, PM_FRAME, DS_SIZE in *.
    pose proof (dl_blocks _ _ _ _ _ _ DL _ _ _ _ _ _ DS) as [HBlen HBin].
    eapply (cl_put_cstr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL fx A (w_s w) R M model (w_sp w - d) ret (w_sp w - d) err len p n m B K).
    - eapply pmx_callB_at; [exact X | exact CR | lia | exact HD2 | cbn [dc_stack dcS1]; lia | cbn [dc_stack dcS1]; unfold PM_FRAME; lia].
    - exact (x_roc X).
    - exact Ha0. - exact Ha1. - exact Ha2. - exact DS.
    - split; [lia|]. split; [unfold DS_SIZE; lia|]. intros i Hi. eapply (hi_unowned MI ly_img_low ly_rw_img); [exact AI | lia].
    - exact RO. - exact Hm. - exact Hlen.
    - eapply pmx_ds_room; [exact PS | exact X | exact BUD].
    - intros A' R' M' model' B' J RB Hres DS' XFER HJ EF.
      pose proof (dl_blocks _ _ _ _ _ _ DL _ _ _ _ _ _ DS') as [HB'len HB'in].
      pose proof (dl_def _ _ _ _ _ _ DL _ _ _ _ _ _ DS') as (Hdef' & _).
      destruct (pm_dsx_step w c0 K A M model c A' R R' M' model' d B B' rest J PS X Htr BUD Hrest HDF HBlen
                 ltac:(intros q k Hq; exact (proj1 (HBin q k Hq))) RB HB'len HB'in Hdef' XFER HJ
                 ltac:(eapply eff_weaken; [exact EF | intros a [Ha|[Ha|[Ha|[]]]]; [left | right; left | right; right; left]; exact Ha]))
        as (X' & BUD' & AG).
      eapply CONT; [exact X' | exact BUD' | exact (rb_kept _ _ _ _ _ _ _ _ _ _ _ RB) | exact (Hres eq_refl) | exact DS' | exact AG].
  Qed.

  Lemma pm_put_num_at : forall (pc lo hi : Z) (enc : Z -> Z),
    put_num_stmt SEGS Ly.L MI ST dcS1 ds_rep pc lo hi enc ->
    forall (w : pmw MI ST) c0 K (fx : FPState) A M model c R (d err len x ret : Z) (B rest : list (Z * Z)),
    PMS w c0 K -> PMX w A M model c -> c_tr c = B ++ rest -> pm_bud (w_n w) c -> Zlength rest <= 1 -> dframe_ok w d ->
    ds_rep A M (w_sp w - d) err len B ->
    cregs_at w d R ret ->
    getr R 10%bv = Z_to_bv 64 (w_sp w - d) -> getr R 11%bv = Z_to_bv 64 (enc x) -> lo <= x < hi -> len + 24 <= DS_MAXLEN ->
    (forall A' R' M' model' B',
        PMX w A' M' model' (set_tr c (B' ++ rest)) -> pm_bud (w_n w) (set_tr c (B' ++ rest)) ->
        kept R R' -> getr R' 10%bv = Z_to_bv 64 (w_sp w - d) ->
        ds_rep A' M' (w_sp w - d) err (len + 24) B' ->
        CRep.agree_on (fun a => w_sp w - d + DS_SIZE <= a < w_sp0 w) M M' ->
        srealizes SEGS (cfg fx R' ret M' model') K) ->
    srealizes SEGS (cfg fx R pc M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros pc lo hi enc STMT w c0 K fx A M model c R d err len x ret B rest PS X Htr BUD Hrest HDF DS CR Ha0 Ha1 Hx Hlen CONT.
    pose proof HDF as (HD1 & HD2 & HD3). cbn [dc_stack dcS1] in HD3.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ai X) as AI. destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & _). unfold w_sp0, PM_FRAME, DS_SIZE in *.
    pose proof (dl_blocks _ _ _ _ _ _ DL _ _ _ _ _ _ DS) as [HBlen HBin].
    eapply (STMT fx A (w_s w) R M model (w_sp w - d) ret (w_sp w - d) err len x B K).
    - eapply pmx_callB_at; [exact X | exact CR | lia | exact HD2 | cbn [dc_stack dcS1]; lia | cbn [dc_stack dcS1]; unfold PM_FRAME; lia].
    - exact (x_roc X).
    - exact Ha0. - exact Ha1. - exact Hx. - exact DS.
    - split; [lia|]. split; [unfold DS_SIZE; lia|]. intros i Hi. eapply (hi_unowned MI ly_img_low ly_rw_img); [exact AI | lia].
    - exact Hlen.
    - eapply pmx_ds_room; [exact PS | exact X | exact BUD].
    - intros A' R' M' model' B' J RB Hres DS' XFER HJ EF.
      pose proof (dl_blocks _ _ _ _ _ _ DL _ _ _ _ _ _ DS') as [HB'len HB'in].
      pose proof (dl_def _ _ _ _ _ _ DL _ _ _ _ _ _ DS') as (Hdef' & _).
      destruct (pm_dsx_step w c0 K A M model c A' R R' M' model' d B B' rest J PS X Htr BUD Hrest HDF HBlen
                 ltac:(intros q k Hq; exact (proj1 (HBin q k Hq))) RB HB'len HB'in Hdef' XFER HJ
                 ltac:(eapply eff_weaken; [exact EF | intros a [Ha|[Ha|[Ha|[]]]]; [left | right; left | right; right; left]; exact Ha]))
        as (X' & BUD' & AG).
      eapply CONT; [exact X' | exact BUD' | exact (rb_kept _ _ _ _ _ _ _ _ _ _ _ RB) | exact (Hres eq_refl) | exact DS' | exact AG].
  Qed.
  Definition pm_put_u32_at := pm_put_num_at _ _ _ _ (cl_put_u32 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).

  Lemma pm_dtor_at : forall (w : pmw MI ST) c0 K (fx : FPState) A M model c R (d err len ret : Z) (B rest : list (Z * Z)),
    PMS w c0 K -> PMX w A M model c -> c_tr c = B ++ rest -> pm_bud (w_n w) c -> Zlength rest <= 1 -> dframe_ok w d ->
    ds_rep A M (w_sp w - d) err len B ->
    cregs_at w d R ret -> getr R 10%bv = Z_to_bv 64 (w_sp w - d) ->
    (forall A' R' M' model',
        PMX w A' M' model' (set_tr c rest) -> pm_bud (w_n w) (set_tr c rest) ->
        kept R R' ->
        CRep.agree_on (fun a => w_sp w - d + DS_SIZE <= a < w_sp0 w) M M' ->
        srealizes SEGS (cfg fx R' ret M' model') K) ->
    srealizes SEGS (cfg fx R (dc_dtor dcS1) M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx A M model c R d err len ret B rest PS X Htr BUD Hrest HDF DS CR Ha0 CONT.
    pose proof HDF as (HD1 & HD2 & HD3). cbn [dc_stack dcS1] in HD3.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ai X) as AI. destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & _). unfold w_sp0, PM_FRAME, DS_SIZE in *.
    pose proof (dl_blocks _ _ _ _ _ _ DL _ _ _ _ _ _ DS) as [HBlen HBin].
    eapply (cl_ds_dtor _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL fx A (w_s w) R M model (w_sp w - d) ret (w_sp w - d) err len B K).
    - eapply pmx_callB_at; [exact X | exact CR | lia | exact HD2 | cbn [dc_stack dcS1]; lia | cbn [dc_stack dcS1]; unfold PM_FRAME; lia].
    - exact (x_roc X).
    - exact Ha0. - exact DS.
    - split; [lia|]. split; [unfold DS_SIZE; lia|]. intros i Hi. eapply (hi_unowned MI ly_img_low ly_rw_img); [exact AI | lia].
    - intros A' R' M' model' RB XFER Hdef' EF.
      destruct (pm_dsx_step w c0 K A M model c A' R R' M' model' d B [] rest (fun _ => False) PS X Htr BUD Hrest HDF HBlen
                 ltac:(intros q k Hq; exact (proj1 (HBin q k Hq))) RB ltac:(rewrite Zlength_nil; lia) ltac:(intros q k []) Hdef' XFER ltac:(intros a [])
                 ltac:(eapply eff_weaken; [exact EF | intros a Ha; left; exact Ha]))
        as (X' & BUD' & AG).
      eapply CONT; [exact X' | exact BUD' | exact (rb_kept _ _ _ _ _ _ _ _ _ _ _ RB) | exact AG].
  Qed.

  Definition SN_D : Z := 496.

  Lemma pm_nt_find : forall (w : pmw MI ST) A M model c (fx : FPState) R (tid : Z) K,
    PMX w A M model c -> getr R 10%bv = Z_to_bv 64 (w_p w) -> getr R 8%bv = Z_to_bv 64 (PrsNeeds.sx32 tid) -> 0 <= tid < 2 ^ 32 ->
    (forall R', (forall r, ~ In r [12; 13; 14; 15; 16; 17]%bv -> getr R' r = getr R r) ->
        srealizes SEGS (cfg fx R' (nf_miss nfcS1) M model) K) ->
    (forall R' (p : Z) (v : Z * Z * Z), (forall r, ~ In r [12; 13; 14; 15; 16; 17]%bv -> getr R' r = getr R r) ->
        In (p, (tid, v)) (t3c (c_m2 c)) -> getr R' 14%bv = Z_to_bv 64 p ->
        srealizes SEGS (cfg fx R' (nf_hit nfcS1) M model) K) ->
    srealizes SEGS (cfg fx R (nf_entry nfcS1) M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w A M model c fx R tid K X Ha0 Hs0 Htid MISS HIT.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & _). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof (x_m2 X) as U. unfold O_M2 in U.
    destruct ((cl_nt_find _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL) fx A R M (w_p w) _ _ tid _ U Ha0 Hs0 Htid ltac:(lia) ltac:(lia))
      as (R' & pc' & MSx & GK & Hres).
    eapply srz_msteps; [exact (ms_halt _ MS) | exact (ms_lazy _ MS) | exact MSx |].
    destruct Hres as [-> | (-> & p & v & Hin & H14)]; [exact (MISS R' GK) | exact (HIT R' p v GK Hin H14)].
  Qed.

  Lemma sn_tail : forall (w : pmw MI ST) c0 K (fx : FPState) A M model c R (ret len p n : Z) (s0v : word) B,
    PMS w c0 K -> PMX w A M model c -> c_tr c = B -> pm_bud (w_n w) c -> SN_D + dc_stack dcS1 <= w_STK w - PM_FRAME ->
    ds_rep A M (w_sp w - SN_D) (-4) len B -> len + n <= DS_MAXLEN -> ro_cstr SEGS Ly.L p n -> 0 <= n ->
    getr R 2%bv = Z_to_bv 64 (w_sp w - SN_D) -> getr R 3%bv = Z_to_bv 64 (ly_gp Ly.L) -> getr R 4%bv = Z_to_bv 64 (ly_tp Ly.L) ->
    getr R 10%bv = Z_to_bv 64 (w_sp w - SN_D) -> getr R 11%bv = Z_to_bv 64 p -> getr R 12%bv = Z_to_bv 64 n ->
    cellw SEGS M (w_sp w - 8) 8 ret -> rdn SEGS M (Z_to_bv 64 (w_sp w - 16)) 8 = Some (word_to_le_bytes 8 s0v) -> ret_ok (Z_to_bv 64 ret) -> 0 <= ret < 2 ^ 64 ->
    (forall A' R' M' model',
        PMX w A' M' model' (set_tr c []) -> pm_bud (w_n w) (set_tr c []) ->
        (forall r, In r [9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr R' r = getr R r) ->
        getr R' 2%bv = Z_to_bv 64 (w_sp w) -> getr R' 8%bv = s0v -> getr R' 3%bv = Z_to_bv 64 (ly_gp Ly.L) -> getr R' 4%bv = Z_to_bv 64 (ly_tp Ly.L) ->
        getr R' 10%bv = sxw (2 ^ 32 - 4) ->
        CRep.agree_on (fun a => w_sp w <= a < w_sp0 w) M M' ->
        srealizes SEGS (cfg fx R' ret M' model') K) ->
    srealizes SEGS (cfg fx R 0x69b40 M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx A M model c R ret len p n s0v B PS X Htr BUD HSTK DS Hlen RO Hn Qsp Qgp Qtp Ha0 Ha1 Ha2 Cra Cs0 Hret Rret CONT.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & _). unfold w_sp0, PM_FRAME, PARSER_SIZE in *. cbn [dc_stack dcS1] in HSTK. unfold SN_D in *.
    assert (HDF : dframe_ok w 496) by (split; [unfold DS_SIZE; lia | split; [reflexivity | cbn [dc_stack dcS1]; unfold PM_FRAME; lia]]).

    pm_seed R w c [Z_to_bv 64 (w_sp w - 496); Z_to_bv 64 p; Z_to_bv 64 n].
    seedHR HR E [(2%bv, EVar 39); (10%bv, EVar 39); (11%bv, EVar 40); (12%bv, EVar 41)] R. seedHK HK w A M model c E X.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R1.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    pose proof (syms_id_sound _ _ _ _ [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HRn eq_refl) as GS1.
    clear HRn HR HK. fixregs3.
    eapply (pm_put_cstr_at w c0 K fx A M model c R1 496 (-4) len p n n _ B [] PS X ltac:(rewrite app_nil_r; exact Htr) BUD ltac:(rewrite Zlength_nil; lia) HDF DS
              ltac:(split; [exact G1 | split; [apply bv_eq; vm_compute; reflexivity | split; [lia | split; [exact G2 | split; [rewrite (GS1 3%bv) by (clear; cbn; tauto); exact Qgp | rewrite (GS1 4%bv) by (clear; cbn; tauto); exact Qtp]]]]])
              G10 G11 G12 RO ltac:(lia) ltac:(lia)).
    intros A2 R2 M2 model2 B2 X2 BUD2 KEPT Ha0' DS2 AG2. rewrite app_nil_r in X2, BUD2. pose proof (x_ms X2) as MS2.

    pose proof (dl_err _ _ _ _ _ _ DL _ _ _ _ _ _ DS2) as Herrc. unfold CRep.fld in Herrc.
    assert (Cerr : cell4 SEGS M2 (w_sp w - 496 + 360) ((-4) mod 2 ^ 32)).
    { split; [pose proof (Z.mod_pos_bound (-4) (2 ^ 32)); cbn; lia | exact Herrc]. }
    keptQ KEPT G2 Q2b.
    pm_seed R2 w c [Z_to_bv 64 (w_sp w - 496); sxw ((-4) mod 2 ^ 32)].
    seedHR HR E [(2%bv, EVar 39)] R2. seedHK HK w A2 M2 model2 (set_tr c B2) E X2.
    xruns HR HK 100%nat STOPS (SCR [] [EVar 40] []) 50%N. { split_scs; try sc_auto1. all: sc_rd_sx Cerr. }
    postrun. name_run HRn R3.
    rreg HRn (1%bv) H1. rreg HRn (2%bv) H2. rreg HRn (8%bv) H8. rreg HRn (10%bv) H10.
    pose proof (syms_id_sound _ _ _ _ [3; 4; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HRn eq_refl) as GS3.
    clear HRn HR HK. fixregs3.
    eapply (pm_dtor_at w c0 K fx A2 M2 model2 (set_tr c B2) R3 496 (-4) _ _ B2 [] PS X2 ltac:(cbn [c_tr set_tr]; rewrite app_nil_r; reflexivity) BUD2 ltac:(rewrite Zlength_nil; lia) HDF DS2
              ltac:(split; [exact H1 | split; [apply bv_eq; vm_compute; reflexivity | split; [lia | split; [exact H2 | split;
                      [rewrite (GS3 3%bv) by (clear; cbn; tauto); rewrite (KEPT 3%bv) by (clear; apply PmStepS1.in_reg_list; reflexivity); rewrite (GS1 3%bv) by (clear; cbn; tauto); exact Qgp
                      | rewrite (GS3 4%bv) by (clear; cbn; tauto); rewrite (KEPT 4%bv) by (clear; apply PmStepS1.in_reg_list; reflexivity); rewrite (GS1 4%bv) by (clear; cbn; tauto); exact Qtp]]]]])
              H10).
    intros A4 R4 M4 model4 X4 BUD4 KEPT4 AG4. cbn [set_tr] in X4, BUD4. pose proof (x_ms X4) as MS4.

    assert (AG24 : CRep.agree_on (fun a => w_sp w - 104 <= a < w_sp w + 880) M M4).
    { intros a Ha. rewrite (AG4 a) by (unfold DS_SIZE, w_sp0, PM_FRAME; lia). apply AG2. unfold DS_SIZE, w_sp0, PM_FRAME. lia. }
    assert (Cra4 : cellw SEGS M4 (w_sp w - 8) 8 ret).
    { eapply (PmBody1S1.cellw_frame M M4); [exact Cra | lia | cbn; lia | eapply agree_on_weaken; [exact AG24 | unfold zwin; cbn; intros; lia]]. }
    assert (Cs04 : rdn SEGS M4 (Z_to_bv 64 (w_sp w - 16)) 8 = Some (word_to_le_bytes 8 s0v)).
    { rewrite <- Cs0. apply (rdn_agree_win SEGS M M4 (w_sp w - 16) 8); [lia | cbn; lia |]. eapply agree_on_weaken; [exact AG24 | unfold zwin; cbn; intros; lia]. }
    keptQ KEPT4 H2 Q2c. keptQ KEPT4 H8 Q8c.
    pm_seed R4 w c [Z_to_bv 64 (w_sp w - 496); sxw ((-4) mod 2 ^ 32); Z_to_bv 64 ret; s0v].
    seedHR HR E [(2%bv, EVar 39); (8%bv, EVar 40)] R4. seedHK HK w A4 M4 model4 (set_tr c []) E X4.
    apply (know_more E M4 [KWord (SA (EVar 39) 488) (N.to_nat 8) (EVar 41)]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil. eapply kword_var; [replace (w_sp w - 496 + 488) with (w_sp w - 8) by lia; exact Cra4 | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity]. }
    xruns HR HK 100%nat STOPS (SCR [] [EVar 42] []) 50%N.
    { split_scs; try sc_auto1. all: eapply (PmCoreS1.sc_read_w _ _ _ _ _ _ Cs04); [evs; rewrite ?v_addi_Z by lia; first [reflexivity | f_equal; lia] | evs; reflexivity]. }
    postrun. name_run HRn R5.
    rreg HRn (1%bv) J1. rreg HRn (2%bv) J2. rreg HRn (8%bv) J8. rreg HRn (10%bv) J10.
    pose proof (syms_id_sound _ _ _ _ [3; 4; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HRn eq_refl) as GS5.
    clear HRn HR HK. fixregs3. rewrite w_add in J2 by lia.
    eapply srz_msteps; [exact (ms_halt _ MS4) | exact (ms_lazy _ MS4) | | ].
    { norm_pc. stepjr F_69b20 D_69b20 (Z_to_bv 64 ret) ltac:(gres; rewrite J1; reflexivity). apply mst_refl. }
    lazymatch goal with |- srealizes _ (mkCfg (mkst _ ?pc _ _) _) _ => replace pc with (Z_to_bv 64 ret) by (symmetry; exact Hret) end.
    eapply (CONT A4 R5 M4 model4 X4 BUD4); [| | exact J8 | | | exact J10 |].
    - intros r Hr. rewrite (GS5 r) by (revert Hr; clear; cbn; intros Hr; tauto).
      rewrite (KEPT4 r) by (revert Hr; clear; intros Hr; apply PmStepS1.in_reg_list; cbn in Hr; decompose [or] Hr; try contradiction; subst r; reflexivity).
      rewrite (GS3 r) by (revert Hr; clear; cbn; intros Hr; tauto).
      rewrite (KEPT r) by (revert Hr; clear; intros Hr; apply PmStepS1.in_reg_list; cbn in Hr; decompose [or] Hr; try contradiction; subst r; reflexivity).
      apply GS1. revert Hr; clear; cbn; intros Hr; tauto.
    - replace (w_sp w - 496 + 496) with (w_sp w) in J2 by lia. exact J2.
    - rewrite (GS5 3%bv) by (clear; cbn; tauto). rewrite (KEPT4 3%bv) by (clear; apply PmStepS1.in_reg_list; reflexivity). rewrite (GS3 3%bv) by (clear; cbn; tauto).
      rewrite (KEPT 3%bv) by (clear; apply PmStepS1.in_reg_list; reflexivity). rewrite (GS1 3%bv) by (clear; cbn; tauto). exact Qgp.
    - rewrite (GS5 4%bv) by (clear; cbn; tauto). rewrite (KEPT4 4%bv) by (clear; apply PmStepS1.in_reg_list; reflexivity). rewrite (GS3 4%bv) by (clear; cbn; tauto).
      rewrite (KEPT 4%bv) by (clear; apply PmStepS1.in_reg_list; reflexivity). rewrite (GS1 4%bv) by (clear; cbn; tauto). exact Qtp.
    - intros a Ha. apply AG24. lia.
  Qed.

  Lemma sn_diag : forall (pc0 : Z) (w : pmw MI ST) c0 K (fx : FPState) A M model c R (tid ret : Z) (s0v : word),
    pc0 = 0x69aa4 \/ pc0 = 0x69ba0 ->
    PMS w c0 K -> PMX w A M model c -> c_tr c = [] -> pm_bud (w_n w) c -> SN_D + dc_stack dcS1 <= w_STK w - PM_FRAME ->
    getr R 2%bv = Z_to_bv 64 (w_sp w - SN_D) -> getr R 3%bv = Z_to_bv 64 (ly_gp Ly.L) -> getr R 4%bv = Z_to_bv 64 (ly_tp Ly.L) ->
    getr R 10%bv = Z_to_bv 64 (w_p w) -> getr R 8%bv = Z_to_bv 64 (PrsNeeds.sx32 tid) -> 0 <= tid < 2 ^ 32 ->
    cellw SEGS M (w_sp w - 8) 8 ret -> rdn SEGS M (Z_to_bv 64 (w_sp w - 16)) 8 = Some (word_to_le_bytes 8 s0v) -> ret_ok (Z_to_bv 64 ret) -> 0 <= ret < 2 ^ 64 ->
    (forall A' R' M' model',
        PMX w A' M' model' (set_tr c []) -> pm_bud (w_n w) (set_tr c []) ->
        (forall r, In r [9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr R' r = getr R r) ->
        getr R' 2%bv = Z_to_bv 64 (w_sp w) -> getr R' 8%bv = s0v -> getr R' 3%bv = Z_to_bv 64 (ly_gp Ly.L) -> getr R' 4%bv = Z_to_bv 64 (ly_tp Ly.L) ->
        getr R' 10%bv = sxw (2 ^ 32 - 4) ->
        CRep.agree_on (fun a => w_sp w <= a < w_sp0 w) M M' ->
        srealizes SEGS (cfg fx R' ret M' model') K) ->
    srealizes SEGS (cfg fx R pc0 M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros pc0 w c0 K fx A M model c R tid ret s0v Hpc PS X Htr BUD HSTK Qsp Qgp Qtp Ha0 Hs0 Htid Cra Cs0 Hret Rret CONT.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & Gc2 & _). unfold w_sp0, PM_FRAME, PARSER_SIZE in *. cbn [dc_stack dcS1] in HSTK. unfold SN_D in *.
    pose proof (x_scal X) as (Sc1 & Sc2 & Sc3 & Sc4).
    assert (HDF : dframe_ok w 496) by (split; [unfold DS_SIZE; lia | split; [reflexivity | cbn [dc_stack dcS1]; unfold PM_FRAME; lia]]).
    assert (WD : forall t n, w_sp w + 880 - w_STK w <= t -> t + n <= w_sp w + 880 -> mdef M t n).
    { intros t n Ht Hn i Hi. pose proof (x_wdef X (t + i - (w_sp w + 880 - w_STK w)) ltac:(unfold w_sp0, PM_FRAME; lia)) as D.
      unfold w_sp0, PM_FRAME in D. replace (w_sp w + 880 - w_STK w + (t + i - (w_sp w + 880 - w_STK w))) with (t + i) in D by lia. exact D. }

    pm_seed R w c [Z_to_bv 64 (w_sp w - 496); Z_to_bv 64 (PrsNeeds.sx32 tid)].
    seedHR HR E [(2%bv, EVar 39); (10%bv, EVar 33); (8%bv, EVar 40)] R. seedHK HK w A M model c E X.
    apply (know_more E M [KWr (SA (EVar 39) 0) (ELit 496)]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil. eapply kwr_mdef; [evs; reflexivity | apply WD; lia | lia | lia | lia | lia]. }
    destruct Hpc as [-> | ->].
    all: xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N; [split_scs; try sc_auto1 |].
    all: postrun; name_run HRn R1.
    all: rreg HRn (1%bv) G1; rreg HRn (2%bv) G2; rreg HRn (10%bv) G10; rreg HRn (11%bv) G11; rreg HRn (12%bv) G12; rreg HRn (13%bv) G13; rreg HRn (14%bv) G14; rreg HRn (15%bv) G15.
    all: rreg HRn (8%bv) G8; pose proof (syms_id_sound _ _ _ _ [3; 4; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HRn eq_refl) as GS1.
    all: clear HRn HR HK; fixregs3; rewrite w_add in G11 by lia; rewrite w_add in G13 by lia; rewrite w_add in G15 by lia.
    all: lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?mm _) _) _ => set (M2 := mm) in * end.
    all: assert (ST2 : stores_in (zwin (w_sp w - 496 + 408) (w_sp w - 496 + 480)) M M2) by (unfold M2; stin).
    all: assert (X2 : PMX w A M2 model c) by (eapply (pmx_low_stores w A M M2 model c); [exact X | exact ST2 | unfold zwin, w_sp0, PM_FRAME; intros; lia]).
    all: assert (F1 : fld SEGS M2 (w_sp w - 496 + 432) 2 0) by (unfold M2; rdback).
    all: assert (F2 : fld SEGS M2 (w_sp w - 496 + 408) 2 0) by (unfold M2; rdback).
    all: assert (AG2 : CRep.agree_on (fun a => w_sp w - 16 <= a < w_sp w + 880) M M2) by (eapply stores_in_agree; [exact ST2 | intros b Hb; unfold zwin in *; lia]).
    all: assert (B1 : cellw SEGS M2 (w_sp w - 496 + 432) 1 0) by (split; [cbn; lia | unfold M2; rdback]).
    all: assert (B2 : cellw SEGS M2 (w_sp w - 496 + 408) 1 0) by (split; [cbn; lia | unfold M2; rdback]).
    all: pose proof (x_ms X2) as MS2; clearbody M2.
    all: eapply (pm_ctor_at w c0 K fx A M2 model c R1 496 (-4) (w_sp w - 496 + 456) (w_sp w - 496 + 432) (w_sp w - 496 + 408) _ [] PS X2 Htr BUD ltac:(rewrite Zlength_nil; lia) HDF
              ltac:(split; [exact G1 | split; [apply bv_eq; vm_compute; reflexivity | split; [lia | split; [exact G2 | split; [rewrite (GS1 3%bv) by (clear; cbn; tauto); exact Qgp | rewrite (GS1 4%bv) by (clear; cbn; tauto); exact Qtp]]]]])
              G10 G11 ltac:(rewrite G12; reflexivity) G13 ltac:(rewrite G14; apply bv_eq; vm_compute; reflexivity) G15);
         [lia | unfold DS_SIZE; lia | lia | unfold DS_SIZE; lia | lia | unfold DS_SIZE; lia | lia | exact F1 | exact F2 |].
    all: intros A3 R3 M3 model3 B3 X3 BUD3 KEPT DS3 AG3; rewrite app_nil_r in X3, BUD3; pose proof (x_ms X3) as MS3.
    all: keptQ KEPT G2 Q2c; keptQ KEPT G8 Q8c.
    all: assert (B1' : cellw SEGS M3 (w_sp w - 496 + 432) 1 0) by (eapply (PmBody1S1.cellw_frame M2 M3); [exact B1 | lia | cbn; lia | eapply agree_on_weaken; [exact AG3 | unfold zwin, DS_SIZE, w_sp0, PM_FRAME; cbn; intros; lia]]).
    all: assert (B2' : cellw SEGS M3 (w_sp w - 496 + 408) 1 0) by (eapply (PmBody1S1.cellw_frame M2 M3); [exact B2 | lia | cbn; lia | eapply agree_on_weaken; [exact AG3 | unfold zwin, DS_SIZE, w_sp0, PM_FRAME; cbn; intros; lia]]).

    all: pm_seed R3 w c [Z_to_bv 64 (w_sp w - 496)].
    all: seedHR HR E [(2%bv, EVar 39)] R3; seedHK HK w A3 M3 model3 (set_tr c B3) E X3.
    all: apply (know_more E M3 [KWord (SA (EVar 39) 432) (N.to_nat 1) (ELit 0); KWord (SA (EVar 39) 408) (N.to_nat 1) (ELit 0)]) in HK;
         [| repeat apply Forall_cons; try apply Forall_nil;
            [ eapply kword_var; [exact B1' | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity]
            | eapply kword_var; [exact B2' | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity] ] ].
    all: xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N; [split_scs; try sc_auto1 |].
    all: postrun; name_run HRn R4.
    all: rreg HRn (1%bv) H1; rreg HRn (2%bv) H2; rreg HRn (10%bv) H10; rreg HRn (11%bv) H11; rreg HRn (12%bv) H12.
    all: pose proof (syms_id_sound _ _ _ _ [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HRn eq_refl) as GS4.
    all: clear HRn HR HK; fixregs3.
    all: lazymatch type of H11 with _ = Z_to_bv 64 ?p => lazymatch type of H12 with _ = Z_to_bv 64 ?n =>
           assert (RO1 : ro_cstr SEGS Ly.L p n) by (apply ro_cstr_of_chk; vm_compute; reflexivity) end end.
    all: lazymatch type of RO1 with ro_cstr _ _ ?p ?n =>
         eapply (pm_put_cstr_at w c0 K fx A3 M3 model3 (set_tr c B3) R4 496 (-4) 0 p n n _ B3 [] PS X3 ltac:(cbn [c_tr set_tr]; rewrite app_nil_r; reflexivity) BUD3 ltac:(rewrite Zlength_nil; lia) HDF DS3
              ltac:(split; [exact H1 | split; [apply bv_eq; vm_compute; reflexivity | split; [lia | split; [exact H2 | split;
                      [rewrite (GS4 3%bv) by (clear; cbn; tauto); rewrite (KEPT 3%bv) by (clear; apply PmStepS1.in_reg_list; reflexivity); rewrite (GS1 3%bv) by (clear; cbn; tauto); exact Qgp
                      | rewrite (GS4 4%bv) by (clear; cbn; tauto); rewrite (KEPT 4%bv) by (clear; apply PmStepS1.in_reg_list; reflexivity); rewrite (GS1 4%bv) by (clear; cbn; tauto); exact Qtp]]]]])
              H10 H11 H12 RO1 ltac:(lia) ltac:(unfold DS_MAXLEN; lia)) end.
    all: intros A5 R5 M5 model5 B5 X5 BUD5 KEPT5 _ DS5 AG5; cbn [set_tr] in X5, BUD5; rewrite app_nil_r in X5, BUD5; pose proof (x_ms X5) as MS5.
    all: keptQ KEPT5 H2 Q2e.
    all: assert (Q8e : getr R5 8%bv = Z_to_bv 64 (PrsGrammar.sx32 tid)) by (rewrite (KEPT5 8%bv) by (clear; apply PmStepS1.in_reg_list; reflexivity); rewrite (GS4 8%bv) by (clear; cbn; tauto); exact Q8c).

    all: pm_seed R5 w c [Z_to_bv 64 (w_sp w - 496); Z_to_bv 64 (PrsGrammar.sx32 tid)].
    all: seedHR HR E [(2%bv, EVar 39); (8%bv, EVar 40)] R5; seedHK HK w A5 M5 model5 (set_tr c B5) E X5.
    all: xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N; [split_scs; try sc_auto1 |].
    all: postrun; name_run HRn R6.
    all: rreg HRn (1%bv) I1; rreg HRn (2%bv) I2; rreg HRn (10%bv) I10; rreg HRn (11%bv) I11.
    all: pose proof (syms_id_sound _ _ _ _ [3; 4; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HRn eq_refl) as GS6.
    all: clear HRn HR HK; fixregs3.
    all: eapply (pm_put_u32_at w c0 K fx A5 M5 model5 (set_tr c B5) R6 496 (-4) _ tid _ B5 [] PS X5 ltac:(cbn [c_tr set_tr]; rewrite app_nil_r; reflexivity) BUD5 ltac:(rewrite Zlength_nil; lia) HDF DS5
              ltac:(split; [exact I1 | split; [apply bv_eq; vm_compute; reflexivity | split; [lia | split; [exact I2 | split;
                      [rewrite (GS6 3%bv) by (clear; cbn; tauto); rewrite (KEPT5 3%bv) by (clear; apply PmStepS1.in_reg_list; reflexivity); rewrite (GS4 3%bv) by (clear; cbn; tauto); rewrite (KEPT 3%bv) by (clear; apply PmStepS1.in_reg_list; reflexivity); rewrite (GS1 3%bv) by (clear; cbn; tauto); exact Qgp
                      | rewrite (GS6 4%bv) by (clear; cbn; tauto); rewrite (KEPT5 4%bv) by (clear; apply PmStepS1.in_reg_list; reflexivity); rewrite (GS4 4%bv) by (clear; cbn; tauto); rewrite (KEPT 4%bv) by (clear; apply PmStepS1.in_reg_list; reflexivity); rewrite (GS1 4%bv) by (clear; cbn; tauto); exact Qtp]]]]])
              I10 I11 Htid ltac:(unfold DS_MAXLEN; lia)).
    all: intros A7 R7 M7 model7 B7 X7 BUD7 KEPT7 _ DS7 AG7; cbn [set_tr] in X7, BUD7; rewrite app_nil_r in X7, BUD7; pose proof (x_ms X7) as MS7.
    all: keptQ KEPT7 I2 Q2g.

    all: pm_seed R7 w c [Z_to_bv 64 (w_sp w - 496)].
    all: seedHR HR E [(2%bv, EVar 39)] R7; seedHK HK w A7 M7 model7 (set_tr c B7) E X7.
    all: xruns HR HK 100%nat (0x69b40 :: STOPS) (SCR [] [] []) 50%N; [split_scs; try sc_auto1 |].
    all: postrun; name_run HRn R8.
    all: rreg HRn (2%bv) J2; rreg HRn (10%bv) J10; rreg HRn (11%bv) J11; rreg HRn (12%bv) J12.
    all: pose proof (syms_id_sound _ _ _ _ [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HRn eq_refl) as GS8.
    all: clear HRn HR HK; fixregs3.
    all: assert (KK : forall r, In r [3; 4; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr R8 r = getr R r) by
      (intros r Hr; rewrite (GS8 r) by (revert Hr; clear; cbn; intros Hr; tauto);
      rewrite (KEPT7 r) by (revert Hr; clear; intros Hr; apply PmStepS1.in_reg_list; cbn in Hr; decompose [or] Hr; try contradiction; subst r; reflexivity);
      rewrite (GS6 r) by (revert Hr; clear; cbn; intros Hr; tauto);
      rewrite (KEPT5 r) by (revert Hr; clear; intros Hr; apply PmStepS1.in_reg_list; cbn in Hr; decompose [or] Hr; try contradiction; subst r; reflexivity);
      rewrite (GS4 r) by (revert Hr; clear; cbn; intros Hr; tauto);
      rewrite (KEPT r) by (revert Hr; clear; intros Hr; apply PmStepS1.in_reg_list; cbn in Hr; decompose [or] Hr; try contradiction; subst r; reflexivity);
      apply GS1; revert Hr; clear; cbn; intros Hr; tauto).
    all: assert (AG17 : CRep.agree_on (fun a => w_sp w - 16 <= a < w_sp w + 880) M M7) by
      (intros a Ha; rewrite (AG7 a) by (unfold DS_SIZE, w_sp0, PM_FRAME; lia); rewrite (AG5 a) by (unfold DS_SIZE, w_sp0, PM_FRAME; lia);
       rewrite (AG3 a) by (unfold DS_SIZE, w_sp0, PM_FRAME; lia); apply AG2; lia).
    all: assert (Cra7 : cellw SEGS M7 (w_sp w - 8) 8 ret) by (eapply (PmBody1S1.cellw_frame M M7); [exact Cra | lia | cbn; lia | eapply agree_on_weaken; [exact AG17 | unfold zwin; cbn; intros; lia]]).
    all: assert (Cs07 : rdn SEGS M7 (Z_to_bv 64 (w_sp w - 16)) 8 = Some (word_to_le_bytes 8 s0v))
           by (rewrite <- Cs0; apply (rdn_agree_win SEGS M M7 (w_sp w - 16) 8); [lia | cbn; lia | eapply agree_on_weaken; [exact AG17 | unfold zwin; cbn; intros; lia]]).
    all: lazymatch type of J11 with _ = Z_to_bv 64 ?p => lazymatch type of J12 with _ = Z_to_bv 64 ?n =>
           assert (RO2 : ro_cstr SEGS Ly.L p n) by (apply ro_cstr_of_chk; vm_compute; reflexivity) end end.
    all: lazymatch type of RO2 with ro_cstr _ _ ?p ?n =>
         eapply (sn_tail w c0 K fx A7 M7 model7 (set_tr c B7) R8 ret (0 + 8 + 24) p n s0v B7 PS X7 ltac:(reflexivity) BUD7 ltac:(unfold SN_D, PM_FRAME; cbn [dc_stack dcS1]; lia) DS7 ltac:(unfold DS_MAXLEN; lia) RO2 ltac:(lia)
                   J2 ltac:(rewrite (KK 3%bv) by (clear; cbn; tauto); exact Qgp) ltac:(rewrite (KK 4%bv) by (clear; cbn; tauto); exact Qtp) J10 J11 J12 Cra7 Cs07 Hret Rret) end.
    all: intros A9 R9 M9 model9 X9 BUD9 GK9 Y2 Y8 Y3 Y4 Y10 AG9; cbn [set_tr] in X9, BUD9.
    all: eapply (CONT A9 R9 M9 model9 X9 BUD9); [| exact Y2 | exact Y8 | exact Y3 | exact Y4 | exact Y10 |].
    1, 3: intros r Hr; rewrite (GK9 r Hr); apply KK; revert Hr; clear; cbn; intros Hr; tauto.
    all: intros a Ha; rewrite (AG9 a) by (unfold w_sp0, PM_FRAME; lia); apply AG17; lia.
  Qed.
  Lemma w2lb2_mod : forall (W : word), word_to_le_bytes 2 W = word_to_le_bytes 2 (Z_to_bv 64 (bv_unsigned W mod 2 ^ 16)).
  Proof using.
    intros W. rewrite <- (Z_to_bv_bv_unsigned 64 W) at 1. apply word_to_le_bytes_low; [lia|].
    intros i Hi. cbn in Hi. symmetry. apply Z.mod_pow2_bits_low. lia.
  Qed.

  Ltac reg_cases r :=
    let ur := fresh "ur" in let Hur := fresh "Hur" in let H := fresh "Hrc" in let Hr5 := fresh "Hr5" in
    pose proof (u5_range r) as Hr5; remember (bv_unsigned r) as ur eqn:Hur in *;
    pose proof (PmDispatchS1.In_range_enum ur 0 32 ltac:(lia)) as H; vm_compute in H; clear Hr5;
    repeat match type of H with
           | _ \/ _ => destruct H as [H|H]; [rewrite <- H in Hur; clear H; apply (f_equal (Z_to_bv 5)) in Hur; rewrite Z_to_bv_bv_unsigned in Hur; subst r |]
           | False => destruct H
           end.
  Ltac in_regs := apply PmStepS1.in_reg_list; reflexivity.
  Ltac fixregs_lit :=
    try (lazymatch goal with |- context [Z_to_bv 5 0] => idtac | _ : context [Z_to_bv 5 0] |- _ => idtac end; replace (Z_to_bv 5 0) with (0%bv : reg) in * by (apply bv_eq; reflexivity));
    try (lazymatch goal with |- context [Z_to_bv 5 1] => idtac | _ : context [Z_to_bv 5 1] |- _ => idtac end; replace (Z_to_bv 5 1) with (1%bv : reg) in * by (apply bv_eq; reflexivity));
    try (lazymatch goal with |- context [Z_to_bv 5 2] => idtac | _ : context [Z_to_bv 5 2] |- _ => idtac end; replace (Z_to_bv 5 2) with (2%bv : reg) in * by (apply bv_eq; reflexivity));
    try (lazymatch goal with |- context [Z_to_bv 5 3] => idtac | _ : context [Z_to_bv 5 3] |- _ => idtac end; replace (Z_to_bv 5 3) with (3%bv : reg) in * by (apply bv_eq; reflexivity));
    try (lazymatch goal with |- context [Z_to_bv 5 4] => idtac | _ : context [Z_to_bv 5 4] |- _ => idtac end; replace (Z_to_bv 5 4) with (4%bv : reg) in * by (apply bv_eq; reflexivity));
    try (lazymatch goal with |- context [Z_to_bv 5 5] => idtac | _ : context [Z_to_bv 5 5] |- _ => idtac end; replace (Z_to_bv 5 5) with (5%bv : reg) in * by (apply bv_eq; reflexivity));
    try (lazymatch goal with |- context [Z_to_bv 5 6] => idtac | _ : context [Z_to_bv 5 6] |- _ => idtac end; replace (Z_to_bv 5 6) with (6%bv : reg) in * by (apply bv_eq; reflexivity));
    try (lazymatch goal with |- context [Z_to_bv 5 7] => idtac | _ : context [Z_to_bv 5 7] |- _ => idtac end; replace (Z_to_bv 5 7) with (7%bv : reg) in * by (apply bv_eq; reflexivity));
    try (lazymatch goal with |- context [Z_to_bv 5 8] => idtac | _ : context [Z_to_bv 5 8] |- _ => idtac end; replace (Z_to_bv 5 8) with (8%bv : reg) in * by (apply bv_eq; reflexivity));
    try (lazymatch goal with |- context [Z_to_bv 5 9] => idtac | _ : context [Z_to_bv 5 9] |- _ => idtac end; replace (Z_to_bv 5 9) with (9%bv : reg) in * by (apply bv_eq; reflexivity));
    try (lazymatch goal with |- context [Z_to_bv 5 10] => idtac | _ : context [Z_to_bv 5 10] |- _ => idtac end; replace (Z_to_bv 5 10) with (10%bv : reg) in * by (apply bv_eq; reflexivity));
    try (lazymatch goal with |- context [Z_to_bv 5 11] => idtac | _ : context [Z_to_bv 5 11] |- _ => idtac end; replace (Z_to_bv 5 11) with (11%bv : reg) in * by (apply bv_eq; reflexivity));
    try (lazymatch goal with |- context [Z_to_bv 5 12] => idtac | _ : context [Z_to_bv 5 12] |- _ => idtac end; replace (Z_to_bv 5 12) with (12%bv : reg) in * by (apply bv_eq; reflexivity));
    try (lazymatch goal with |- context [Z_to_bv 5 13] => idtac | _ : context [Z_to_bv 5 13] |- _ => idtac end; replace (Z_to_bv 5 13) with (13%bv : reg) in * by (apply bv_eq; reflexivity));
    try (lazymatch goal with |- context [Z_to_bv 5 14] => idtac | _ : context [Z_to_bv 5 14] |- _ => idtac end; replace (Z_to_bv 5 14) with (14%bv : reg) in * by (apply bv_eq; reflexivity));
    try (lazymatch goal with |- context [Z_to_bv 5 15] => idtac | _ : context [Z_to_bv 5 15] |- _ => idtac end; replace (Z_to_bv 5 15) with (15%bv : reg) in * by (apply bv_eq; reflexivity));
    try (lazymatch goal with |- context [Z_to_bv 5 16] => idtac | _ : context [Z_to_bv 5 16] |- _ => idtac end; replace (Z_to_bv 5 16) with (16%bv : reg) in * by (apply bv_eq; reflexivity));
    try (lazymatch goal with |- context [Z_to_bv 5 17] => idtac | _ : context [Z_to_bv 5 17] |- _ => idtac end; replace (Z_to_bv 5 17) with (17%bv : reg) in * by (apply bv_eq; reflexivity));
    try (lazymatch goal with |- context [Z_to_bv 5 18] => idtac | _ : context [Z_to_bv 5 18] |- _ => idtac end; replace (Z_to_bv 5 18) with (18%bv : reg) in * by (apply bv_eq; reflexivity));
    try (lazymatch goal with |- context [Z_to_bv 5 19] => idtac | _ : context [Z_to_bv 5 19] |- _ => idtac end; replace (Z_to_bv 5 19) with (19%bv : reg) in * by (apply bv_eq; reflexivity));
    try (lazymatch goal with |- context [Z_to_bv 5 20] => idtac | _ : context [Z_to_bv 5 20] |- _ => idtac end; replace (Z_to_bv 5 20) with (20%bv : reg) in * by (apply bv_eq; reflexivity));
    try (lazymatch goal with |- context [Z_to_bv 5 21] => idtac | _ : context [Z_to_bv 5 21] |- _ => idtac end; replace (Z_to_bv 5 21) with (21%bv : reg) in * by (apply bv_eq; reflexivity));
    try (lazymatch goal with |- context [Z_to_bv 5 22] => idtac | _ : context [Z_to_bv 5 22] |- _ => idtac end; replace (Z_to_bv 5 22) with (22%bv : reg) in * by (apply bv_eq; reflexivity));
    try (lazymatch goal with |- context [Z_to_bv 5 23] => idtac | _ : context [Z_to_bv 5 23] |- _ => idtac end; replace (Z_to_bv 5 23) with (23%bv : reg) in * by (apply bv_eq; reflexivity));
    try (lazymatch goal with |- context [Z_to_bv 5 24] => idtac | _ : context [Z_to_bv 5 24] |- _ => idtac end; replace (Z_to_bv 5 24) with (24%bv : reg) in * by (apply bv_eq; reflexivity));
    try (lazymatch goal with |- context [Z_to_bv 5 25] => idtac | _ : context [Z_to_bv 5 25] |- _ => idtac end; replace (Z_to_bv 5 25) with (25%bv : reg) in * by (apply bv_eq; reflexivity));
    try (lazymatch goal with |- context [Z_to_bv 5 26] => idtac | _ : context [Z_to_bv 5 26] |- _ => idtac end; replace (Z_to_bv 5 26) with (26%bv : reg) in * by (apply bv_eq; reflexivity));
    try (lazymatch goal with |- context [Z_to_bv 5 27] => idtac | _ : context [Z_to_bv 5 27] |- _ => idtac end; replace (Z_to_bv 5 27) with (27%bv : reg) in * by (apply bv_eq; reflexivity));
    try (lazymatch goal with |- context [Z_to_bv 5 28] => idtac | _ : context [Z_to_bv 5 28] |- _ => idtac end; replace (Z_to_bv 5 28) with (28%bv : reg) in * by (apply bv_eq; reflexivity));
    try (lazymatch goal with |- context [Z_to_bv 5 29] => idtac | _ : context [Z_to_bv 5 29] |- _ => idtac end; replace (Z_to_bv 5 29) with (29%bv : reg) in * by (apply bv_eq; reflexivity));
    try (lazymatch goal with |- context [Z_to_bv 5 30] => idtac | _ : context [Z_to_bv 5 30] |- _ => idtac end; replace (Z_to_bv 5 30) with (30%bv : reg) in * by (apply bv_eq; reflexivity));
    try (lazymatch goal with |- context [Z_to_bv 5 31] => idtac | _ : context [Z_to_bv 5 31] |- _ => idtac end; replace (Z_to_bv 5 31) with (31%bv : reg) in * by (apply bv_eq; reflexivity)).

  Lemma pm_set_numeric : forall (w : pmw MI ST) c0 K (fx : FPState) A M model c R (tid ret : Z),
    PMS w c0 K -> PMX w A M model c -> c_tr c = [] -> pm_bud (w_n w) c -> SN_D + dc_stack dcS1 <= w_STK w - PM_FRAME ->
    cregs w R ret -> getr R 10%bv = Z_to_bv 64 (w_p w) -> getr R 11%bv = Z_to_bv 64 (w_sp w + 684) -> getr R 12%bv = Z_to_bv 64 (PrsNeeds.sx32 tid) -> 0 <= tid < 2 ^ 32 ->
    (forall A' R' M' model' (e : Z),
        PMX w A' M' model' c -> pm_bud (w_n w) c ->
        (forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr R' r = getr R r) ->
        getr R' 10%bv = sxw e -> 0 <= e < 2 ^ 32 ->
        CRep.agree_on (fun a => w_sp w <= a < w_sp0 w /\ ~ (w_sp w + 686 <= a < w_sp w + 688) /\ ~ (w_sp w + 692 <= a < w_sp w + 704)) M M' ->
        (e = 0 -> exists nw nk, cellw SEGS M' (w_sp w + 686) 2 nw /\ cellw SEGS M' (w_sp w + 692) 4 nk) ->
        srealizes SEGS (cfg fx R' ret M' model') K) ->
    srealizes SEGS (cfg fx R (kc_set_numeric kcS1) M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx A M model c R tid ret PS X Htr BUD HSTK CR Ha0 Ha1 Ha2 Htid CONT.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS. pose proof (x_ai X) as AI.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & Gc2 & _). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof HSTK as HSTK'. cbn [dc_stack dcS1] in HSTK'. unfold SN_D in HSTK'.
    destruct CR as (C1 & C2 & C3 & C4 & C5 & C6).
    assert (WD : forall t n, w_sp w + 880 - w_STK w <= t -> t + n <= w_sp w + 880 -> mdef M t n).
    { intros t n Ht Hn i Hi. pose proof (x_wdef X (t + i - (w_sp w + 880 - w_STK w)) ltac:(unfold w_sp0, PM_FRAME; lia)) as D.
      unfold w_sp0, PM_FRAME in D. replace (w_sp w + 880 - w_STK w + (t + i - (w_sp w + 880 - w_STK w))) with (t + i) in D by lia. exact D. }

    pm_seed R w c [Z_to_bv 64 ret; getr R 8%bv; Z_to_bv 64 (PrsNeeds.sx32 tid)].
    seedHR HR E [(2%bv, EVar 32); (1%bv, EVar 39); (8%bv, EVar 40); (12%bv, EVar 41); (10%bv, EVar 33)] R. seedHK HK w A M model c E X.
    apply (know_more E M [KWr (SA (EVar 32) (-496)) (ELit 496)]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil. eapply kwr_mdef; [evs; reflexivity | apply WD; lia | lia | lia | lia | lia]. }
    xruns HR HK 100%nat (0x69988 :: STOPS) (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R1.
    rreg HRn (2%bv) G2. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11.
    pose proof (syms_id_sound _ _ _ _ [3; 4; 9; 11; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HRn eq_refl) as GS1.
    clear HRn HR HK. fixregs3. rewrite w_addm in G2 by lia.
    lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?mm _) _) _ => set (M1 := mm) in * end.
    assert (ST1 : stores_in (zwin (w_sp w - 16) (w_sp w)) M M1) by (unfold M1; stin).
    assert (X1 : PMX w A M1 model c) by (eapply (pmx_low_stores w A M M1 model c); [exact X | exact ST1 | unfold zwin, w_sp0, PM_FRAME; intros; lia]).
    assert (Cra : cellw SEGS M1 (w_sp w - 8) 8 ret) by (split; [cbn; lia | unfold M1; rdback]).
    assert (Cs0 : rdn SEGS M1 (Z_to_bv 64 (w_sp w - 16)) 8 = Some (word_to_le_bytes 8 (getr R 8%bv))) by (unfold M1; rdback).
    assert (AG1 : CRep.agree_on (fun a => w_sp w <= a < w_sp w + 880) M M1) by (eapply stores_in_agree; [exact ST1 | intros b Hb; unfold zwin in *; lia]).
    pose proof (x_ms X1) as MS1. clearbody M1. clear ST1.

    assert (DIAG : forall pc0 Rd, pc0 = 0x69aa4 \/ pc0 = 0x69ba0 -> (forall r, ~ In r [12; 13; 14; 15; 16; 17]%bv -> getr Rd r = getr R1 r) ->
              srealizes SEGS (cfg fx Rd pc0 M1 model) K).
    { intros pc0 Rd Hpc GK.
      eapply (sn_diag pc0 w c0 K fx A M1 model c Rd tid ret (getr R 8%bv) Hpc PS X1 Htr BUD HSTK); try (rewrite GK by (clear; cbn; intuition discriminate)).
      - exact G2. - rewrite (GS1 3%bv) by (clear; cbn; tauto). exact C5. - rewrite (GS1 4%bv) by (clear; cbn; tauto). exact C6.
      - exact G10. - exact G8. - exact Htid. - exact Cra. - exact Cs0. - exact C2. - exact C3.
      - intros A' R' M' model' X' BUD' GK' Y2 Y8 Y3 Y4 Y10 AG'. rewrite <- Htr, PmStepS1.set_tr_id in X', BUD'.
        eapply (CONT A' R' M' model' (2 ^ 32 - 4)); [exact X' | exact BUD' | | exact Y10 | lia | | intros He; exfalso; lia].
        + intros r Hr. cbn in Hr.
          destruct Hr as [<- | [<- | [<- | [<- | Hin]]]]; [rewrite Y2; symmetry; exact C4 | rewrite Y3; symmetry; exact C5 | rewrite Y4; symmetry; exact C6 | exact Y8 |].
          rewrite (GK' r Hin). rewrite (GK r) by (revert Hin; clear; intros Hin [H|[H|[H|[H|[H|[H|[]]]]]]]; subst r; cbn in Hin; intuition discriminate).
          apply GS1. revert Hin; clear; cbn; intros Hin; tauto.
        + intros a (Ha & _ & _). rewrite (AG' a) by (unfold w_sp0, PM_FRAME; lia). apply AG1. lia. }
    eapply (pm_nt_find w A M1 model c fx R1 tid K X1 G10 G8 Htid).
    { intros Rm GK. apply (DIAG 0x69aa4 Rm (or_introl eq_refl) GK). }
    intros Rh p v GK Hin H14.
    pose proof (x_m2 X1) as U. pose proof U as U0. destruct U0 as [_ _ _ _ _ _ _ _ _ _ _ _ _ _ Unode _].
    destruct v as [[nk bw] enc]. destruct (Unode p tid _ Hin) as (Hlive & Hp0 & Hp47 & Hpal & _ & _ & _ & NV & _).
    cbn [nval32] in NV. destruct NV as (Cnk & Cbw & Cenc).
    pose proof (proj1 Cnk) as Rnk. pose proof (proj1 Cbw) as Rbw. pose proof (proj1 Cenc) as Renc. cbn in Rnk, Rbw, Renc.
    assert (U2 : getr Rh 2%bv = Z_to_bv 64 (w_sp w - 496)) by (rewrite (GK 2%bv) by (clear; cbn; intuition discriminate); exact G2).
    assert (U11 : getr Rh 11%bv = Z_to_bv 64 (w_sp w + 684)) by (rewrite (GK 11%bv) by (clear; cbn; intuition discriminate); rewrite (GS1 11%bv) by (clear; cbn; tauto); exact Ha1).
    destruct (Z.eq_dec nk 0) as [Hnk0 | Hnk].
    {
      subst nk.
      pm_seed Rh w c [Z_to_bv 64 (w_sp w - 496); Z_to_bv 64 p].
      seedHR HR E [(2%bv, EVar 39); (14%bv, EVar 40)] Rh. seedHK HK w A M1 model c E X1.
      apply (know_more E M1 [KWord (SA (EVar 40) 20) (N.to_nat 4) (ELit 0)]) in HK.
      2: { repeat apply Forall_cons; try apply Forall_nil. eapply kword_var; [exact Cnk | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity]. }
      xruns HR HK 100%nat (0x69ba0 :: STOPS) (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
      postrun. name_run HRn R2.
      rreg HRn (2%bv) G2'. pose proof (syms_id_sound _ _ _ _ [1; 3; 4; 5; 6; 7; 8; 9; 10; 11; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv HRn eq_refl) as GS2.
      clear HRn HR HK. fixregs3.
      apply (DIAG 0x69ba0 R2 (or_intror eq_refl)).
      intros r Hr. reg_cases r; fixregs_lit; try (exfalso; apply Hr; clear; in_regs);
        first [ rewrite (GS2 _) by (clear; in_regs); apply GK; exact Hr
              | rewrite G2'; symmetry; exact G2
              | rewrite !getr_zero; reflexivity
              ]. }

    assert (U2' : getr Rh 2%bv = alu64 ALU_ADD (Z_to_bv 64 (w_sp w)) (Z_to_bv 64 (-496))) by (rewrite w_addm by lia; rewrite U2; f_equal; lia).
    pm_seed Rh w c [Z_to_bv 64 (w_sp w - 496); Z_to_bv 64 p; Z_to_bv 64 nk; Z_to_bv 64 bw; Z_to_bv 64 enc; Z_to_bv 64 ret; getr R 8%bv].
    seedHR HR E [(2%bv, EAlu ALU_ADD (EVar 32) (ELit (-496))); (14%bv, EVar 40); (11%bv, EAlu ALU_ADD (EVar 32) (ELit 684))] Rh. seedHK HK w A M1 model c E X1.
    apply (know_more E M1 [KRange (EVar 41) 1 (2 ^ 32); KWord (SA (EVar 40) 20) (N.to_nat 4) (EVar 41); KWord (SA (EVar 40) 24) (N.to_nat 4) (EVar 42);
                           KWord (SA (EVar 40) 28) (N.to_nat 4) (EVar 43); KWord (SA (EVar 32) (-8)) (N.to_nat 8) (EVar 44);
                           KDisj (SA (EVar 40) 0) (ELit 32) (SA (EVar 32) 0) (ELit 880)]) in HK.
    2: { destruct (ai_live_block MI A M1 model p 32 (x_ai X1) Hlive) as (_ & _ & _ & Hpc & _).
         repeat apply Forall_cons; try apply Forall_nil.
         - eapply krange_var; [evs; reflexivity | lia | lia].
         - eapply kword_var; [exact Cnk | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
         - eapply kword_var; [exact Cbw | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
         - eapply kword_var; [exact Cenc | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
         - eapply kword_var; [replace (w_sp w + -8) with (w_sp w - 8) by lia; exact Cra | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
         - eapply kdisj_vars; [evs; reflexivity | evs; reflexivity | lia | lia | lia | lia | lia]. }
    assert (Hsx : 0 < PrsGrammar.sx32 nk < 2 ^ 64) by (unfold PrsGrammar.sx32; destruct (Z.ltb_spec nk (2 ^ 31)); lia).
    xruns HR HK 100%nat STOPS (SCR [false] [EVar 45] []) 50%N.
    { split_scs; try sc_auto1.
      all: first [ cbn [sc_denot]; evs; rewrite PmStepS1.ext_val_sx4 by lia; rewrite ?br_eq, ?br_ne by lia; bool_lia
                 | eapply (PmCoreS1.sc_read_w _ _ _ _ _ _ Cs0); [evs; rewrite ?v_addi_Z by lia; first [reflexivity | f_equal; lia] | evs; reflexivity] ]. }
    postrun. name_run HRn R2.
    rreg HRn (1%bv) J1. rreg HRn (2%bv) J2. rreg HRn (8%bv) J8. rreg HRn (10%bv) J10.
    pose proof (syms_id_sound _ _ _ _ [3; 4; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HRn eq_refl) as GS2.
    clear HRn HR HK. fixregs3. rewrite ?w_addm, ?w_add in J2 by lia. rewrite ?Z.add_0_r in J2. try replace (w_sp w + -496 + 496) with (w_sp w) in J2 by lia.
    rewrite !PmStepS1.ext_val_sx4 by lia. rewrite !PmBody1S1.w2lb4_sx32 by lia. rewrite w2lb2_mod.
    lazymatch goal with |- context [word_to_le_bytes 2 (Z_to_bv 64 ?v)] => set (nwv := v) in * end.
    assert (Rnw : 0 <= nwv < 2 ^ 16) by (apply Z.mod_pos_bound; lia).
    lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?mm _) _) _ => set (M2 := mm) in * end.
    assert (ST2 : stores_in (fun a => zwin (w_sp w + 686) (w_sp w + 688) a \/ zwin (w_sp w + 692) (w_sp w + 704) a) M1 M2) by (unfold M2; stin).
    assert (X2 : PMX w A M2 model c).
    { eapply (pmx_frame_stores SEGS Ly.L MI ST ly_img_low ly_rw_img ly_relro_img w A M1 M2 model c _ X1 ST2). unfold zwin, w_sp0, PM_FRAME. intros; lia. }
    assert (Cnw : cellw SEGS M2 (w_sp w + 686) 2 nwv) by (split; [cbn; lia | unfold M2; rdback]).
    assert (Cnk2 : cellw SEGS M2 (w_sp w + 692) 4 nk) by (split; [cbn; lia | unfold M2; rdback]).
    assert (AG2 : CRep.agree_on (fun a => w_sp w <= a < w_sp0 w /\ ~ (w_sp w + 686 <= a < w_sp w + 688) /\ ~ (w_sp w + 692 <= a < w_sp w + 704)) M M2).
    { intros a Ha. unfold w_sp0, PM_FRAME in Ha. rewrite (proj1 ST2 (Z_to_bv 64 a)) by (rewrite u64_of_Z by lia; unfold zwin; lia). apply AG1. lia. }
    pose proof (x_ms X2) as MS2. clearbody M2.
    eapply srz_msteps; [exact (ms_halt _ MS2) | exact (ms_lazy _ MS2) | | ].
    { norm_pc. stepjr F_69b5c D_69b5c (Z_to_bv 64 ret) ltac:(gres; rewrite J1; reflexivity). apply mst_refl. }
    lazymatch goal with |- srealizes _ (mkCfg (mkst _ ?pc _ _) _) _ => replace pc with (Z_to_bv 64 ret) by (symmetry; exact C2) end.
    eapply (CONT A R2 M2 model 0 X2 BUD); [| rewrite J10; unfold sxw; apply bv_eq; vm_compute; reflexivity | lia | exact AG2 | intros _; exists nwv, nk; split; [exact Cnw | exact Cnk2]].
    intros r Hr. reg_cases r; fixregs_lit; try (exfalso; revert Hr; clear; cbn; intuition discriminate);
      first [ rewrite J2; symmetry; exact C4 | exact J8
            | rewrite (GS2 _) by (clear; in_regs); rewrite GK by (clear; cbn; intuition discriminate); apply GS1; clear; in_regs
            ].
  Qed.
End PM.
