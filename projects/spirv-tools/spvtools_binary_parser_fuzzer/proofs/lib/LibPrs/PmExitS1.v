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
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep2S1.PmUpd. From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PmStep2S1 PmLoopS1 PmBody1S1 PmStep3S1 PmODefsS1 PmBody2S1 PmZw PmOLoopS1 PmStep4S1 PmStep5S1 PmExitDiagS1.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PeLia.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Local Ltac lia ::= pe_lia.
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
  #[local] Notation pm_D7 := (PmExitDiagS1.pm_D7 CL).
  #[local] Notation pm_D8 := (PmExitDiagS1.pm_D8 CL).
  #[local] Notation pm_D9 := (PmExitDiagS1.pm_D9 CL).

  #[local] Notation izero := (PmBody1S1.izero).
  #[local] Notation ictx := (PmBody1S1.ictx).
  #[local] Notation ipure := (PmODefsS1.ipure (G:=G) (idesc:=idesc)).
  #[local] Notation OLI := (PmODefsS1.OLI (MI:=MI) (ST:=ST) (generates_type:=generates_type)).
  #[local] Notation iacc := (PmODefsS1.iacc (generates_type:=generates_type)).
  Definition pm_generates_type := pm_leafA (MI:=MI) (ST:=ST) _ _ _ (cl_generates_type _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
  Definition pm_is_optional := pm_leafA (MI:=MI) (ST:=ST) _ _ _ (cl_is_optional _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
  Definition pm_fpenc := pm_leafA (MI:=MI) (ST:=ST) _ _ _ (cl_fpenc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
  Lemma ext_val_zx2 : forall v, 0 <= v < 2 ^ 16 -> ext_val false 0 2 (Z_to_bv 64 v) = Z_to_bv 64 v.
  Proof using. intros v Hv. apply ext_val_zx_id. rewrite u64_of_Z by lia. cbn. lia. Qed.
  Ltac fixregs2 := fixregs;
    try replace (Z_to_bv 5 (Z.of_N 10)) with (10%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 11)) with (11%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 12)) with (12%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 13)) with (13%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 18)) with (18%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 21)) with (21%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 22)) with (22%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 26)) with (26%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 27)) with (27%bv : reg) in * by (apply bv_eq; reflexivity).
  Lemma mod16_mod8 : forall s k, s mod 16 = 0 -> k mod 8 = 0 -> (s + k) mod 8 = 0.
  Proof using.
    intros s k Hs Hk. apply Z.mod_divide; [lia|]. apply Z.divide_add_r; [| apply Z.mod_divide; [lia | exact Hk]].
    apply Z.mod_divide in Hs; [|lia]. destruct Hs as [q Hq]. exists (2 * q). lia.
  Qed.
  Lemma Z_to_bv64_inj : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> Z_to_bv 64 a = Z_to_bv 64 b -> a = b.
  Proof using.
    intros a b Ha Hb E. apply (f_equal bv_unsigned) in E. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod, !Z.mod_small in E by lia. exact E.
  Qed.

  Definition LOOPK (w : pmw MI ST) (K : TSet) (io : Z) : Prop :=
    forall (fx' : FPState) A' M' model' c' R', frm_zero (@fp_csr fx') -> LI w A' M' model' c' R' -> io < c_widx c' ->
      srealizes SEGS (cfg fx' R' 0x66c78 M' model') K.

  Lemma pm_xtail : forall (w : pmw MI ST) c0 K (fx : FPState) (io : Z) A M model c R,
    PMS w c0 K -> frm_zero (@fp_csr fx) ->
    PMX w A M model c -> c_tr c = [] -> pm_bud (w_n w) c -> oregs w R -> loop_mem w M ->
    c_icount c + 5 <= c_widx c -> c_endian c < 2 -> w_words w <> 0 -> PmLoopS1.nodes c + 1 <= c_widx c + 3 -> PmLoopS1.macct c -> PmLoopS1.lacc c ->
    io < c_widx c -> LOOPK w K io ->
    srealizes SEGS (cfg fx R 0x68360 M model) K.
  Proof using AC MI ST.
    intros w c0 K fx io A M model c R PS FZ X Htr BUD OR LM Hic He2 Hw ACC MACC LACC Hio LK.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & Gc2 & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof (x_scal X) as (Sc1 & Sc2 & Sc3 & Sc4).
    pose proof OR as OR'. destruct OR' as (Qsp & Qgp & Qtp & Qs0 & Qs1 & Qs3 & Qs4 & Qs8).
    pose proof (x_v1 X) as V1. destruct V1 as (_ & _ & _ & V1len & V1blk & V1f0 & V1f1 & _). unfold O_V1 in V1f0, V1f1.
    assert (Rb1 : 0 <= t3a (c_v1 c) /\ t3a (c_v1 c) + OPND_SZ * t3b (c_v1 c) < 2 ^ 64).
    { destruct V1blk as [[Hb0 Hc0]|(Hb1 & _ & _ & Hb2 & _)]; unfold OPND_SZ in *; [rewrite Hb0; lia | lia]. }
    unfold OPND_SZ in V1f1, Rb1. replace (w_p w + 216 + 8) with (w_p w + 224) in V1f1 by lia.
    pm_seed R w c [Z_to_bv 64 (t3a (c_v1 c)); Z_to_bv 64 (t3a (c_v1 c) + 20 * t3b (c_v1 c))].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R. seedHK HK w A M model c E X.
    apply (know_more E M [KWord (SA (EVar 33) 216) (N.to_nat 8) (EVar 39); KWord (SA (EVar 33) 224) (N.to_nat 8) (EVar 40);
                           KWord (SA (EVar 32) 88) (N.to_nat 8) (ELit 0xffffffffcccccccd); KWord (SA (EVar 33) 32) (N.to_nat 8) (ELit 0)]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil.
         - eapply kword_var; [eapply fld_cellw; [exact V1f0 | cbn; lia] | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
         - eapply kword_var; [eapply fld_cellw; [exact V1f1 | cbn; lia] | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
         - eapply kword_var; [eapply (PmBody1S1.loop_mem_cell w _ 88 0xffffffffcccccccd LM); [(first [ solve [cbn [In]; repeat (first [left; reflexivity | right])] | cbn; repeat (first [left; reflexivity | right]) ]) | lia] | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | cbn [edenot]; reflexivity].
         - eapply kword_var; [eapply fld_cellw; [exact (x_insfn X) | cbn; lia] | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | cbn [edenot]; reflexivity]. }
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R1.
    rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (9%bv) G9.
    rreg HRn (18%bv) G18. rreg HRn (21%bv) G21. rreg HRn (22%bv) G22. rreg HRn (26%bv) G26.
    pose proof (syms_id_sound _ _ _ _ OSREGS HRn eq_refl) as GS.
    clear HRn HR HK. fixregs. pose proof (oregs_glue w R R1 OR GS G2 G3 G4 G8 (or_introl G9)) as OR1. clear GS G9.
    rewrite w_add in G18, G21, G22 by lia.
    lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ => set (M1 := m) in * end.
    assert (ST1 : stores_in (zwin (w_sp w + 248) (w_sp w + 258)) M M1) by (unfold M1; stin).
    assert (X1 : PMX w A M1 model c).
    { eapply (pmx_frame_stores SEGS Ly.L MI ST ly_img_low ly_rw_img ly_relro_img w A M M1 model c (zwin (w_sp w + 248) (w_sp w + 258)));
        [exact X | exact ST1 | unfold zwin, w_sp0, PM_FRAME; intros; lia]. }
    eapply (PmBody1S1.loop_mem_frame w M M1) in LM; [| lia | lia | eapply stores_in_agree; [exact ST1 | unfold zwin; intros; lia]].
    clear ST1 MS. clearbody M1. clear X.
    eapply (PmLoopS1.pm_latch_ok w fx A M1 model c R1 K X1 (oregs_loop_regs w R1 OR1 G18 G21 G22) G26).
    intros R2 LR2 Q26. eapply (LK fx A M1 model c R2 FZ); [| exact Hio].
    split; [exact X1|]. split; [exact Htr|]. split; [exact BUD|]. split; [exact LR2|]. split; [exact LM|].
    split; [lia|]. split; [exact He2|]. split; [exact Hw|]. split; [exact ACC|]. split; [exact MACC | exact LACC].
  Qed.

  Lemma oregs_nt_kept : forall (w : pmw MI ST) R R', oregs w R -> nt_kept R R' -> oregs w R'.
  Proof using AC MI ST.
    intros w R R' OR NK. destruct OR as (Q2 & Q3 & Q4 & Q8 & Q9 & Q19 & Q20 & Q24). unfold oregs.
    rewrite !NK by (clear; apply PmStepS1.in_reg_list; reflexivity). repeat split; assumption.
  Qed.

  Lemma w_sltu : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
    alu64 ALU_SLTU (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (if a <? b then 1 else 0).
  Proof using.
    intros a b Ha Hb. cbn [alu64 alu]. unfold bv_ltu. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod, !Z.mod_small by lia.
    destruct (a <? b); reflexivity.
  Qed.

  Definition RNS (w : pmw MI ST) (I : ictxR) A M model c : Prop :=
    PMX w A M model c /\ c_tr c = [] /\ pm_bud (w_n w) c /\ loop_mem w M /\
    (exists rid, cellw SEGS M (w_sp w + 244) 4 rid) /\
    c_icount c + 5 <= c_widx c /\ c_endian c < 2 /\ w_words w <> 0 /\ PmLoopS1.nodes c + 2 <= c_widx c + 3 /\ PmLoopS1.macct c /\
    i_io I + i_iwc I = c_widx c /\
    2 * Zlen (t3c (c_m1 c)) <= c_widx c /\ 3 * Zlen (t3c (c_m3 c)) <= c_widx c /\ 2 * Zlen (t3c (c_m2 c)) <= i_io I.

  Lemma rns_frame : forall (w : pmw MI ST) I A M M' model c (W : Z -> Prop),
    RNS w I A M model c -> stores_in W M M' ->
    (forall a, W a -> (w_sp w + 144 <= a < w_sp w + 244 \/ w_sp w + 248 <= a < w_sp0 w - 104)) ->
    RNS w I A M' model c.
  Proof using AC MI ST.
    intros w I A M M' model c W (X & Htr & BUD & LM & (rid & Crid) & REST) STI HW.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & Gc2 & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    split.
    { eapply (pmx_frame_stores SEGS Ly.L MI ST ly_img_low ly_rw_img ly_relro_img w A M M' model c W); [exact X | exact STI |].
      intros a Ha. unfold zwin, w_sp0, PM_FRAME. destruct (HW a Ha); lia. }
    split; [exact Htr|]. split; [exact BUD|]. split.
    { eapply (PmBody1S1.loop_mem_frame w M M'); [exact LM | lia | lia | eapply stores_in_agree; [exact STI | unfold zwin; intros a Ha; split; [lia | intros HWa; destruct (HW a HWa); lia]]]. }
    split; [| exact REST]. exists rid.
    eapply (PmBody1S1.cellw_frame M M'); [exact Crid | lia | cbn; lia | eapply stores_in_agree; [exact STI | unfold zwin; cbn; intros a Ha; split; [lia | intros HWa; destruct (HW a HWa); lia]]].
  Qed.

  Lemma pm_xh5 : forall (w : pmw MI ST) c0 K (fx : FPState) (I : ictxR) A M model c R (va v2 vc : Z),
    PMS w c0 K -> frm_zero (@fp_csr fx) -> ipure I -> RNS w I A M model c -> oregs w R ->
    getr R 21%bv = Z_to_bv 64 va -> getr R 18%bv = Z_to_bv 64 v2 -> getr R 27%bv = Z_to_bv 64 vc ->
    0 <= va < 2 ^ 32 -> 0 <= v2 < 2 ^ 64 -> 0 <= vc < 2 ^ 32 -> 2 <= i_iwc I -> LOOPK w K (i_io I) ->
    srealizes SEGS (cfg fx R 0x67ed4 M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx I A M model c R va v2 vc PS FZ IP (X & Htr & BUD & LM & (rid & Crid) & Hic & He2 & Hw & ACC & MACC & Hsum & LA1 & LA3 & LA2) OR Q21 Q18 Q27 Rva Rv2 Rvc Hiwc2 LK.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & Gc2 & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof (ipure_ranges I IP) as (Riwc & Rop).
    pose proof (Z.mod_pos_bound v2 (2 ^ 32) ltac:(lia)) as Hm2.
    change (hc_nt_entry HConstsS1.hc) with 0x67ed4 in |- *.
    eapply (pm_h5 w c0 K fx A M model c R rid (va, v2 mod 2 ^ 32, vc) v2 PS FZ X Htr BUD ACC MACC ltac:(lia) OR Q21 Q18 Q27);
      cbn [t3a t3b t3c fst snd]; [lia | lia | lia | lia | reflexivity | exact LM | exact Crid |].
    intros fx' A' R' M' model' m2' FZ' X' BUD' ACC' MACC' ACC2' NK AG.
    change (hc_nt_exit HConstsS1.hc) with 0x68360.
    eapply (pm_xtail w c0 K fx' (i_io I) A' M' model' (PmStep5S1.set_m2 c m2') R' PS FZ' X' ltac:(cbn; exact Htr) BUD' (oregs_nt_kept w R R' OR NK));
      cbn [PmStep5S1.set_m2 c_icount c_widx c_endian]; [| exact Hic | exact He2 | exact Hw | exact ACC' | exact MACC' | | lia | exact LK].
    2: { unfold PmLoopS1.lacc. cbn [PmStep5S1.set_m2 c_m1 c_m2 c_m3 c_widx t3c snd]. lia. }
    eapply (PmBody1S1.loop_mem_frame w M M'); [exact LM | lia | lia | eapply agree_on_weaken; [exact AG | unfold zwin, w_sp0, PM_FRAME; cbn; intros; lia]].
  Qed.

  Definition WIO : expr := EAlu ALU_ADD (EVar 34) (EVar 39).
  Lemma wio_val : forall E words a, ev E 34 = Z_to_bv 64 words -> ev E 39 = Z_to_bv 64 a ->
    0 <= words -> 0 <= a -> words + a < 2 ^ 64 -> edenot E WIO = Z_to_bv 64 (words + a).
  Proof using. intros E words a H34 H39 Hw Ha Hhi. cbn [edenot WIO]. rewrite H34, H39. rewrite w_add by lia. reflexivity. Qed.

  Lemma pm_xrnt_int : forall (w : pmw MI ST) c0 K (fx : FPState) (I : ictxR) A M model c R,
    PMS w c0 K -> frm_zero (@fp_csr fx) -> ipure I -> RNS w I A M model c -> oregs w R ->
    i_op I = OP_TYPE_INT -> 4 <= i_iwc I ->
    getr R 22%bv = Z_to_bv 64 (4 * i_io I) -> LOOPK w K (i_io I) ->
    srealizes SEGS (cfg fx R 0x67e1c M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx I A M model c R PS FZ IP RN OR Hop Hiwc Q22 LK.
    pose proof RN as RN'. destruct RN' as (X & Htr & BUD & LM & _ & Hic & He2 & Hw & ACC & MACC & Hsum & LA1 & LA3 & LA2).
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & Gc2 & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof (x_scal X) as (Sc1 & Sc2 & Sc3 & Sc4). pose proof (ipure_ranges I IP) as (Riwc & Rop).
    pose proof IP as IP'. destruct IP' as (_ & _ & _ & _ & Hg & Hdesc & Rio).
    pose proof OR as OR'. destruct OR' as (Qsp & Qgp & Qtp & Qs0 & Qs1 & Qs3 & Qs4 & Qs8).
    destruct (Gw Hw) as (W1 & W2 & W3 & W4 & W5).

    destruct (mdef_cell4 M (w_words w + 4 * i_io I + 8) ltac:(eapply mdef_sub; [exact (x_wbuf X Hw) | lia | lia]) ltac:(lia) ltac:(lia)) as (w2 & Cw2).
    destruct (mdef_cell4 M (w_words w + 4 * i_io I + 12) ltac:(eapply mdef_sub; [exact (x_wbuf X Hw) | lia | lia]) ltac:(lia) ltac:(lia)) as (w3 & Cw3).
    pose proof (proj1 Cw2) as Rw2. pose proof (proj1 Cw3) as Rw3. cbn in Rw2, Rw3.
    pose proof (fld_cellw M _ 4 _ (x_endian X) ltac:(lia)) as Ce. unfold O_ENDIAN in Ce.
    assert (He32 : 0 <= c_endian c < 2 ^ 32) by lia.

    pm_seed R w c [Z_to_bv 64 (4 * i_io I); Z_to_bv 64 (c_endian c); Z_to_bv 64 w3; Z_to_bv 64 w2].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (22%bv, EVar 39)] R. seedHK HK w A M model c E X.
    assert (AW : edenot E WIO = Z_to_bv 64 (w_words w + 4 * i_io I)) by (apply wio_val; [evs; reflexivity | evs; reflexivity | lia | lia | lia]).
    apply (know_more E M [KWord (SA (EVar 33) 88) (N.to_nat 4) (EVar 40); KWord (SA WIO 12) (N.to_nat 4) (EVar 41); KWord (SA WIO 8) (N.to_nat 4) (EVar 42);
                           KDisj (SA WIO 8) (ELit 8) (SA (EVar 32) 0) (ELit 880); KDisj (SA WIO 8) (ELit 8) (SA (EVar 33) 0) (ELit 288)]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil.
         - eapply kword_var; [exact Ce | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
         - eapply PmBody1S1.kword_expr; [exact Cw3 | cbn; lia | exact AW | lia | lia | cbn; lia | evs; reflexivity].
         - eapply PmBody1S1.kword_expr; [exact Cw2 | cbn; lia | exact AW | lia | lia | cbn; lia | evs; reflexivity].
         - eapply PmBody1S1.kdisj_expr; [exact AW | evs; reflexivity | lia | lia | lia | lia |].
           destruct (W5 (w_words w + 4 * i_io I + 8) ltac:(unfold zwin; lia)) as [Hnw _].
           destruct (W5 (w_words w + 4 * i_io I + 15) ltac:(unfold zwin; lia)) as [Hnw' _]. unfold zwin in Hnw, Hnw'. lia.
         - eapply PmBody1S1.kdisj_expr; [exact AW | evs; reflexivity | lia | lia | lia | lia |].
           destruct (W5 (w_words w + 4 * i_io I + 8) ltac:(unfold zwin; lia)) as [_ Hnp].
           destruct (W5 (w_words w + 4 * i_io I + 15) ltac:(unfold zwin; lia)) as [_ Hnp']. lia. }
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N.
    { split_scs; try sc_auto1. all: try (eapply sc_flat; [exact AW | lia | cbn [a_off]; lia | lia | cbn [a_off]; lia]). }
    postrun. name_run HRn R1.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (9%bv) G9.
    rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (22%bv) G22.
    pose proof (syms_id_sound _ _ _ _ OSREGS HRn eq_refl) as GS.
    clear HRn HR HK AW. fixregs2. pose proof (oregs_glue w R R1 OR GS G2 G3 G4 G8 (or_introl G9)) as OR1. clear GS G9.
    rewrite ext_val_sx4 in G10 by lia. rewrite ext_val_sx4, sx32_small in G11 by lia.
    eapply (pm_fixword w A M model c fx R1 _ K X (ex_intro _ w3 (ex_intro _ (c_endian c) (conj Rw3 (conj G10 (conj He32 G11))))) G1 ltac:(apply bv_eq; vm_compute; reflexivity)).
    intros R2 KEPT (r3 & Rr3 & Hr3). rewrite TablStmts.sx32_prs in Hr3.
    pose proof (oregs_kept w R1 R2 OR1 KEPT) as OR2. keptQ KEPT G2 Qsp_R2. keptQ KEPT G8 Qs0_R2. keptQ KEPT G22 Q22b. clear G1 G2 G3 G4 G8 G10 G11 G22 KEPT OR1.
    pose proof (sx32_range r3 Rr3) as Rsr3.

    pm_seed R2 w c [Z_to_bv 64 (4 * i_io I); Z_to_bv 64 (c_endian c); Z_to_bv 64 w3; Z_to_bv 64 w2; Z_to_bv 64 (PrsNeeds.sx32 r3)].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (22%bv, EVar 39); (10%bv, EVar 43)] R2. seedHK HK w A M model c E X.
    assert (AW : edenot E WIO = Z_to_bv 64 (w_words w + 4 * i_io I)) by (apply wio_val; [evs; reflexivity | evs; reflexivity | lia | lia | lia]).
    apply (know_more E M [KWord (SA (EVar 33) 88) (N.to_nat 4) (EVar 40); KWord (SA WIO 8) (N.to_nat 4) (EVar 42);
                           KDisj (SA WIO 8) (ELit 8) (SA (EVar 32) 0) (ELit 880); KDisj (SA WIO 8) (ELit 8) (SA (EVar 33) 0) (ELit 288)]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil.
         - eapply kword_var; [exact Ce | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
         - eapply PmBody1S1.kword_expr; [exact Cw2 | cbn; lia | exact AW | lia | lia | cbn; lia | evs; reflexivity].
         - eapply PmBody1S1.kdisj_expr; [exact AW | evs; reflexivity | lia | lia | lia | lia |].
           destruct (W5 (w_words w + 4 * i_io I + 8) ltac:(unfold zwin; lia)) as [Hnw _].
           destruct (W5 (w_words w + 4 * i_io I + 15) ltac:(unfold zwin; lia)) as [Hnw' _]. unfold zwin in Hnw, Hnw'. lia.
         - eapply PmBody1S1.kdisj_expr; [exact AW | evs; reflexivity | lia | lia | lia | lia |].
           destruct (W5 (w_words w + 4 * i_io I + 8) ltac:(unfold zwin; lia)) as [_ Hnp].
           destruct (W5 (w_words w + 4 * i_io I + 15) ltac:(unfold zwin; lia)) as [_ Hnp']. lia. }
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N.
    { split_scs; try sc_auto1. all: try (eapply sc_flat; [exact AW | lia | cbn [a_off]; lia | lia | cbn [a_off]; lia]). }
    postrun. name_run HRn R3.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (9%bv) G9.
    rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (21%bv) G21. rreg HRn (22%bv) G22.
    pose proof (syms_id_sound _ _ _ _ OSREGS HRn eq_refl) as GS.
    clear HRn HR HK AW. fixregs2. pose proof (oregs_glue w R2 R3 OR2 GS G2 G3 G4 G8 (or_introl G9)) as OR3. clear GS G9.
    rewrite ext_val_sx4 in G10 by lia. rewrite ext_val_sx4, sx32_small in G11 by lia.
    rewrite w_sltu in G21 by lia. rewrite w_add in G21 by (destruct (0 <? PrsNeeds.sx32 r3); lia).
    set (va := (if 0 <? PrsNeeds.sx32 r3 then 1 else 0) + 1) in G21.
    assert (Rva : 0 <= va < 2 ^ 32) by (subst va; destruct (0 <? PrsNeeds.sx32 r3); lia).
    eapply (pm_fixword w A M model c fx R3 _ K X (ex_intro _ w2 (ex_intro _ (c_endian c) (conj Rw2 (conj G10 (conj He32 G11))))) G1 ltac:(apply bv_eq; vm_compute; reflexivity)).
    intros R4 KEPT (r2 & Rr2 & Hr2). rewrite TablStmts.sx32_prs in Hr2.
    pose proof (oregs_kept w R3 R4 OR3 KEPT) as OR4. keptQ KEPT G2 Qsp_R4. keptQ KEPT G8 Qs0_R4. keptQ KEPT G22 Q22d. keptQ KEPT G21 Q21d. clear G1 G2 G3 G4 G8 G10 G11 G21 G22 KEPT OR3 OR2 Q22b.
    pose proof (sx32_range r2 Rr2) as Rsr2.

    pm_seed R4 w c [Z_to_bv 64 (PrsNeeds.sx32 r2); Z_to_bv 64 va].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (10%bv, EVar 39); (21%bv, EVar 40)] R4. seedHK HK w A M model c E X.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R5.
    rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (9%bv) G9.
    rreg HRn (18%bv) G18. rreg HRn (21%bv) G21. rreg HRn (27%bv) G27.
    pose proof (syms_id_sound _ _ _ _ OSREGS HRn eq_refl) as GS.
    clear HRn HR HK. fixregs2. pose proof (oregs_glue w R4 R5 OR4 GS G2 G3 G4 G8 (or_introl G9)) as OR5. clear GS G9.
    eapply (pm_xh5 w c0 K fx I A M model c R5 va (PrsNeeds.sx32 r2) 0 PS FZ IP RN OR5 G21 G18 G27 Rva Rsr2 ltac:(lia) ltac:(lia) LK).
  Qed.

  Lemma rns_agree : forall (w : pmw MI ST) I A M M' model c (P : Z -> Prop),
    RNS w I A M model c -> PMX w A M' model c -> CRep.agree_on P M M' ->
    (forall a, (w_sp w + 16 <= a < w_sp w + 144 \/ w_sp w + 244 <= a < w_sp w + 248) -> P a) ->
    RNS w I A M' model c.
  Proof using AC MI ST.
    intros w I A M M' model c P (X & Htr & BUD & LM & (rid & Crid) & REST) X' AG HP.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & Gc2 & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    split; [exact X'|]. split; [exact Htr|]. split; [exact BUD|]. split.
    { eapply (PmBody1S1.loop_mem_frame w M M'); [exact LM | lia | lia | eapply agree_on_weaken; [exact AG | unfold zwin; intros a Ha; apply HP; lia]]. }
    split; [| exact REST]. exists rid.
    eapply (PmBody1S1.cellw_frame M M'); [exact Crid | lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold zwin; cbn; intros a Ha; apply HP; lia]].
  Unshelve. all: first [exact SEGS | exact M].
  Qed.

  Lemma pm_xrnt_float : forall (w : pmw MI ST) c0 K (fx : FPState) (I : ictxR) A M model c R,
    PMS w c0 K -> frm_zero (@fp_csr fx) -> ipure I -> RNS w I A M model c -> oregs w R ->
    i_op I = OP_TYPE_FLOAT -> 3 <= i_iwc I -> cellw SEGS M (w_sp w + 232) 2 (i_iwc I) ->
    getr R 22%bv = Z_to_bv 64 (4 * i_io I) -> LOOPK w K (i_io I) ->
    srealizes SEGS (cfg fx R 0x67e58 M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx I A M model c R PS FZ IP RN OR Hop Hiwc C232 Q22 LK.
    pose proof RN as RN'. destruct RN' as (X & Htr & BUD & LM & _ & Hic & He2 & Hw & ACC & MACC & Hsum & LA1 & LA3 & LA2).
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & Gc2 & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof (x_scal X) as (Sc1 & Sc2 & Sc3 & Sc4). pose proof (ipure_ranges I IP) as (Riwc & Rop).
    pose proof IP as IP'. destruct IP' as (_ & _ & _ & _ & Hg & Hdesc & Rio).
    pose proof OR as OR'. destruct OR' as (Qsp & Qgp & Qtp & Qs0 & Qs1 & Qs3 & Qs4 & Qs8).
    destruct (Gw Hw) as (W1 & W2 & W3 & W4 & W5).
    destruct (mdef_cell4 M (w_words w + 4 * i_io I + 8) ltac:(eapply mdef_sub; [exact (x_wbuf X Hw) | lia | lia]) ltac:(lia) ltac:(lia)) as (w2 & Cw2).
    pose proof (proj1 Cw2) as Rw2. cbn in Rw2.
    pose proof (fld_cellw M _ 4 _ (x_endian X) ltac:(lia)) as Ce. unfold O_ENDIAN in Ce.
    assert (He32 : 0 <= c_endian c < 2 ^ 32) by lia.

    pm_seed R w c [Z_to_bv 64 (4 * i_io I); Z_to_bv 64 (c_endian c); Z_to_bv 64 w2].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (22%bv, EVar 39)] R. seedHK HK w A M model c E X.
    assert (AW : edenot E WIO = Z_to_bv 64 (w_words w + 4 * i_io I)) by (apply wio_val; [evs; reflexivity | evs; reflexivity | lia | lia | lia]).
    apply (know_more E M [KWord (SA (EVar 33) 88) (N.to_nat 4) (EVar 40); KWord (SA WIO 8) (N.to_nat 4) (EVar 41);
                           KDisj (SA WIO 8) (ELit 4) (SA (EVar 32) 0) (ELit 880); KDisj (SA WIO 8) (ELit 4) (SA (EVar 33) 0) (ELit 288)]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil.
         - eapply kword_var; [exact Ce | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
         - eapply PmBody1S1.kword_expr; [exact Cw2 | cbn; lia | exact AW | lia | lia | cbn; lia | evs; reflexivity].
         - eapply PmBody1S1.kdisj_expr; [exact AW | evs; reflexivity | lia | lia | lia | lia |].
           destruct (W5 (w_words w + 4 * i_io I + 8) ltac:(unfold zwin; lia)) as [Hnw _].
           destruct (W5 (w_words w + 4 * i_io I + 11) ltac:(unfold zwin; lia)) as [Hnw' _]. unfold zwin in Hnw, Hnw'. lia.
         - eapply PmBody1S1.kdisj_expr; [exact AW | evs; reflexivity | lia | lia | lia | lia |].
           destruct (W5 (w_words w + 4 * i_io I + 8) ltac:(unfold zwin; lia)) as [_ Hnp].
           destruct (W5 (w_words w + 4 * i_io I + 11) ltac:(unfold zwin; lia)) as [_ Hnp']. lia. }
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N.
    { split_scs; try sc_auto1. all: try (eapply sc_flat; [exact AW | lia | cbn [a_off]; lia | lia | cbn [a_off]; lia]). }
    postrun. name_run HRn R1.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (9%bv) G9.
    rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (22%bv) G22.
    pose proof (syms_id_sound _ _ _ _ OSREGS HRn eq_refl) as GS.
    clear HRn HR HK AW. fixregs2. pose proof (oregs_glue w R R1 OR GS G2 G3 G4 G8 (or_introl G9)) as OR1. clear GS G9.
    rewrite ext_val_sx4 in G10 by lia. rewrite ext_val_sx4, sx32_small in G11 by lia.
    eapply (pm_fixword w A M model c fx R1 _ K X (ex_intro _ w2 (ex_intro _ (c_endian c) (conj Rw2 (conj G10 (conj He32 G11))))) G1 ltac:(apply bv_eq; vm_compute; reflexivity)).
    intros R2 KEPT (r2 & Rr2 & Hr2). rewrite TablStmts.sx32_prs in Hr2.
    pose proof (oregs_kept w R1 R2 OR1 KEPT) as OR2. keptQ KEPT G2 Qsp_R2. keptQ KEPT G8 Qs0_R2. keptQ KEPT G22 Q22b. clear G1 G2 G3 G4 G8 G10 G11 G22 KEPT OR1.
    pose proof (sx32_range r2 Rr2) as Rsr2.

    destruct (Z.le_gt_cases (i_iwc I) 3) as [Hle3 | Hge4].
    -
      pm_seed R2 w c [Z_to_bv 64 (PrsNeeds.sx32 r2); Z_to_bv 64 (i_iwc I)].
      seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (10%bv, EVar 39)] R2. seedHK HK w A M model c E X.
      apply (know_more E M [KWord (SA (EVar 32) 232) (N.to_nat 2) (EVar 40); KRange (EVar 40) 3 3]) in HK.
      2: { repeat apply Forall_cons; try apply Forall_nil.
           - eapply kword_var; [exact C232 | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
           - eapply krange_var; [evs; reflexivity | lia | lia]. }
      xruns HR HK 100%nat STOPS (SCR [true] [] []) 50%N.
      { split_scs; try sc_auto1. all: cbn [sc_denot]; evs; rewrite ?ext_val_zx2 by lia; rewrite ?br_geu, ?br_ltu by lia; try bool_lia. }
      postrun. name_run HRn R3.
      rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (9%bv) G9.
      rreg HRn (18%bv) G18. rreg HRn (21%bv) G21. rreg HRn (27%bv) G27.
      pose proof (syms_id_sound _ _ _ _ OSREGS HRn eq_refl) as GS.
      clear HRn HR HK. fixregs2. pose proof (oregs_glue w R2 R3 OR2 GS G2 G3 G4 G8 (or_introl G9)) as OR3. clear GS G9.
      eapply (pm_xh5 w c0 K fx I A M model c R3 3 (PrsNeeds.sx32 r2) 0 PS FZ IP RN OR3 G21 G18 G27 ltac:(lia) Rsr2 ltac:(lia) ltac:(lia) LK).
    -
      destruct (mdef_cell4 M (w_words w + 4 * i_io I + 12) ltac:(eapply mdef_sub; [exact (x_wbuf X Hw) | lia | lia]) ltac:(lia) ltac:(lia)) as (w3 & Cw3).
      pose proof (proj1 Cw3) as Rw3. cbn in Rw3.
      pm_seed R2 w c [Z_to_bv 64 (4 * i_io I); Z_to_bv 64 (c_endian c); Z_to_bv 64 w3; Z_to_bv 64 (PrsNeeds.sx32 r2); Z_to_bv 64 (i_iwc I)].
      seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (22%bv, EVar 39); (10%bv, EVar 42)] R2. seedHK HK w A M model c E X.
      assert (AW : edenot E WIO = Z_to_bv 64 (w_words w + 4 * i_io I)) by (apply wio_val; [evs; reflexivity | evs; reflexivity | lia | lia | lia]).
      apply (know_more E M [KWord (SA (EVar 32) 232) (N.to_nat 2) (EVar 43); KRange (EVar 43) 4 (2 ^ 16 - 1);
                             KWord (SA (EVar 33) 88) (N.to_nat 4) (EVar 40); KWord (SA WIO 12) (N.to_nat 4) (EVar 41);
                             KDisj (SA WIO 12) (ELit 4) (SA (EVar 32) 0) (ELit 880); KDisj (SA WIO 12) (ELit 4) (SA (EVar 33) 0) (ELit 288)]) in HK.
      2: { repeat apply Forall_cons; try apply Forall_nil.
           - eapply kword_var; [exact C232 | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
           - eapply krange_var; [evs; reflexivity | lia | lia].
           - eapply kword_var; [exact Ce | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
           - eapply PmBody1S1.kword_expr; [exact Cw3 | cbn; lia | exact AW | lia | lia | cbn; lia | evs; reflexivity].
           - eapply PmBody1S1.kdisj_expr; [exact AW | evs; reflexivity | lia | lia | lia | lia |].
             destruct (W5 (w_words w + 4 * i_io I + 12) ltac:(unfold zwin; lia)) as [Hnw _].
             destruct (W5 (w_words w + 4 * i_io I + 15) ltac:(unfold zwin; lia)) as [Hnw' _]. unfold zwin in Hnw, Hnw'. lia.
           - eapply PmBody1S1.kdisj_expr; [exact AW | evs; reflexivity | lia | lia | lia | lia |].
             destruct (W5 (w_words w + 4 * i_io I + 12) ltac:(unfold zwin; lia)) as [_ Hnp].
             destruct (W5 (w_words w + 4 * i_io I + 15) ltac:(unfold zwin; lia)) as [_ Hnp']. lia. }
      xruns HR HK 100%nat STOPS (SCR [false] [] []) 50%N.
      { split_scs; try sc_auto1. all: cbn [sc_denot]; evs; rewrite ?ext_val_zx2 by lia; rewrite ?br_geu, ?br_ltu by lia; try bool_lia.
        all: try (eapply sc_flat; [exact AW | lia | cbn [a_off]; lia | lia | cbn [a_off]; lia]). }
      postrun. name_run HRn R3.
      rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (9%bv) G9.
      rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (18%bv) G18. rreg HRn (21%bv) G21. rreg HRn (22%bv) G22.
      pose proof (syms_id_sound _ _ _ _ OSREGS HRn eq_refl) as GS.
      clear HRn HR HK AW. fixregs2. pose proof (oregs_glue w R2 R3 OR2 GS G2 G3 G4 G8 (or_introl G9)) as OR3. clear GS G9.
      rewrite ext_val_sx4 in G10 by lia. rewrite ext_val_sx4, sx32_small in G11 by lia.
      lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ => set (M1 := m) in * end.
      assert (ST1 : stores_in (zwin (w_sp w + 272) (w_sp w + 280)) M M1) by (unfold M1; stin).
      assert (RN1 : RNS w I A M1 model c) by (eapply (rns_frame w I A M M1 model c _ RN ST1); unfold zwin, w_sp0, PM_FRAME; intros; lia).
      pose proof RN1 as RN1'. destruct RN1' as (X1 & _).
      clear ST1 MS. clearbody M1. clear X RN Ce Cw2 Cw3 C232. pose proof (x_ms X1) as MS1.
      eapply (pm_fixword w A M1 model c fx R3 _ K X1 (ex_intro _ w3 (ex_intro _ (c_endian c) (conj Rw3 (conj G10 (conj He32 G11))))) G1 ltac:(apply bv_eq; vm_compute; reflexivity)).
      intros R4 KEPT (r3 & Rr3 & Hr3). rewrite TablStmts.sx32_prs in Hr3.
      pose proof (oregs_kept w R3 R4 OR3 KEPT) as OR4. keptQ KEPT G2 Qsp_R4. keptQ KEPT G8 Qs0_R4. keptQ KEPT G18 Q18d. keptQ KEPT G21 Q21d. clear G1 G2 G3 G4 G8 G10 G11 G18 G21 G22 KEPT OR3 OR2.
      pose proof (sx32_range r3 Rr3) as Rsr3.

      pm_seed R4 w c [Z_to_bv 64 (PrsNeeds.sx32 r3)].
      seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (10%bv, EVar 39)] R4. seedHK HK w A M1 model c E X1.
      xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
      postrun. name_run HRn R5.
      rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (9%bv) G9.
      rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12. rreg HRn (18%bv) G18. rreg HRn (21%bv) G21.
      pose proof (syms_id_sound _ _ _ _ OSREGS HRn eq_refl) as GS.
      clear HRn HR HK. fixregs2. pose proof (oregs_glue w R4 R5 OR4 GS G2 G3 G4 G8 (or_introl G9)) as OR5. clear GS G9.
      rewrite w_add in G12 by lia. rewrite Q18d in G18. rewrite Q21d in G21.
      eapply (pm_lookup_operand w A M1 model c fx R5 34 r3 (w_sp w + 272) 0x67ea4 K X1 G10 ltac:(lia)
                ltac:(intros XX; discriminate XX) ltac:(intros _; split; [rewrite TablStmts.sx32_prs; exact G11 | split; [exact Rr3 | exact G12]]) G2
                ltac:(lia) ltac:(unfold w_sp0, PM_FRAME; lia) ltac:(apply mod16_mod8; [exact Gsp16 | reflexivity])
                G1 ltac:(apply bv_eq; vm_compute; reflexivity)).
      intros R6 M2 r d KEPT Ga0 Rr Fd Hfound Hdesc2 X2 AG.
      assert (RN2 : RNS w I A M2 model c) by (eapply (rns_agree w I A M1 M2 model c _ RN1 X2 AG); unfold zwin, w_sp0, PM_FRAME; intros; lia).
      pose proof (oregs_kept w R5 R6 OR5 KEPT) as OR6. keptQ KEPT G2 Qsp_R6. keptQ KEPT G8 Qs0_R6. keptQ KEPT G18 Q18f. keptQ KEPT G21 Q21f. keptQ KEPT G2 Qsp6. keptQ KEPT G8 Qs06.
      clear G1 G2 G3 G4 G8 G10 G11 G12 G18 G21 KEPT OR5 OR4 Q18d Q21d.
      pose proof (x_ms X2) as MS2.

      destruct (Z.eq_dec r 0) as [-> | Hr0].
      + pose proof (Hdesc2 eq_refl) as HD.
        destruct ((cl_odesc_value _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL) d 34 r3 M2 HD (x_roc X2)) as (Fv & Hd1 & Hd2).
        pose proof (fld_cellw M2 _ 4 _ Fv ltac:(lia)) as Cv.
        pm_seed R6 w c [Z_to_bv 64 d; Z_to_bv 64 r3].
        seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (10%bv, ELit 0)] R6. seedHK HK w A M2 model c E X2.
        apply (know_more E M2 [KWord (SA (EVar 32) 272) (N.to_nat 8) (EVar 39); KWord (SA (EVar 39) 0) (N.to_nat 4) (EVar 40); KRange (EVar 39) 0x10000 (2 ^ 47)]) in HK.
        2: { repeat apply Forall_cons; try apply Forall_nil.
             - eapply kword_var; [eapply fld_cellw; [exact Fd | cbn; lia] | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
             - eapply kword_var; [rewrite Z.add_0_r; exact Cv | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
             - eapply krange_var; [evs; reflexivity | lia | lia]. }
        xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
        postrun. name_run HRn R7.
        rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (9%bv) G9.
        rreg HRn (18%bv) G18. rreg HRn (21%bv) G21.
        pose proof (syms_id_sound _ _ _ _ OSREGS HRn eq_refl) as GS.
        clear HRn HR HK. fixregs2. pose proof (oregs_glue w R6 R7 OR6 GS G2 G3 G4 G8 (or_introl G9)) as OR7. clear GS G9.
        rewrite Q18f in G18. rewrite Q21f in G21.
        eapply (pm_fpenc w A M2 model c fx R7 _ K X2 Logic.I G1 ltac:(apply bv_eq; vm_compute; reflexivity)).
        intros R8 KEPT (r11 & Rr11 & Ga0'). pose proof (oregs_kept w R7 R8 OR7 KEPT) as OR8. keptQ KEPT G2 Qsp_R8. keptQ KEPT G8 Qs0_R8. keptQ KEPT G18 Q18h. keptQ KEPT G21 Q21h.
        clear G1 G2 G3 G4 G8 G18 G21 KEPT OR7.

        pm_seed R8 w c [Z_to_bv 64 r11].
        seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (10%bv, EVar 39)] R8. seedHK HK w A M2 model c E X2.
        xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
        postrun. name_run HRn R9.
        rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (9%bv) G9.
        rreg HRn (18%bv) G18. rreg HRn (21%bv) G21. rreg HRn (27%bv) G27.
        pose proof (syms_id_sound _ _ _ _ OSREGS HRn eq_refl) as GS.
        clear HRn HR HK. fixregs2. pose proof (oregs_glue w R8 R9 OR8 GS G2 G3 G4 G8 (or_introl G9)) as OR9. clear GS G9.
        rewrite Q18h in G18. rewrite Q21h in G21.
        eapply (pm_xh5 w c0 K fx I A M2 model c R9 3 (PrsNeeds.sx32 r2) r11 PS FZ IP RN2 OR9 G21 G18 G27 ltac:(lia) Rsr2 Rr11 ltac:(lia) LK).
      +
        pm_seed R6 w c [Z_to_bv 64 r].
        seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (10%bv, EVar 39)] R6. seedHK HK w A M2 model c E X2.
        apply (know_more E M2 [KRange (EVar 39) 1 (2 ^ 64 - 1)]) in HK.
        2: { repeat apply Forall_cons; try apply Forall_nil. eapply krange_var; [evs; reflexivity | lia | lia]. }
        xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
        postrun. name_run HRn R7.
        rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (9%bv) G9.
        rreg HRn (18%bv) G18. rreg HRn (21%bv) G21. rreg HRn (27%bv) G27.
        pose proof (syms_id_sound _ _ _ _ OSREGS HRn eq_refl) as GS.
        clear HRn HR HK. fixregs2. pose proof (oregs_glue w R6 R7 OR6 GS G2 G3 G4 G8 (or_introl G9)) as OR7. clear GS G9.
        rewrite Q18f in G18. rewrite Q21f in G21.
        eapply (pm_xh5 w c0 K fx I A M2 model c R7 3 (PrsNeeds.sx32 r2) 0 PS FZ IP RN2 OR7 G21 G18 G27 ltac:(lia) Rsr2 ltac:(lia) ltac:(lia) LK).
  Unshelve. all: first [exact SEGS | exact M].
  Qed.

  Lemma pm_xrnt : forall (w : pmw MI ST) c0 K (fx : FPState) (I : ictxR) A M model c R (pw : Z),
    PMS w c0 K -> frm_zero (@fp_csr fx) -> ipure I ->
    PMX w A M model c -> c_tr c = [] -> pm_bud (w_n w) c -> oregs w R -> loop_mem w M ->
    ictx w M (i_io I) (i_fw I) (i_iwc I) (i_op I) (i_d I) -> ifr w M ->
    c_icount c + 4 <= i_io I -> c_endian c < 2 -> w_words w <> 0 -> PmLoopS1.nodes c + 2 <= c_widx c + 3 -> PmLoopS1.macct c ->
    i_io I + i_iwc I = c_widx c ->
    2 * Zlen (t3c (c_m1 c)) <= c_widx c -> 3 * Zlen (t3c (c_m3 c)) <= c_widx c -> 2 * Zlen (t3c (c_m2 c)) <= i_io I ->
    (generates_type (i_op I) = true -> 2 <= i_iwc I) ->
    (i_op I = OP_TYPE_INT -> 4 <= i_iwc I) -> (i_op I = OP_TYPE_FLOAT -> 3 <= i_iwc I) ->
    getr R 11%bv = Z_to_bv 64 pw -> 0 <= pw < 2 ^ 64 -> getr R 10%bv = Z_to_bv 64 (i_iwc I) -> getr R 22%bv = Z_to_bv 64 (4 * i_io I) ->
    LOOPK w K (i_io I) ->
    srealizes SEGS (cfg fx R 0x67df4 M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx I A M model c R pw PS FZ IP X Htr BUD OR LM IC IFR Hic He2 Hw ACC MACC Hsum LA1 LA3 LA2 HG5 HInt HFlt Q11 Rpw Q10 Q22 LK.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & Gc2 & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof (x_scal X) as (Sc1 & Sc2 & Sc3 & Sc4). pose proof (ipure_ranges I IP) as (Riwc & Rop).
    pose proof OR as OR'. destruct OR' as (Qsp & Qgp & Qtp & Qs0 & Qs1 & Qs3 & Qs4 & Qs8).
    pose proof IC as IC'. destruct IC' as (Cio & Cfw & Ciwc & Cop & Fd).
    destruct IFR as (ext & tid & rid & _ & _ & _ & _ & Crid & _).

    pm_seed R w c [Z_to_bv 64 pw; Z_to_bv 64 (i_iwc I); Z_to_bv 64 (4 * i_io I); Z_to_bv 64 (i_op I)].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (11%bv, EVar 39); (10%bv, EVar 40); (22%bv, EVar 41)] R. seedHK HK w A M model c E X.
    apply (know_more E M [KWord (SA (EVar 32) 234) (N.to_nat 2) (EVar 42)]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil.
         eapply kword_var; [exact Cop | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity]. }
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R1.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (9%bv) G9.
    rreg HRn (10%bv) G10. rreg HRn (21%bv) G21. rreg HRn (22%bv) G22.
    pose proof (syms_id_sound _ _ _ _ OSREGS HRn eq_refl) as GS.
    clear HRn HR HK. fixregs2. pose proof (oregs_glue w R R1 OR GS G2 G3 G4 G8 (or_introl G9)) as OR1. clear GS G9.
    rewrite ?ext_val_zx2 in G10, G21 by lia.
    lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ => set (M1 := m) in * end.
    assert (ST1 : stores_in (zwin (w_sp w + 224) (w_sp w + 234)) M M1) by (unfold M1; stin).
    assert (C232 : cellw SEGS M1 (w_sp w + 232) 2 (i_iwc I)) by (split; [cbn; lia | unfold M1; rdback]).
    assert (RN1 : RNS w I A M1 model c).
    { split.
      { eapply (pmx_frame_stores SEGS Ly.L MI ST ly_img_low ly_rw_img ly_relro_img w A M M1 model c (zwin (w_sp w + 224) (w_sp w + 234)));
          [exact X | exact ST1 | unfold zwin, w_sp0, PM_FRAME; intros; lia]. }
      split; [exact Htr|]. split; [exact BUD|]. split.
      { eapply (PmBody1S1.loop_mem_frame w M M1); [exact LM | lia | lia | eapply stores_in_agree; [exact ST1 | unfold zwin; intros; lia]]. }
      split. { exists rid. eapply (PmBody1S1.cellw_frame M M1); [exact Crid | lia | cbn; lia | eapply stores_in_agree; [exact ST1 | unfold zwin; cbn; intros; lia]]. }
      repeat match goal with |- _ /\ _ => split end; first [assumption | lia]. }
    pose proof RN1 as RN1'. destruct RN1' as (X1 & _ & _ & LM1 & _).
    clear ST1 MS. clearbody M1. clear X LM Cio Cfw Ciwc Cop Fd Crid.
    assert (Rop32 : 0 <= i_op I < 2 ^ 32) by lia.
    eapply (pm_generates_type w A M1 model c fx R1 _ K X1 (ex_intro _ (i_op I) (conj Rop32 G10)) G1 ltac:(apply bv_eq; vm_compute; reflexivity)).
    intros R2 KEPT (b & Gb & Hb). pose proof (oregs_kept w R1 R2 OR1 KEPT) as OR2. keptQ KEPT G2 Qsp_R2. keptQ KEPT G8 Qs0_R2.
    keptQ KEPT G21 Q21b. keptQ KEPT G22 Q22b. clear G1 G2 G3 G4 G8 G21 G22 KEPT OR1.
    pose proof (x_ms X1) as MS1.
    destruct b; cbn in Gb.
    -
      destruct (Hb eq_refl) as (x' & Rx' & Gx' & Hgt). rewrite G10 in Gx'. apply Z_to_bv64_inj in Gx'; [| lia | lia]. subst x'.
      pose proof (HG5 Hgt) as Hiwc2.
      destruct (Z.eq_dec (i_op I) OP_TYPE_FLOAT) as [HopF | HnF]; [| destruct (Z.eq_dec (i_op I) OP_TYPE_INT) as [HopI | HnI]].
      +
        pose proof Q21b as Q21F. rewrite HopF in Q21F. unfold OP_TYPE_FLOAT in Q21F.
        pm_seed R2 w c [Z_to_bv 64 (4 * i_io I)].
        seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (10%bv, ELit 1); (21%bv, ELit 22); (22%bv, EVar 39)] R2. seedHK HK w A M1 model c E X1.
        xruns HR HK 100%nat (0x67e1c :: 0x67e58 :: 0x68360 :: STOPS) (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
        postrun. name_run HRn R3.
        rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (9%bv) G9. rreg HRn (22%bv) G22.
        pose proof (syms_id_sound _ _ _ _ OSREGS HRn eq_refl) as GS.
        clear HRn HR HK. fixregs2. pose proof (oregs_glue w R2 R3 OR2 GS G2 G3 G4 G8 (or_introl G9)) as OR3. clear GS G9.
        eapply (pm_xrnt_float w c0 K fx I A M1 model c R3 PS FZ IP RN1 OR3 HopF (HFlt HopF) C232 G22 LK).
      +
        pose proof Q21b as Q21I. rewrite HopI in Q21I. unfold OP_TYPE_INT in Q21I.
        pm_seed R2 w c [Z_to_bv 64 (4 * i_io I)].
        seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (10%bv, ELit 1); (21%bv, ELit 21); (22%bv, EVar 39)] R2. seedHK HK w A M1 model c E X1.
        xruns HR HK 100%nat (0x67e1c :: 0x67e58 :: 0x68360 :: STOPS) (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
        postrun. name_run HRn R3.
        rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (9%bv) G9. rreg HRn (22%bv) G22.
        pose proof (syms_id_sound _ _ _ _ OSREGS HRn eq_refl) as GS.
        clear HRn HR HK. fixregs2. pose proof (oregs_glue w R2 R3 OR2 GS G2 G3 G4 G8 (or_introl G9)) as OR3. clear GS G9.
        eapply (pm_xrnt_int w c0 K fx I A M1 model c R3 PS FZ IP RN1 OR3 HopI (HInt HopI) G22 LK).
      +
        pm_seed R2 w c [Z_to_bv 64 (i_op I)].
        seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (10%bv, ELit 1); (21%bv, EVar 39)] R2. seedHK HK w A M1 model c E X1.
        apply (know_more E M1 [KRange (EVar 39) 0 (2 ^ 16)]) in HK.
        2: { repeat apply Forall_cons; try apply Forall_nil. eapply krange_var; [evs; reflexivity | lia | lia]. }
        xruns HR HK 100%nat (0x67e1c :: 0x67e58 :: 0x68360 :: STOPS) (SCR [false; true] [] []) 50%N.
        { split_scs; try sc_auto1. all: cbn [sc_denot]; evs; unfold OP_TYPE_INT, OP_TYPE_FLOAT in HnF, HnI; rewrite ?br_eq, ?br_ne by lia; try bool_lia. }
        postrun. name_run HRn R3.
        rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (9%bv) G9.
        rreg HRn (18%bv) G18. rreg HRn (21%bv) G21. rreg HRn (27%bv) G27.
        pose proof (syms_id_sound _ _ _ _ OSREGS HRn eq_refl) as GS.
        clear HRn HR HK. fixregs2. pose proof (oregs_glue w R2 R3 OR2 GS G2 G3 G4 G8 (or_introl G9)) as OR3. clear GS G9.
        eapply (pm_xh5 w c0 K fx I A M1 model c R3 0 0 0 PS FZ IP RN1 OR3 G21 G18 G27 ltac:(lia) ltac:(lia) ltac:(lia) Hiwc2 LK).
    -
      pm_seed R2 w c (@nil word).
      seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (10%bv, ELit 0)] R2. seedHK HK w A M1 model c E X1.
      xruns HR HK 100%nat (0x67e1c :: 0x67e58 :: 0x68360 :: STOPS) (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
      postrun. name_run HRn R3.
      rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (9%bv) G9.
      pose proof (syms_id_sound _ _ _ _ OSREGS HRn eq_refl) as GS.
      clear HRn HR HK. fixregs2. pose proof (oregs_glue w R2 R3 OR2 GS G2 G3 G4 G8 (or_introl G9)) as OR3. clear GS G9.
      destruct RN1 as (_ & _ & _ & _ & _ & Hic5 & _ & _ & ACC2 & MACC1 & _).
      eapply (pm_xtail w c0 K fx (i_io I) A M1 model c R3 PS FZ X1 Htr BUD OR3 LM1 Hic5 He2 Hw ltac:(lia) MACC1 ltac:(unfold PmLoopS1.lacc; lia) ltac:(lia) LK).
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

  Lemma oli_regs : forall (w : pmw MI ST) I A M model c R R', OLI w I A M model c R -> oregs w R' -> OLI w I A M model c R'.
  Proof using AC MI ST generates_type.
    intros w I A M model c R R' (OB & REST) OR'. split; [| exact REST].
    destruct OB as (X & Htr & BUD & OR & REST2). split; [exact X|]. split; [exact Htr|]. split; [exact BUD|]. split; [exact OR' | exact REST2].
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

#[local] Definition HTPmExitS1_0 : list (reg * expr) := [(2%bv, EVar 32); (8%bv, EVar 33); (11%bv, EVar 38); (22%bv, EVar 38); (21%bv, EVar 39); (10%bv, EVar 40)].
  Lemma pm_x679b8 : forall (w : pmw MI ST) c0 K (fx : FPState) (I : ictxR) A M model c R,
    PMS w c0 K -> frm_zero (@fp_csr fx) -> ipure I -> OLI w I A M model c R ->
    i_io I + i_iwc I <= c_widx c ->
    (t3b (c_v3 c) = [] \/ (t3b (c_v3 c) <> [] /\ 42 <= last (t3b (c_v3 c)) 0)) ->
    getr R 11%bv = Z_to_bv 64 (i_io I + i_iwc I) -> getr R 22%bv = Z_to_bv 64 (c_widx c) ->
    getr R 21%bv = Z_to_bv 64 (i_io I) -> getr R 10%bv = Z_to_bv 64 (i_iwc I) ->
    LOOPK w K (i_io I) ->
    srealizes SEGS (cfg fx R 0x67a5c M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx I A M model c R PS FZ IP HOLI Hle Hopt Q11 Q22 Q21 Q10 LK.
    pose proof HOLI as HOLI'. destruct HOLI' as (OB & Hw1 & ACC & CNT & V2L & V3L & ZW & HTY & IACC).
    pose proof OB as OB'. destruct OB' as (X & Htr & BUD & OR & LM & IC & IFR & Hic & He2 & Hw & MACC & FR3).
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & Gc2 & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof (x_scal X) as (Sc1 & Sc2 & Sc3 & Sc4). pose proof (ipure_ranges I IP) as (Riwc & Rop).
    pose proof IP as IP'. destruct IP' as (_ & _ & _ & _ & Hg & Hdesc & Rio).
    pose proof OR as OR'. destruct OR' as (Qsp & Qgp & Qtp & Qs0 & Qs1 & Qs3 & Qs4 & Qs8).
    destruct (Z.eq_dec (i_io I + i_iwc I) (c_widx c)) as [Hsum | Hne].
    2: {
         pm_seed R w c [Z_to_bv 64 (i_io I + i_iwc I)].
         seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (11%bv, EVar 39); (22%bv, EVar 38)] R. seedHK HK w A M model c E X.
         apply (know_more E M [KRange (EVar 39) 0 (2 ^ 24)]) in HK.
         2: { repeat apply Forall_cons; try apply Forall_nil. eapply krange_var; [evs; reflexivity | lia | lia]. }
         xruns HR HK 100%nat (0x67bc0 :: 0x67df4 :: STOPS) (SCR [true] [] []) 50%N.
         { split_scs; try sc_auto1. all: cbn [sc_denot]; evs; rewrite ?br_eq, ?br_ne by lia; try bool_lia. }
         postrun. name_run HRn R1.
         rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (9%bv) G9.
         pose proof (syms_id_sound _ _ _ _ OSREGS HRn eq_refl) as GS.
         clear HRn HR HK. fixregs2. pose proof (oregs_glue w R R1 OR GS G2 G3 G4 G8 (or_introl G9)) as OR1. clear GS G9.
         exact (pm_D9 w c0 K fx I A M model c R1 PS FZ IP (oli_regs w I A M model c R R1 HOLI OR1)). }

    pose proof (nty_exit (i_op I) (t3b (c_v3 c)) (c_widx c - i_io I) HTY) as NTX.
    assert (HInt : i_op I = OP_TYPE_INT -> 4 <= i_iwc I) by (intros Hop; destruct (NTX (or_introl Hop) Hopt) as [H4 _]; specialize (H4 Hop); lia).
    assert (HFlt : i_op I = OP_TYPE_FLOAT -> 3 <= i_iwc I) by (intros Hop; destruct (NTX (or_intror Hop) Hopt) as [_ H3]; lia).
    destruct (iacc_exit I c IACC Hw1 Hopt) as (LA1 & LA3 & LA2 & HG5).
    rewrite Hsum in Q11.
    pose proof (flags_lo_byte M (w_p w) (c_reqconv c) (x_flags X) Sc4) as Crc.
    pose proof (x_v2 X) as V2. destruct V2 as (_ & _ & _ & V2len & V2blk & V2f0 & _). unfold O_V2 in V2f0.
    assert (Rb2 : 0 <= t3a (c_v2 c) < 2 ^ 64) by (destruct V2blk as [[-> _]|(Hb & _ & _ & Hbc & _)]; [lia | lia]).
    destruct Sc4 as [Hrc | Hrc]; rewrite Hrc in Crc.
    -
      pm_seed R w c [Z_to_bv 64 (i_io I); Z_to_bv 64 (i_iwc I)].
      seedHR HR E HTPmExitS1_0 R. seedHK HK w A M model c E X.
      apply (know_more E M [KWord (SA (EVar 33) 92) (N.to_nat 1) (ELit 0); KRange (EVar 39) 0 (2 ^ 24)]) in HK.
      2: { repeat apply Forall_cons; try apply Forall_nil.
           - eapply kword_var; [exact Crc | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | cbn [edenot]; reflexivity].
           - eapply krange_var; [evs; reflexivity | lia | lia]. }
      xruns HR HK 100%nat (0x67bc0 :: 0x67df4 :: STOPS) (SCR [] [] []) 50%N.
      { split_scs; try sc_auto1. all: cbn [sc_denot]; evs; rewrite ?br_eq, ?br_ne by lia; try bool_lia. }
      postrun. name_run HRn R1.
      rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (9%bv) G9.
      rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (22%bv) G22.
      pose proof (syms_id_sound _ _ _ _ OSREGS HRn eq_refl) as GS.
      clear HRn HR HK. fixregs2. pose proof (oregs_glue w R R1 OR GS G2 G3 G4 G8 (or_introl G9)) as OR1. clear GS G9.
      rewrite ?PmExitDiagS1.w_mul_lit, ?SymExec.alu64_add_lit in G22. rewrite ?PmExitDiagS1.w_mul_lit in G11. rewrite ?w_add in G11 by lia.
      replace (i_io I * 4) with (4 * i_io I) in G11, G22 by lia.
      eapply (pm_xrnt w c0 K fx I A M model c R1 (w_words w + 4 * i_io I) PS FZ IP X Htr BUD OR1 LM IC IFR Hic He2 Hw ACC MACC Hsum LA1 LA3 LA2 ltac:(intros Hgt; specialize (HG5 Hgt); lia) HInt HFlt G11 ltac:(lia) G10 G22 LK).
    -
      pm_seed R w c [Z_to_bv 64 (i_io I); Z_to_bv 64 (i_iwc I); Z_to_bv 64 (t3a (c_v2 c))].
      seedHR HR E HTPmExitS1_0 R. seedHK HK w A M model c E X.
      apply (know_more E M [KWord (SA (EVar 33) 92) (N.to_nat 1) (ELit 1); KRange (EVar 39) 0 (2 ^ 24); KWord (SA (EVar 33) 240) (N.to_nat 8) (EVar 41)]) in HK.
      2: { repeat apply Forall_cons; try apply Forall_nil.
           - eapply kword_var; [exact Crc | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | cbn [edenot]; reflexivity].
           - eapply krange_var; [evs; reflexivity | lia | lia].
           - eapply kword_var; [eapply fld_cellw; [exact V2f0 | cbn; lia] | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity]. }
      xruns HR HK 100%nat (0x67bc0 :: 0x67df4 :: STOPS) (SCR [] [] []) 50%N.
      { split_scs; try sc_auto1. all: cbn [sc_denot]; evs; rewrite ?br_eq, ?br_ne by lia; try bool_lia. }
      postrun. name_run HRn R1.
      rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (9%bv) G9.
      rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (22%bv) G22.
      pose proof (syms_id_sound _ _ _ _ OSREGS HRn eq_refl) as GS.
      clear HRn HR HK. fixregs2. pose proof (oregs_glue w R R1 OR GS G2 G3 G4 G8 (or_introl G9)) as OR1. clear GS G9.
      rewrite ?PmExitDiagS1.w_mul_lit, ?SymExec.alu64_add_lit in G22. replace (i_io I * 4) with (4 * i_io I) in G22 by lia.
      eapply (pm_xrnt w c0 K fx I A M model c R1 (t3a (c_v2 c)) PS FZ IP X Htr BUD OR1 LM IC IFR Hic He2 Hw ACC MACC Hsum LA1 LA3 LA2 ltac:(intros Hgt; specialize (HG5 Hgt); lia) HInt HFlt G11 ltac:(lia) G10 G22 LK).
  Qed.

  Lemma pm_xexit : forall (w : pmw MI ST) c0 K (fx : FPState) (I : ictxR) A M model c R',
    PMS w c0 K -> frm_zero (@fp_csr fx) -> ipure I -> OLI w I A M model c R' -> i_io I + i_iwc I <= c_widx c ->
    getr R' 22%bv = Z_to_bv 64 (c_widx c) -> getr R' 21%bv = Z_to_bv 64 (i_io I) -> getr R' 10%bv = Z_to_bv 64 (i_iwc I) ->
    getr R' 11%bv = Z_to_bv 64 (i_io I + i_iwc I) -> getr R' 13%bv = Z_to_bv 64 (t3a (c_v3 c)) ->
    getr R' 12%bv = Z_to_bv 64 (t3a (c_v3 c) + 4 * Zlen (t3b (c_v3 c))) ->
    LOOPK w K (i_io I) ->
    srealizes SEGS (cfg fx R' 0x67a3c M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx I A M model c R PS FZ IP HOLI Hle Q22 Q21 Q10 Q11 Q13 Q12 LK.
    pose proof HOLI as HOLI'. destruct HOLI' as (OB & Hw1 & ACC & CNT & V2L & V3L & ZW & HTY & IACC).
    pose proof OB as OB'. destruct OB' as (X & Htr & BUD & OR & LM & IC & IFR & Hic & He2 & Hw & MACC & FR3).
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & Gc2 & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof (x_scal X) as (Sc1 & Sc2 & Sc3 & Sc4). pose proof (ipure_ranges I IP) as (Riwc & Rop).
    pose proof IP as IP'. destruct IP' as (_ & _ & _ & _ & Hg & Hdesc & Rio).
    pose proof OR as OR'. destruct OR' as (Qsp & Qgp & Qtp & Qs0 & Qs1 & Qs3 & Qs4 & Qs8).
    pose proof IC as IC'. destruct IC' as (Cio & Cfw & Ciwc & Cop & Fd).
    pose proof (x_v3 X) as V3. destruct V3 as (_ & _ & _ & V3len & V3blk & V3f0 & V3f1 & _ & V3el). unfold O_V3 in V3f0, V3f1.
    set (b3 := t3a (c_v3 c)) in *. set (xs := t3b (c_v3 c)) in *.
    assert (Rb3 : 0 <= b3 /\ b3 + 4 * Zlen xs < 2 ^ 64).
    { destruct V3blk as [[Hb0 Hc0]|(Hb & _ & _ & Hbc & _)]; [rewrite Hb0; unfold Zlen in *; lia | lia]. }
    pose proof (Zlen_nonneg xs) as Hl0.
    destruct xs as [|x0 xs'] eqn:Exs.
    -
      change (Zlen (@nil Z)) with 0 in Q12. replace (b3 + 4 * 0) with b3 in Q12 by lia.
      pm_seed R w c [Z_to_bv 64 b3; Z_to_bv 64 (i_io I + i_iwc I); Z_to_bv 64 (i_io I); Z_to_bv 64 (i_iwc I)].
      seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (13%bv, EVar 39); (12%bv, EVar 39); (11%bv, EVar 40); (22%bv, EVar 38); (21%bv, EVar 41); (10%bv, EVar 42)] R.
      seedHK HK w A M model c E X.
      xruns HR HK 100%nat (0x67a5c :: STOPS) (SCR [true] [] []) 50%N.
      { split_scs; try sc_auto1. all: cbn [sc_denot]; evs; rewrite ?br_eq, ?br_ne by lia; try bool_lia. }
      postrun. name_run HRn R1.
      rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (9%bv) G9.
      rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (21%bv) G21. rreg HRn (22%bv) G22.
      pose proof (syms_id_sound _ _ _ _ OSREGS HRn eq_refl) as GS.
      clear HRn HR HK. fixregs2. pose proof (oregs_glue w R R1 OR GS G2 G3 G4 G8 (or_introl G9)) as OR1. clear GS G9.
      eapply (pm_x679b8 w c0 K fx I A M model c R1 PS FZ IP (oli_regs w I A M model c R R1 HOLI OR1) Hle); [left; exact Exs | exact G11 | exact G22 | exact G21 | exact G10 | exact LK].
    -
      assert (Hne : xs <> []) by (rewrite Exs; discriminate). rewrite <- Exs in *. clear x0 xs' Exs.
      assert (Hl1 : 1 <= Zlen xs) by (destruct xs as [|z zs]; [exfalso; exact (Hne eq_refl) | rewrite Zlen_cons; pose proof (Zlen_nonneg zs); lia]).
      destruct (V3el (Zlen xs - 1) ltac:(lia)) as [Rxl Fxl]. rewrite (Znth_last xs Hne) in Rxl, Fxl.
      set (xl := last xs 0) in *.
      assert (Rxl31 : 0 <= xl < 2 ^ 31) by (subst xl; apply Forall_last; [exact FR3 | lia]).
      replace (b3 + 4 * (Zlen xs - 1)) with (b3 + 4 * Zlen xs + -4) in Fxl by lia.
      pm_seed R w c [Z_to_bv 64 b3; Z_to_bv 64 (b3 + 4 * Zlen xs); Z_to_bv 64 xl].
      seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (13%bv, EVar 39); (12%bv, EVar 40)] R. seedHK HK w A M model c E X.
      apply (know_more E M [KWord (SA (EVar 40) (-4)) (N.to_nat 4) (EVar 41)]) in HK.
      2: { repeat apply Forall_cons; try apply Forall_nil.
           eapply kword_var; [eapply fld_cellw; [exact Fxl | cbn; lia] | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity]. }
      xruns HR HK 100%nat STOPS (SCR [false] [] []) 50%N.
      { split_scs; try sc_auto1. all: cbn [sc_denot]; evs; rewrite ?br_eq, ?br_ne by lia; try bool_lia. }
      postrun. name_run HRn R1.
      rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (9%bv) G9. rreg HRn (10%bv) G10.
      pose proof (syms_id_sound _ _ _ _ OSREGS HRn eq_refl) as GS.
      clear HRn HR HK. fixregs2. pose proof (oregs_glue w R R1 OR GS G2 G3 G4 G8 (or_introl G9)) as OR1. clear GS G9.
      rewrite ext_val_sx4, sx32_small in G10 by lia.
      assert (Rxl32 : 0 <= xl < 2 ^ 32) by lia.
      eapply (pm_is_optional w A M model c fx R1 _ K X (ex_intro _ xl (conj Rxl32 G10)) G1 ltac:(apply bv_eq; vm_compute; reflexivity)).
      intros R2 KEPT (b & Gb & Hb). pose proof (oregs_kept w R1 R2 OR1 KEPT) as OR2. keptQ KEPT G2 Qsp_R2. keptQ KEPT G8 Qs0_R2.
      clear G1 G2 G3 G4 G8 KEPT.
      destruct b; cbn in Gb.
      +
        destruct (Hb eq_refl) as (x' & Rx' & Gx'). rewrite G10 in Gx'. apply Z_to_bv64_inj in Gx'; [| lia | lia]. subst x'.
        pose proof (fld_cellw M _ 8 _ (x_widx X) ltac:(lia)) as Cwi. unfold O_WIDX in Cwi.
        pm_seed R2 w c [Z_to_bv 64 (i_io I); Z_to_bv 64 (i_iwc I)].
        seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (10%bv, ELit 1)] R2. seedHK HK w A M model c E X.
        apply (know_more E M [KWord (SA (EVar 32) 200) (N.to_nat 8) (EVar 39); KWord (SA (EVar 32) 218) (N.to_nat 2) (EVar 40);
                               KRange (EVar 39) 0 (2 ^ 24); KRange (EVar 40) 0 (2 ^ 16 - 1)]) in HK.
        2: { repeat apply Forall_cons; try apply Forall_nil.
             - eapply kword_var; [exact Cio | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
             - eapply kword_var; [exact Ciwc | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
             - eapply krange_var; [evs; reflexivity | lia | lia].
             - eapply krange_var; [evs; reflexivity | lia | lia]. }
        xruns HR HK 100%nat (0x67a5c :: STOPS) (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
        postrun. name_run HRn R3.
        rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (9%bv) G9.
        rreg HRn (10%bv) G10b. rreg HRn (11%bv) G11. rreg HRn (21%bv) G21. rreg HRn (22%bv) G22.
        pose proof (syms_id_sound _ _ _ _ OSREGS HRn eq_refl) as GS.
        clear HRn HR HK. fixregs2. pose proof (oregs_glue w R2 R3 OR2 GS G2 G3 G4 G8 (or_introl G9)) as OR3. clear GS G9.
        rewrite ?ext_val_zx2 in G10b, G11 by lia. rewrite ?w_add in G11 by lia.
        eapply (pm_x679b8 w c0 K fx I A M model c R3 PS FZ IP (oli_regs w I A M model c R R3 HOLI OR3) Hle); [right; split; [exact Hne | subst xl xs b3; lia] | exact G11 | exact G22 | exact G21 | exact G10b | exact LK].
      +
        pm_seed R2 w c (@nil word).
        seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (10%bv, ELit 0)] R2. seedHK HK w A M model c E X.
        xruns HR HK 100%nat (0x67ce0 :: 0x67a5c :: STOPS) (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
        postrun. name_run HRn R3.
        rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (9%bv) G9.
        pose proof (syms_id_sound _ _ _ _ OSREGS HRn eq_refl) as GS.
        clear HRn HR HK. fixregs2. pose proof (oregs_glue w R2 R3 OR2 GS G2 G3 G4 G8 (or_introl G9)) as OR3. clear GS G9.
        exact (pm_D8 w c0 K fx I A M model c R3 PS FZ IP (oli_regs w I A M model c R R3 HOLI OR3)).
  Qed.
End PM.
