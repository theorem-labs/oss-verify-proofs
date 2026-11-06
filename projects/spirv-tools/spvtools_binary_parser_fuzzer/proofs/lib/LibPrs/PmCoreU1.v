(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From stdpp Require list.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Ubsan.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PropExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SeqExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StepTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.WalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StartupTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SumWalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StoreOk OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MemSplit OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Hoare OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ShapeAlg OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SRealizes OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefReadLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.FPSteps OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibIface OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibBudget OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibEff OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MmapSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibMaskBits OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ZStores OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3Sound OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymRun3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.U1Layout.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.CRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContStmts2 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.U1Facts.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRepFacts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HStmtsU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HFpu OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HConstsU1.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsNeeds OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsInv OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmBaseU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmHyps OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmHypsU1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Module U1_code_671d0_6721c.

Import Stdlib.ZArith.ZArith.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Ubsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_67208 : bv 32 := 0x2e813827.
Lemma F_67208 : fetch_word Ubsan.M.loaded_segments (0x67248 : word) = Some W_67208.
Proof. vm_refl. Qed.
Lemma D_67208 : decode_any W_67208 = Some (FStore FMT_D 2 8 752, 4%Z).
Proof. vm_refl. Qed.

Definition W_6720c : bv 32 := 0x2e913427.
Lemma F_6720c : fetch_word Ubsan.M.loaded_segments (0x6724c : word) = Some W_6720c.
Proof. vm_refl. Qed.
Lemma D_6720c : decode_any W_6720c = Some (FStore FMT_D 2 9 744, 4%Z).
Proof. vm_refl. Qed.

Definition W_67210 : bv 32 := 0x2f213027.
Lemma F_67210 : fetch_word Ubsan.M.loaded_segments (0x67250 : word) = Some W_67210.
Proof. vm_refl. Qed.
Lemma D_67210 : decode_any W_67210 = Some (FStore FMT_D 2 18 736, 4%Z).
Proof. vm_refl. Qed.
End U1_code_671d0_6721c.

Module U1_code_673ac_673f8.

Import Stdlib.ZArith.ZArith.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Ubsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_673e4 : bv 32 := 0x2f013407.
Lemma F_673e4 : fetch_word Ubsan.M.loaded_segments (0x67424 : word) = Some W_673e4.
Proof. vm_refl. Qed.
Lemma D_673e4 : decode_any W_673e4 = Some (FLoad FMT_D 8 2 752, 4%Z).
Proof. vm_refl. Qed.

Definition W_673e8 : bv 32 := 0x2e813487.
Lemma F_673e8 : fetch_word Ubsan.M.loaded_segments (0x67428 : word) = Some W_673e8.
Proof. vm_refl. Qed.
Lemma D_673e8 : decode_any W_673e8 = Some (FLoad FMT_D 9 2 744, 4%Z).
Proof. vm_refl. Qed.

Definition W_673ec : bv 32 := 0x2e013907.
Lemma F_673ec : fetch_word Ubsan.M.loaded_segments (0x6742c : word) = Some W_673ec.
Proof. vm_refl. Qed.
Lemma D_673ec : decode_any W_673ec = Some (FLoad FMT_D 18 2 736, 4%Z).
Proof. vm_refl. Qed.

Definition W_673f4 : bv 32 := 0x00008067.
Lemma F_673f4 : fetch_word Ubsan.M.loaded_segments (0x67434 : word) = Some W_673f4.
Proof. vm_refl. Qed.
Lemma D_673f4 : decode_any W_673f4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
End U1_code_673ac_673f8.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require list.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac WalkTac StartupTac SumWalkTac StoreOk MemSplit Hoare ShapeAlg
  SRealizes RefMemcpyLib RefReadLib FPSteps LibIface LibBudget LibEff MmapSim LibMaskBits
  ZStores SymExec3 SymExec3Sound SymRun3 U1Layout.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContLib ContStmts ContStmts2 U1Facts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts HStmtsU1 HLib HFpu HConstsU1.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsNeeds PrsInv PrsStmts PmBaseU1 PmHyps PmHypsU1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmCoreU1.U1_code_671d0_6721c. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmCoreU1.U1_code_673ac_673f8.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition tcU1 : tabl_consts := {|
  tc_fixword := 0x6bf10; tc_is_host_endian := 0x6c010; tc_binary_endianness := 0x6bf50; tc_opcode_split := 0x6c5b8;
  tc_lookup_opcode := 0x6c804; tc_lookup_operand := 0x6c8f0; tc_lookup_ext := 0x6cecc; tc_spec_lookup := 0x6d9dc;
  tc_idesc_operands := 0x6c790; tc_idesc_name := 0x6c7b8; tc_odesc_operands := 0x6c768; tc_edesc_operands := 0x6c7dc;
  tc_operand_type_str := 0x6d0fc; tc_generates_type := 0x6c634; tc_is_ext_inst := 0x6c748; tc_is_optional := 0x6d2b0;
  tc_is_nonsemantic := 0x6dcd4; tc_fpenc := 0x6d7bc; tc_import_type_get := 0x6da2c; tc_push_types := 0x6d134;
  tc_take_first := 0x6d744; tc_strlen := 0xe3600;
  tc_lookup_stack := 64; tc_import_stack := 64; tc_pattern_stack := 96 |}.

Definition dcU1 : ds_consts := {|
  dc_ctor := 0x69830; dc_pdiag := 0x693c4; dc_pdiag_err := 0x693c4; dc_put_cstr := 0x69468;
  dc_put_u16 := 0x92044; dc_put_u32 := 0x92414; dc_put_u64 := 0x925e4; dc_put_int := 0x92210;
  dc_put_string := 0x6c4c8; dc_dtor := 0x6c020; dc_exhausted := 0x6a3fc; dc_stack := 12288; dc_vboff := 112 |}.

Definition nfcU1 : ntfind_consts := {| nf_entry := 0x6a604; nf_miss := 0x6a75c; nf_hit := 0x6a7c0 |}.
Definition ccU1 : cont_constsU1 := {|
  ku_ecw_pbs := {| vc_entry := 0x6a25c; vc_stack := 80 |}; ku_ecw_pbs2 := {| vc_entry := 0x6a0bc; vc_stack := 80 |};
  ku_oty_pb := {| vc_entry := 0x6a57c; vc_stack := 96 |}; ku_oty_pbs := {| vc_entry := 0x6d838; vc_stack := 80 |};
  ku_opnd_pbs := {| vc_entry := 0x6bd40; vc_stack := 64 |};
  ku_str := {| sc_push_back := 0x8d1d8; sc_resize := 0x8d60c; sc_makestring := 0x6682c; sc_push_stack := 64; sc_resize_stack := 80; sc_ms_stack := 128 |};
  ku_idx_u32 := 0x6a53c; ku_idx_ext := 0x6a85c; ku_del1 := 0x6f8cc; ku_del_stack := 0 |}.
Definition kcU1 : prs_consts := {|
  kc_parse := 0x66944; kc_parse_opts := 0x6694c; kc_parse_module := 0x67210; kc_set_numeric := 0x6a5f4;
  kc_pm_stack := 16384; kc_po_stack := 17056 |}.

Definition STOPS : list Z :=
  [0x6bf10; 0x6c010; 0x6bf50; 0x6c5b8; 0x6c804; 0x6c8f0; 0x6cecc; 0x6d9dc; 0x6c790; 0x6c7b8; 0x6c768; 0x6c7dc;
   0x6d0fc; 0x6c634; 0x6c748; 0x6d2b0; 0x6dcd4; 0x6d7bc; 0x6da2c; 0x6d134; 0x6d744; 0xe3600;
   0x693c4; 0x69468; 0x92044; 0x92414; 0x925e4; 0x92210; 0x6c020; 0x6a3fc;
   0x6a5f4; 0x6b21c; 0x6a89c; 0x6a53c; 0x6a85c; 0x689f8; 0x66680; 0x6a06c;
   0x6a25c; 0x6a0bc; 0x6a57c; 0x6bd40; 0x6682c; 0x6f8cc; 0x69ce4;
   0x673ec; 0x67578; 0x67570; 0x677d0; 0x677c4; 0x67f60; 0x68560; 0x690d8; 0x690dc].

Definition fconsts (fx : FPState) : Prop :=
  fholds fx 8%bv 0x4b000000 /\ fholds fx 9%bv 0xbf800000 /\ fholds fx 18%bv 0x5f800000.

Module Ly := U1Layout.

Section PM.
Context {AC : AllocCeiling}.
  Variable MI : MallocIface SEGS Ly.L.
  Variable ST : StaticsIface SEGS Ly.L.
  Variables (G : grammar) (idesc : Z -> Z -> Prop) (odesc edesc : Z -> Z -> Z -> Prop)
            (generates_type is_ext_inst is_nonsemantic : Z -> bool)
            (ds_rep : AS MI -> mem -> Z -> Z -> Z -> list (Z * Z) -> Prop).
  Variable CL : pm_calleesU1 SEGS Ly.L MI ST G tcU1 dcU1 nfcU1 HConstsU1.hc ccU1 kcU1
                  idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep.

  #[local] Notation PMX := (PmBaseU1.PMX MI ST).
  #[local] Notation cfg fx R pc M model := (mkCfg (@mkst fx R (Z_to_bv 64 pc) M (seg_rom SEGS)) model).

  Definition stc_of (w : pmw MI ST) (c : pmc) : stateC :=
    {| st_words := w_words w; st_nwords := w_n w; st_diag := w_diag w;
       st_widx := c_widx c; st_icount := c_icount c; st_endian := c_endian c; st_flags := c_reqconv c;
       st_m1 := c_m1 c; st_m2 := c_m2 c; st_m3 := c_m3 c;
       st_v1 := (t3a (c_v1 c), t3a (c_v1 c) + OPND_SZ * t3b (c_v1 c), t3a (c_v1 c) + OPND_SZ * t3c (c_v1 c));
       st_v2 := (t3a (c_v2 c), t3a (c_v2 c) + 4 * Zlen (t3b (c_v2 c)), t3a (c_v2 c) + 4 * t3c (c_v2 c));
       st_v3 := (t3a (c_v3 c), t3a (c_v3 c) + 4 * Zlen (t3b (c_v3 c)), t3a (c_v3 c) + 4 * t3c (c_v3 c)) |}.
  Definition prc_of (w : pmw MI ST) (c : pmc) : parserC :=
    {| pc_cons := w_cons w; pc_user := w_user w; pc_state := stc_of w c |}.

  Lemma fld_cell : forall M a (w : N) v,
    CRep.fld SEGS M a (N.to_nat w) v -> 0 <= v < 2 ^ (8 * Z.of_N w) -> cellw SEGS M a w v.
  Proof using. intros M a w v F Hr. split; [exact Hr | exact F]. Qed.

  Lemma c_blocks_state_blocks : forall (w : pmw MI ST) c,
    c_tr c = [] -> state_blocks (stc_of w c) = c_blocks c.
  Proof using AC MI ST.
    intros w c Htr. unfold state_blocks, c_blocks, vec_blocks, vec_opnd_blocks.
    cbn [stc_of st_m1 st_m2 st_m3 st_v1 st_v2 st_v3].
    change (t3a (t3a (c_v1 c), t3a (c_v1 c) + OPND_SZ * t3b (c_v1 c), t3a (c_v1 c) + OPND_SZ * t3c (c_v1 c))) with (t3a (c_v1 c)).
    change (t3c (t3a (c_v1 c), t3a (c_v1 c) + OPND_SZ * t3b (c_v1 c), t3a (c_v1 c) + OPND_SZ * t3c (c_v1 c))) with (t3a (c_v1 c) + OPND_SZ * t3c (c_v1 c)).
    change (t3a (t3a (c_v2 c), t3a (c_v2 c) + 4 * Zlen (t3b (c_v2 c)), t3a (c_v2 c) + 4 * t3c (c_v2 c))) with (t3a (c_v2 c)).
    change (t3c (t3a (c_v2 c), t3a (c_v2 c) + 4 * Zlen (t3b (c_v2 c)), t3a (c_v2 c) + 4 * t3c (c_v2 c))) with (t3a (c_v2 c) + 4 * t3c (c_v2 c)).
    change (t3a (t3a (c_v3 c), t3a (c_v3 c) + 4 * Zlen (t3b (c_v3 c)), t3a (c_v3 c) + 4 * t3c (c_v3 c))) with (t3a (c_v3 c)).
    change (t3c (t3a (c_v3 c), t3a (c_v3 c) + 4 * Zlen (t3b (c_v3 c)), t3a (c_v3 c) + 4 * t3c (c_v3 c))) with (t3a (c_v3 c) + 4 * t3c (c_v3 c)).
    rewrite Htr, app_nil_r.
    f_equal. f_equal. f_equal. f_equal.
    - destruct (t3a (c_v1 c) =? 0); [reflexivity|]. f_equal. f_equal. lia.
    - f_equal.
      + destruct (t3a (c_v2 c) =? 0); [reflexivity|]. f_equal. f_equal. lia.
      + destruct (t3a (c_v3 c) =? 0); [reflexivity|]. f_equal. f_equal. lia.
  Qed.

  Lemma vraw_of_vec32 : forall A M v b xs cap,
    CRep.vec32 MI A M v b xs cap -> 0 <= v -> v + 24 <= 2 ^ 47 -> cap < 2 ^ 40 ->
    vraw MI A M v b (b + 4 * Zlen xs) (b + 4 * cap).
  Proof using AC MI.
    intros A M v b xs cap (Hv0 & Hv1 & HD & Hlen & Hb & F0 & F1 & F2 & _) Hv Hv' Hcap.
    constructor.
    - apply fld_cell; [exact F0 | destruct Hb as [[-> ->]|(Hb0 & _ & _ & Hbc & _)]; cbn; lia].
    - apply fld_cell; [exact F1 | destruct Hb as [[-> ->]|(Hb0 & _ & _ & Hbc & _)]; cbn; lia].
    - apply fld_cell; [exact F2 | destruct Hb as [[-> ->]|(Hb0 & _ & _ & Hbc & _)]; cbn; lia].
    - destruct Hb as [[-> ->]|(Hb0 & Hal & Hc0 & Hbc & HIn & _)].
      + left. repeat split; lia.
      + right. split; [lia|]. split; [replace (b + 4 * cap - b) with (4 * cap) by lia; exact HIn | lia].
  Qed.

  Lemma vraw_of_vec_opnd : forall A M v b n cap,
    CRep.vec_opnd MI A M v b n cap -> 0 <= v -> v + 24 <= 2 ^ 47 -> cap < 2 ^ 40 ->
    vraw MI A M v b (b + OPND_SZ * n) (b + OPND_SZ * cap).
  Proof using AC MI.
    intros A M v b n cap (Hv0 & Hv1 & HD & Hlen & Hb & F0 & F1 & F2) Hv Hv' Hcap. unfold OPND_SZ in *.
    constructor.
    - apply fld_cell; [exact F0 | destruct Hb as [[-> ->]|(Hb0 & _ & _ & Hbc & _)]; cbn; lia].
    - apply fld_cell; [exact F1 | destruct Hb as [[-> ->]|(Hb0 & _ & _ & Hbc & _)]; cbn; lia].
    - apply fld_cell; [exact F2 | destruct Hb as [[-> ->]|(Hb0 & _ & _ & Hbc & _)]; cbn; lia].
    - destruct Hb as [[-> ->]|(Hb0 & Hal & Hc0 & Hbc & HIn & _)].
      + left. repeat split; lia.
      + right. split; [lia|]. split; [replace (b + 20 * cap - b) with (20 * cap) by lia; exact HIn | lia].
  Qed.

  Lemma pmx_parser_rep : forall (w : pmw MI ST) A M model c,
    PMX w A M model c -> c_tr c = [] ->
    t3c (c_v1 c) < 2 ^ 40 -> t3c (c_v2 c) < 2 ^ 40 -> t3c (c_v3 c) < 2 ^ 40 -> 0 <= w_diag w < 2 ^ 64 ->
    parser_rep SEGS Ly.L MI A M (w_p w) (prc_of w c).
  Proof using AC MI ST.
    intros w A M model c X Htr Hc1 Hc2 Hc3 Hdiag.
    pose proof (x_geo X) as GEO. pose proof (x_scal X) as SC. pose proof ac_bounds_lit as Hcv.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & [Gc2 Gcal] & Gap & Gn & Gw).
    unfold w_sp0, PARSER_SIZE, PM_FRAME in *.
    assert (NDB : NoDup (map fst (state_blocks (stc_of w c)))).
    { rewrite (c_blocks_state_blocks w c Htr).
      pose proof (ai_live_nodup MI A M model (x_ai X)) as ND.
      pose proof (x_live X) as PL.
      apply (Permutation_map fst) in PL. rewrite map_app in PL.
      rewrite PL in ND. apply (proj1 (list_relations.list.NoDup_app _ _)) in ND. destruct ND as (_ & _ & ND2). exact ND2. }
    unfold prc_of. constructor; cbn [pc_cons pc_user pc_state].
    - exact (x_cons X).
    - exact (x_user X).
    - exact (x_hdrfn X).
    - exact (x_insfn X).
    - exact (x_hunk X).
    -
      unfold ST_OFF. constructor; unfold stc_of;
        cbn [st_words st_nwords st_diag st_widx st_icount st_endian st_flags st_m1 st_m2 st_m3 st_v1 st_v2 st_v3 t3a t3b t3c fst snd].
      + apply fld_cell; [| cbn; lia]. replace (w_p w + 48) with (w_p w + O_WORDS) by reflexivity. exact (x_words X).
        Unshelve. all: try exact 0.
      + apply fld_cell; [| cbn; lia]. replace (w_p w + 48 + 8) with (w_p w + O_N) by (unfold O_N; lia). exact (x_n X).
      + apply fld_cell; [| cbn; lia]. replace (w_p w + 48 + 16) with (w_p w + O_DIAG) by (unfold O_DIAG; lia). exact (x_diag X).
      + apply fld_cell; [| cbn; lia]. replace (w_p w + 48 + 24) with (w_p w + O_WIDX) by (unfold O_WIDX; lia). exact (x_widx X).
      + apply fld_cell; [| cbn; lia]. replace (w_p w + 48 + 32) with (w_p w + O_ICOUNT) by (unfold O_ICOUNT; lia). exact (x_icount X).
      + apply fld_cell; [| cbn; lia]. replace (w_p w + 48 + 40) with (w_p w + O_ENDIAN) by (unfold O_ENDIAN; lia). exact (x_endian X).
      + apply fld_cell; [| cbn; lia]. replace (w_p w + 48 + 44) with (w_p w + O_FLAGS) by (unfold O_FLAGS; lia). exact (x_flags X).
      + replace (w_p w + 48 + 48) with (w_p w + O_M1) by (unfold O_M1; lia). exact (x_m1 X).
      + replace (w_p w + 48 + 88) with (w_p w + O_M2) by (unfold O_M2; lia). exact (x_m2 X).
      + replace (w_p w + 48 + 128) with (w_p w + O_M3) by (unfold O_M3; lia). exact (x_m3 X).
      + replace (w_p w + 48 + 168) with (w_p w + O_V1) by (unfold O_V1; lia).
        apply vraw_of_vec_opnd; [exact (x_v1 X) | unfold O_V1; lia | unfold O_V1; lia | exact Hc1].
      + replace (w_p w + 48 + 192) with (w_p w + O_V2) by (unfold O_V2; lia).
        apply vraw_of_vec32; [exact (x_v2 X) | unfold O_V2; lia | unfold O_V2; lia | exact Hc2].
      + replace (w_p w + 48 + 216) with (w_p w + O_V3) by (unfold O_V3; lia).
        apply vraw_of_vec32; [exact (x_v3 X) | unfold O_V3; lia | unfold O_V3; lia | exact Hc3].
      + intros i Hi. replace (w_p w + 48 + i) with (w_p w + (48 + i)) by lia. apply (x_pdef X). unfold PARSER_SIZE. lia.
      + replace (w_p w + 48) with ((w_p w / 16 + 3) * 2 * 8) by (pose proof (Z.div_mod (w_p w) 16 ltac:(lia)); lia).
        apply Z.mod_mul. lia.
      + exact NDB.
    - intros i Hi. apply (x_pdef X). unfold ST_OFF, PARSER_SIZE in *. lia.
    - exact Gp16.
    - unfold PARSER_SIZE. lia.
    - exact (x_consf X).
    - exact (x_consd X).
    - exact Gap.
  Qed.

  Definition POSTK (w : pmw MI ST) (c0 : parserC) (K : TSet) : Prop :=
    forall (fx' : FPState) A' R' M' model' (c' : parserC) (r : Z),
      LibEff.retB MI ST A' (w_s w) (w_R0 w) R' M' (w_model0 w) model' -> frm_zero (@fp_csr fx') ->
      getr R' 10%bv = Z_to_bv 64 r ->
      parser_rep SEGS Ly.L MI A' M' (w_p w) c' -> pc_cons c' = w_cons w ->
      st_words (pc_state c') = w_words w -> st_nwords (pc_state c') = w_n w ->
      Permutation (live MI A') (w_L0 w ++ state_blocks (pc_state c')) ->
      (forall b, In b (state_blocks (pc_state c')) -> 0 < snd b <= PM_BIG (w_n w)) ->
      (forall cls, count_class_f (size_class MI) (BIG MI) (state_blocks (pc_state c')) cls <= (if cls <? 4 then PM_NODES (w_n w) else 0) + 10) ->
      st_vsteps (pc_state c') ->
      eff MI (w_A0 w) A' (w_M0 w) M' (w_sp0 w - w_STK w, w_sp0 w) (pm_foot SEGS Ly.L MI (w_A0 w) (w_p w) c0 c') ->
      srealizes SEGS (cfg fx' R' (w_ret w) M' model') K.

  Lemma sc_read_w : forall E M (sa : saddr) (a : Z) (v : word) (e : expr),
    rdn SEGS M (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 v) ->
    adenot E sa = Z_to_bv 64 a -> edenot E e = v ->
    sc_denot SEGS M E (SCReadBase sa 8 false e).
  Proof using.
    intros E M sa a v e Hr Ha He.
    rewrite <- (Z_to_bv_bv_unsigned 64 v) in Hr.
    pose proof (bv_unsigned_in_range 64 v) as Hv. change (bv_modulus 64) with (2 ^ 64) in Hv.
    eapply (sc_read_cellw SEGS E M sa a 8 (bv_unsigned v) e); [split; [cbn; lia | exact Hr] | cbn; lia | exact Ha | rewrite He; symmetry; apply Z_to_bv_bv_unsigned].
  Qed.

  Ltac sc_rdw H := eapply (sc_read_w _ _ _ _ _ _ H); [evs; rewrite ?v_addi_Z by lia; first [reflexivity | f_equal; lia] | evs; reflexivity].

  Lemma in_blocks_dec : forall (l : list (Z * Z)) a,
    (exists b, In b l /\ fst b <= a < fst b + snd b) \/ (forall b, In b l -> ~ (fst b <= a < fst b + snd b)).
  Proof using.
    intros l a. induction l as [|[q k] l IH].
    - right. intros b Hb. destruct Hb.
    - destruct (Z_le_dec q a); [destruct (Z_lt_dec a (q + k))|].
      + left. exists (q, k). split; [left; reflexivity | cbn; lia].
      + destruct IH as [(b & Hb & Hab)|Hn]; [left; exists b; split; [right; exact Hb | exact Hab] | right].
        intros b [<-|Hb]; [cbn; lia | apply Hn; exact Hb].
      + destruct IH as [(b & Hb & Hab)|Hn]; [left; exists b; split; [right; exact Hb | exact Hab] | right].
        intros b [<-|Hb]; [cbn; lia | apply Hn; exact Hb].
  Qed.

  Lemma fslot_rdn : forall (w : pmw MI ST) A M model c (k : Z),
    PMX w A M model c -> 104 <= k -> k + 8 <= 864 ->
    exists bs, rdn SEGS M (Z_to_bv 64 (w_sp w + (864 - k - 8))) 8 = Some bs.
  Proof using AC MI ST.
    intros w A M model c k X Hk1 Hk2. pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & _). unfold w_sp0, PM_FRAME in *.
    pose proof (x_wdef X) as D. unfold w_sp0, PM_FRAME in D.
    destruct (mdef_rdn SEGS M (w_sp w + 864 - w_STK w) (w_STK w) (w_STK w - k - 8) 8 D ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn; lia)) as (bs & Hbs & _).
    exists bs. replace (w_sp w + (864 - k - 8)) with (w_sp w + 864 - w_STK w + (w_STK w - k - 8)) by lia. exact Hbs.
  Qed.

  Ltac fld_step MS Fx Dx Qsp Hbs znext :=
    eapply srz_msteps; [eapply ms_halt; exact MS | eapply ms_lazy; exact MS | | ];
    [ norm_pc; eapply msteps_one; [reflexivity|];
      eapply fp_step_fld; [exact Fx | reflexivity | exact Dx | rewrite Qsp; match goal with |- v_addi _ ?i = _ => let v := eval vm_compute in i in change i with v end; apply v_addi_Z; lia | exact Hbs]
    | cbn [fp_regs fp_csr];
      lazymatch goal with |- srealizes _ (mkCfg (mkst _ ?pc _ _) _) _ =>
        replace pc with (Z_to_bv 64 znext : word) by (apply bv_eq; vm_compute; reflexivity) end ].

  Lemma pm_exit : forall (w : pmw MI ST) (c0 : parserC) K (fx : FPState) A M model c R (r : word),
    PMX w A M model c -> c_tr c = [] ->
    t3c (c_v1 c) < 2 ^ 40 -> t3c (c_v2 c) < 2 ^ 40 -> t3c (c_v3 c) < 2 ^ 40 ->
    0 <= w_diag w < 2 ^ 64 ->
    (forall b, In b (c_blocks c) -> 0 < snd b <= PM_BIG (w_n w)) ->
    (forall cls, count_class_f (size_class MI) (BIG MI) (c_blocks c) cls <= (if cls <? 4 then PM_NODES (w_n w) else 0) + 10) ->
    Permutation (live MI (w_A0 w)) (w_L0 w ++ state_blocks (pc_state c0)) ->
    frm_zero (@fp_csr fx) -> POSTK w c0 K ->
    getr R 2%bv = Z_to_bv 64 (w_sp w) -> getr R 3%bv = getr (w_R0 w) 3%bv -> getr R 4%bv = getr (w_R0 w) 4%bv ->
    getr R 22%bv = r -> ret_ok (Z_to_bv 64 (w_ret w)) -> getr (w_R0 w) 1%bv = Z_to_bv 64 (w_ret w) -> getr (w_R0 w) 2%bv = Z_to_bv 64 (w_sp0 w) ->
    srealizes SEGS (cfg fx R 0x673ec M model) K.
  Proof using AC MI ST.
    intros w c0 K fx A M model c R r X Htr Hc1 Hc2 Hc3 Hdiag Hsz Hcnt HL0 FZ POST Hsp Hgp Htp Hs6 Hret R0ra R0sp.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & [Gc2 Gcal] & Gap & Gn & Gw).
    destruct (fslot_rdn w A M model c 104 X ltac:(lia) ltac:(lia)) as [bs0 Hbs0].
    destruct (fslot_rdn w A M model c 112 X ltac:(lia) ltac:(lia)) as [bs1 Hbs1].
    destruct (fslot_rdn w A M model c 120 X ltac:(lia) ltac:(lia)) as [bs2 Hbs2].
    cbn [Z.sub] in Hbs0, Hbs1, Hbs2.
    unfold w_sp0, PARSER_SIZE, PM_FRAME in *.
    pose proof (x_slots X) as SL. unfold w_sp0, PM_FRAME in SL.
    pose (E := Eseed R [getr (w_R0 w) 27%bv; getr (w_R0 w) 26%bv; getr (w_R0 w) 25%bv; getr (w_R0 w) 24%bv; getr (w_R0 w) 23%bv;
                        getr (w_R0 w) 22%bv; getr (w_R0 w) 21%bv; getr (w_R0 w) 20%bv; getr (w_R0 w) 19%bv; getr (w_R0 w) 18%bv;
                        getr (w_R0 w) 9%bv; getr (w_R0 w) 8%bv; Z_to_bv 64 (w_ret w); Z_to_bv 64 (w_sp w); r]).
    assert (HR : regs_ok E (srs sr_id [(2%bv, EVar 45); (22%bv, EVar 46)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros XX; discriminate XX); evs; assumption. }
    assert (HK : know_ok SEGS E M [KRange (EVar 45) (2 ^ 20) (2 ^ 47)]).
    { repeat apply Forall_cons; try apply Forall_nil. eapply krange_var; [evs; reflexivity | lia | lia]. }
    pose proof (x_ms X) as MS.
    xruns HR HK 100%nat STOPS (SCR [] [EVar 44; EVar 43; EVar 42; EVar 41; EVar 40; EVar 39; EVar 38; EVar 37; EVar 36; EVar 35; EVar 34; EVar 33; EVar 32] []) 60%N.
    { split_scs.
      - sc_rdw (SL 13 ltac:(lia)). - sc_rdw (SL 12 ltac:(lia)). - sc_rdw (SL 11 ltac:(lia)). - sc_rdw (SL 10 ltac:(lia)).
      - sc_rdw (SL 9 ltac:(lia)). - sc_rdw (SL 8 ltac:(lia)). - sc_rdw (SL 7 ltac:(lia)). - sc_rdw (SL 6 ltac:(lia)).
      - sc_rdw (SL 5 ltac:(lia)). - sc_rdw (SL 4 ltac:(lia)). - sc_rdw (SL 3 ltac:(lia)). - sc_rdw (SL 2 ltac:(lia)).
      - sc_rdw (SL 1 ltac:(lia)). }

    rreg HR' (2%bv) G2.
    fld_step MS F_673e4 D_673e4 G2 Hbs0 0x67428.
    fld_step MS F_673e8 D_673e8 G2 Hbs1 0x6742c.
    fld_step MS F_673ec D_673ec G2 Hbs2 0x67430.

    rreg HR' (1%bv) G1. rreg HR' (10%bv) G10. rreg HR' (3%bv) G3. rreg HR' (4%bv) G4.
    pose proof (bv_unsigned_in_range 64 (getr R' 10%bv)) as Ha0r. change (bv_modulus 64) with (2 ^ 64) in Ha0r.
    pose (E2 := Eseed R' [Z_to_bv 64 (w_sp w); Z_to_bv 64 (w_ret w)]).
    assert (HR2 : regs_ok E2 (srs sr_id [(2%bv, EVar 32); (1%bv, EVar 33)]) R').
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros XX; discriminate XX); evs; assumption. }
    assert (HK2 : know_ok SEGS E2 M []) by constructor.
    xruns HR2 HK2 100%nat STOPS (SCR [] [] []) 60%N. { split_scs. }
    lazymatch goal with H : regs_ok _ _ ?Rx |- srealizes _ (mkCfg (mkst _ _ _ ?Rx) _) _ => idtac | _ => idtac end.
    lazymatch goal with H : regs_ok E2 _ ?Rx |- _ => rename H into HRf; rename Rx into Rf end.
    rreg HRf (1%bv) F1. rreg HRf (2%bv) F2.
    pose proof (syms_id_sound _ _ _ _ [3; 4; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HRf eq_refl) as Fs.
    eapply srz_msteps; [exact (ms_halt _ MS) | exact (ms_lazy _ MS) | | ].
    { norm_pc. stepjr F_673f4 D_673f4 (Z_to_bv 64 (w_ret w)) ltac:(gres; rewrite F1; reflexivity). apply mst_refl. }
    lazymatch goal with |- srealizes _ (mkCfg (mkst _ ?pc _ _) _) _ =>
      replace pc with (Z_to_bv 64 (w_ret w)) by (symmetry; exact Hret) end.
    lazymatch goal with |- srealizes _ (mkCfg (@mkst ?fxc _ _ _ _) _) _ =>
      eapply (POST fxc A Rf M model (prc_of w c) (bv_unsigned (getr R' 10%bv))) end.
    - constructor.
      + exact (x_ai X). + exact MS. + exact (x_fs X). + exact (x_fds X). + exact (x_sx X).
      + intros rr Hrr. unfold callee_saved in Hrr.
        destruct (bv_eq_dec _ rr 1%bv) as [->|N1]; [rewrite F1; symmetry; exact R0ra|].
        destruct (bv_eq_dec _ rr 2%bv) as [->|N2]; [rewrite F2, w_add by lia; symmetry; exact R0sp|].
        cbn in Hrr.
        repeat (destruct Hrr as [<-|Hrr];
          [first [contradiction
                 | rewrite Fs by (clear; cbn; tauto); first [rewrite G3; exact Hgp | rewrite G4; exact Htp | rewrite (reg_val _ _ _ _ HR'); evs; reflexivity]] |]).
        destruct Hrr.
    - exact FZ.
    - rewrite Fs by (clear; cbn; tauto). symmetry. apply Z_to_bv_bv_unsigned.
    - eapply pmx_parser_rep; eassumption.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - cbn [pc_state prc_of]. rewrite (c_blocks_state_blocks w c Htr). exact (x_live X).
    - cbn [pc_state prc_of]. rewrite (c_blocks_state_blocks w c Htr). exact Hsz.
    - cbn [pc_state prc_of]. rewrite (c_blocks_state_blocks w c Htr). exact Hcnt.
    - unfold st_vsteps, prc_of, stc_of. cbn [pc_state st_v1 st_v2 st_v3 HStmts.t3a HStmts.t3b fst snd]. pose proof (x_v1 X) as V1. destruct V1 as (_ & _ & _ & Hn1 & _). split; [| split]; [exists (HStmts.t3b (c_v1 c)); unfold OPND_SZ; lia | exists (Zlen (HStmts.t3b (c_v2 c))); unfold Zlen; lia | exists (Zlen (HStmts.t3b (c_v3 c))); unfold Zlen; lia].
    - eapply eff_weaken; [exact (x_eff X)|]. intros a [Ha|(Hj1 & Hj2 & Hj3)].
      + left. left. unfold PARSER_SIZE. exact Ha.
      + destruct (in_blocks_dec (state_blocks (pc_state c0)) a) as [(b & Hb & Hab)|Hnone].
        * left. right. unfold ST_OFF. right. exists b. split; [exact Hb | exact Hab].
        * right. right. split; [exact Hj1|]. split; [exact Hj2|]. intros q k Hqk.
          apply (Permutation_in (q, k) HL0) in Hqk. apply in_app_iff in Hqk. destruct Hqk as [Hq|Hq].
          -- exact (Hj3 q k Hq).
          -- intros Hin. exact (Hnone (q, k) Hq Hin).
  Qed.

  Definition init_pmc (c0 : parserC) : pmc :=
    let st := pc_state c0 in
    {| c_widx := st_widx st; c_icount := st_icount st; c_endian := st_endian st; c_reqconv := st_flags st;
       c_m1 := st_m1 st; c_m2 := st_m2 st; c_m3 := st_m3 st;
       c_v1 := (t3a (st_v1 st), 0, 25); c_v2 := (t3a (st_v2 st), [], 25); c_v3 := (t3a (st_v3 st), [], 25); c_tr := [] |}.

  Definition mkw (sp0 STK ret p : Z) (c0 : parserC) (L0 : list (Z * Z)) (R : bvmap 5 word)
             (A : AS MI) (M : mem) (model : Model) (s : LibIface.SX ST) : pmw MI ST :=
    {| w_sp := sp0 - PM_FRAME; w_STK := STK; w_ret := ret; w_p := p; w_cons := pc_cons c0; w_user := pc_user c0;
       w_diag := st_diag (pc_state c0); w_words := st_words (pc_state c0); w_n := st_nwords (pc_state c0);
       w_L0 := L0; w_R0 := R; w_A0 := A; w_M0 := M; w_model0 := model; w_s := s |}.

  Lemma init_blocks : forall c0,
    fresh_state (pc_state c0) (st_words (pc_state c0)) (st_nwords (pc_state c0)) ->
    c_blocks (init_pmc c0) = state_blocks (pc_state c0).
  Proof using.
    intros c0 FR. destruct FR as (_ & _ & _ & _ & _ & Hm1 & Hm2 & Hm3 & E1 & E2 & E3 & N1 & N2 & N3 & C1 & C2 & C3).
    unfold c_blocks, init_pmc, state_blocks, vec_blocks, vec_opnd_blocks. cbn [c_m1 c_m2 c_m3 c_v1 c_v2 c_v3 c_tr t3a t3b t3c fst snd].
    rewrite app_nil_r. unfold t3a, t3c in *.
    destruct (Z.eqb_spec (fst (fst (st_v1 (pc_state c0)))) 0); [lia|].
    destruct (Z.eqb_spec (fst (fst (st_v2 (pc_state c0)))) 0); [lia|].
    destruct (Z.eqb_spec (fst (fst (st_v3 (pc_state c0)))) 0); [lia|].
    rewrite C1, C2, C3. repeat f_equal; unfold OPND_SZ; lia.
  Qed.

  Lemma vec32_of_vraw_empty : forall A M model v b,
    ainv MI A M model -> vraw MI A M v b b (b + 100) -> b <> 0 -> defined M v 24 -> alloc_ceiling <= v -> v + 24 <= 2 ^ 47 ->
    CRep.vec32 MI A M v b [] 25.
  Proof using AC MI.
    intros A M model v b AI [Vb Ve Vc Vblk] Hb HD Hv Hv'. pose proof ac_bounds_lit as Hcv.
    destruct Vblk as [(-> & _)|(_ & HIn & _)]; [lia|].
    replace (b + 100 - b) with (4 * 25) in HIn by lia.
    destruct (ai_live_block MI A M model b (4 * 25) AI HIn) as (_ & Hal & Hb0 & Hbc & _).
    unfold CRep.vec32. unfold Zlen. cbn [length Z.of_nat]. rewrite Z.mul_0_r, Z.add_0_r.
    refine (conj _ (conj _ (conj HD (conj _ (conj _ (conj (proj2 Vb) (conj (proj2 Ve) (conj _ _)))))))); try lia.
    - right. repeat split; try lia. exact HIn.
    - replace (b + 4 * 25) with (b + 100) by lia. exact (proj2 Vc).
  Qed.

  Lemma vec_opnd_of_vraw_empty : forall A M model v b,
    ainv MI A M model -> vraw MI A M v b b (b + 500) -> b <> 0 -> defined M v 24 -> alloc_ceiling <= v -> v + 24 <= 2 ^ 47 ->
    CRep.vec_opnd MI A M v b 0 25.
  Proof using AC MI.
    intros A M model v b AI [Vb Ve Vc Vblk] Hb HD Hv Hv'. pose proof ac_bounds_lit as Hcv.
    destruct Vblk as [(-> & _)|(_ & HIn & _)]; [lia|].
    replace (b + 500 - b) with (OPND_SZ * 25) in HIn by (unfold OPND_SZ; lia).
    destruct (ai_live_block MI A M model b (OPND_SZ * 25) AI HIn) as (_ & Hal & Hb0 & Hbc & _).
    unfold CRep.vec_opnd, OPND_SZ in *. rewrite Z.mul_0_r, Z.add_0_r.
    refine (conj _ (conj _ (conj HD (conj _ (conj _ (conj (proj2 Vb) (conj (proj2 Ve) _))))))); try lia.
    - right. repeat split; try lia. exact HIn.
    - replace (b + 20 * 25) with (b + 500) by lia. exact (proj2 Vc).
  Qed.

  Ltac postrun := evs; rewrite ?v_addi_Z by lia; rewrite ?Z.add_0_r, ?Z.add_opp_r.

  Ltac fsd_step MS Fx Dx Qsp Hok znext :=
    eapply srz_msteps; [eapply ms_halt; exact MS | eapply ms_lazy; exact MS | | ];
    [ norm_pc; eapply msteps_one; [reflexivity|];
      eapply fp_step_fsd; [exact Fx | reflexivity | exact Dx | rewrite Qsp; match goal with |- v_addi _ ?i = _ => let v := eval vm_compute in i in change i with v end; apply v_addi_Z; lia | exact Hok]
    | lazymatch goal with |- srealizes _ (mkCfg (mkst _ ?pc _ _) _) _ =>
        replace pc with (Z_to_bv 64 znext : word) by (apply bv_eq; vm_compute; reflexivity) end ].

  Lemma pm_prologue : forall (fx : FPState) A (s : LibIface.SX ST) R M model (sp0 ret p : Z) (c0 : parserC) (L0 : list (Z * Z)) (K : TSet),
    let words := st_words (pc_state c0) in let n := st_nwords (pc_state c0) in
    LibEff.callB MI ST A s R M model sp0 ret 16384 -> ro_clear Ly.L M ->
    getr R 10%bv = Z_to_bv 64 p ->
    parser_rep SEGS Ly.L MI A M p c0 -> above_sp MI A sp0 p PARSER_SIZE -> above_sp MI A sp0 (pc_cons c0) 48 ->
    pc_cons c0 mod 16 = 0 ->
    fresh_state (pc_state c0) words n ->
    (words <> 0 -> words_ok L0 sp0 M words n) ->
    (words <> 0 -> forall a, zwin words (words + 4 * n) a -> ~ zwin (sp0 - 16384) sp0 a /\ ~ parser_foot p c0 a) ->
    Permutation (live MI A) (L0 ++ state_blocks (pc_state c0)) ->
    pm_budgetL SEGS Ly.L MI A L0 n ->
    let w := mkw sp0 16384 ret p c0 L0 R A M model s in
    (forall M1 R1, PMX w A M1 model (init_pmc c0) ->
       getr R1 8%bv = Z_to_bv 64 p -> getr R1 10%bv = Z_to_bv 64 p -> getr R1 2%bv = Z_to_bv 64 (sp0 - 864) ->
       getr R1 3%bv = getr R 3%bv -> getr R1 4%bv = getr R 4%bv ->
       srealizes SEGS (cfg fx R1 0x67258 M1 model) K) ->
    srealizes SEGS (cfg fx R 0x67210 M model) K.
  Proof using AC MI ST.
    intros fx A s R M model sp0 ret p c0 L0 K. cbn zeta.
    intros CB ROC Ha0 PR ASP ASC CAL FR WOK WDJ PERM BUD CONT.
    destruct CB as [AI MS ROCI SXI SXH CR Hceil HROOM Hwin Hown_sx Herr_sx].
    destruct CR as [Hra Hret Hretr Hsp Hsp16 Hsphi Hgp Htp].
    pose proof ac_bounds_lit as Hcv.
    destruct ASP as (Hpsp & Hphi & Hpown). destruct ASC as (Hcsp & Hchi & Hcown). unfold PARSER_SIZE in *.
    pose (E := Eseed R [Z_to_bv 64 sp0; Z_to_bv 64 p]).
    assert (HR : regs_ok E (srs sr_id [(2%bv, EVar 32); (10%bv, EVar 33)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros XX; discriminate XX); evs; assumption. }
    assert (HK : know_ok SEGS E M [KRange (EVar 32) (2 ^ 24) (2 ^ 47); KWr (SA (EVar 32) (-16384)) (ELit 16384)]).
    { repeat apply Forall_cons; try apply Forall_nil.
      - eapply krange_var; [evs; reflexivity | lia | lia].
      - eapply kwr_stack; [evs; reflexivity | reflexivity | lia | lia | exact HROOM]. }

    xruns HR HK 100%nat (0x67258 :: STOPS) (SCR [] [] []) 50%N.
    { split_scs; try sc_auto1. }
    postrun.
    lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ =>
      replace m with (wslots M sp0 (SLOT_vals R ret)) end.
    2:{ unfold wslots, SLOT_vals. unfold Zlen. cbn [length Z.of_nat Z.of_N Pos.of_succ_nat Pos.succ].
        rewrite <- Hra. repeat first [reflexivity | progress f_equal]; try (f_equal; lia). }
    set (M1 := wslots M sp0 (SLOT_vals R ret)).
    assert (ST1 : stores_in (zwin (sp0 - 104) sp0) M M1).
    { unfold M1. apply (wslots_stores_in M sp0 (SLOT_vals R ret)); unfold Zlen; cbn; lia. }
    assert (HWD : mdef M (sp0 - 16384) 16384).
    { eapply store_ok_mdef_offimg; [exact HROOM | lia | lia | lia |]. intros x Hx. apply ly_noseg. lia. }
    assert (HWD1 : mdef M1 (sp0 - 16384) 16384) by (eapply stores_in_mdef; [exact ST1 | exact HWD]).
    rreg HR' (2%bv) Q2. rewrite w_addm in Q2 by lia.

    assert (OK0 : store_ok SEGS M1 (Z_to_bv 64 (sp0 + -864 + 752)) 8 = true).
    { change 8%nat with (Z.to_nat 8). apply store_ok_of_defined; [lia | lia |]. intros i Hi.
      pose proof (HWD1 (16384 - 112 + i) ltac:(lia)) as D. replace (sp0 - 16384 + (16384 - 112 + i)) with (sp0 + -864 + 752 + i) in D by lia. exact D. }
    fsd_step MS F_67208 D_67208 Q2 OK0 0x6724c.
    lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ => set (M2 := m) end.
    assert (ST2 : stores_in (zwin (sp0 - 128) sp0) M M2).
    { unfold M2. replace (sp0 + -864 + 752) with (sp0 - 112) by lia. eapply stores_in_wbytes_more;
        [eapply stores_in_weaken; [exact ST1 | intros a Ha; unfold zwin in *; lia] | lia | rewrite length_N_to_le_bytes; cbn; lia
        | intros a' Ha'; rewrite length_N_to_le_bytes in Ha'; cbn in Ha'; unfold zwin; lia]. }
    assert (HWD2 : mdef M2 (sp0 - 16384) 16384) by (eapply stores_in_mdef; [exact ST2 | exact HWD]).
    assert (OK1 : store_ok SEGS M2 (Z_to_bv 64 (sp0 + -864 + 744)) 8 = true).
    { change 8%nat with (Z.to_nat 8). apply store_ok_of_defined; [lia | lia |]. intros i Hi.
      pose proof (HWD2 (16384 - 120 + i) ltac:(lia)) as D. replace (sp0 - 16384 + (16384 - 120 + i)) with (sp0 + -864 + 744 + i) in D by lia. exact D. }
    fsd_step MS F_6720c D_6720c Q2 OK1 0x67250.
    lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ => set (M3 := m) end.
    assert (ST3 : stores_in (zwin (sp0 - 128) sp0) M M3).
    { unfold M3. replace (sp0 + -864 + 744) with (sp0 - 120) by lia. eapply stores_in_wbytes_more;
        [exact ST2 | lia | rewrite length_N_to_le_bytes; cbn; lia
        | intros a' Ha'; rewrite length_N_to_le_bytes in Ha'; cbn in Ha'; unfold zwin; lia]. }
    assert (HWD3 : mdef M3 (sp0 - 16384) 16384) by (eapply stores_in_mdef; [exact ST3 | exact HWD]).
    assert (OK2 : store_ok SEGS M3 (Z_to_bv 64 (sp0 + -864 + 736)) 8 = true).
    { change 8%nat with (Z.to_nat 8). apply store_ok_of_defined; [lia | lia |]. intros i Hi.
      pose proof (HWD3 (16384 - 128 + i) ltac:(lia)) as D. replace (sp0 - 16384 + (16384 - 128 + i)) with (sp0 + -864 + 736 + i) in D by lia. exact D. }
    fsd_step MS F_67210 D_67210 Q2 OK2 0x67254.
    lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ => set (M4 := m) end.
    assert (ST4 : stores_in (zwin (sp0 - 128) sp0) M M4).
    { unfold M4. replace (sp0 + -864 + 736) with (sp0 - 128) by lia. eapply stores_in_wbytes_more;
        [exact ST3 | lia | rewrite length_N_to_le_bytes; cbn; lia
        | intros a' Ha'; rewrite length_N_to_le_bytes in Ha'; cbn in Ha'; unfold zwin; lia]. }

    assert (SLOTS : forall k, 1 <= k <= 13 ->
      rdn SEGS M4 (Z_to_bv 64 (sp0 - 8 * k)) 8 = Some (word_to_le_bytes 8 (nth (Z.to_nat (13 - k)) (SLOT_vals R ret) (Z_to_bv 64 0)))).
    { intros k Hk. unfold M4, M3, M2.
      rewrite !rdn_wbytes_out_Z by (rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
      unfold M1. apply wslots_read; unfold Zlen; cbn; lia. }

    rreg HR' (10%bv) Q10. rreg HR' (3%bv) Q3. rreg HR' (4%bv) Q4.
    pose (E5 := Eseed R' [Z_to_bv 64 (sp0 - 864); Z_to_bv 64 p; getr R 3%bv; getr R 4%bv]).
    assert (HR5 : regs_ok E5 (srs sr_id [(2%bv, EVar 32); (10%bv, EVar 33); (3%bv, EVar 34); (4%bv, EVar 35)]) R').
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros XX; discriminate XX); evs; try assumption; rewrite Q2; f_equal; lia. }
    assert (HK5 : know_ok SEGS E5 M4 []) by constructor.
    clear HR'.
    xruns HR5 HK5 100%nat (0x67258 :: STOPS) (SCR [] [] []) 50%N. { split_scs. }
    rreg HR' (8%bv) G8. rreg HR' (10%bv) G10. rreg HR' (2%bv) G2. rreg HR' (3%bv) G3. rreg HR' (4%bv) G4.
    assert (AG1 : forall P : Z -> Prop, (forall a, P a -> sp0 <= a \/ a + 1 <= sp0 - 128) -> (forall a, P a -> 0 <= a < 2 ^ 64) -> CRep.agree_on P M M4).
    { intros P HP HPR. eapply stores_in_agree; [exact ST4|]. intros a Ha. split; [exact (HPR a Ha)|]. unfold zwin. pose proof (HP a Ha). lia. }
    assert (FLD : forall a k v, CRep.fld SEGS M a k v -> sp0 <= a -> a + Z.of_nat k < 2 ^ 64 -> CRep.fld SEGS M4 a k v).
    { intros a k v F Ha Hk. eapply fld_agree; [lia | exact Hk | exact F |]. apply AG1; intros x Hx; unfold zwin in Hx; lia. }
    destruct PR as [Pcons Puser Phdr Pins Phunk Pst Pdef Pal Prange Pconsf Pconsm Pconsd].
    destruct Pst as [Sw0 Sw1 Sw2 Sw3 Sw4 Sw5 Sw6 Sm1 Sm2 Sm3 Sv1 Sv2 Sv3 Sdef Sal Snd].
    pose proof FR as FR'. destruct FR' as (Fw & Fn & Fwi & Fic & Ffl & Fm1 & Fm2 & Fm3 & E1 & E2 & E3 & N1 & N2 & N3 & C1 & C2 & C3).
    destruct BUD as (Bcaps & Bbig & Bnmax & Bn & _).
    unfold ST_OFF in *.
    lazymatch goal with |- srealizes _ (mkCfg (mkst ?Rx _ _ _) _) _ => apply (CONT M4 Rx) end; [| exact G8 | exact G10 | exact G2 | exact G3 | exact G4].
    constructor; cbn [init_pmc mkw w_sp w_STK w_ret w_p w_cons w_user w_diag w_words w_n w_L0 w_R0 w_A0 w_M0 w_model0 w_s
                      c_widx c_icount c_endian c_reqconv c_m1 c_m2 c_m3 c_v1 c_v2 c_v3 c_tr t3a t3b t3c fst snd];
      unfold w_sp0; cbn [w_sp w_STK mkw]; unfold PM_FRAME.
    - eapply stores_in_ainv; [exact AI | exact ST4 |]. intros a Ha. apply Hwin. unfold zwin in *. lia.
    - exact MS.
    - reflexivity.
    - reflexivity.
    - eapply stores_in_sx; [exact SXI | exact ST4 |]. intros a Ha. apply (offimg_not_sx SEGS Ly.L ST ly_rw_img ly_relro_img). intros Hi. pose proof (ly_img_low _ Hi). unfold zwin in Ha. lia.
    - exact SXH.
    - eapply ro_clear_frame; [exact ROC | eapply stores_in_frame_eq; [exact ST4 | intros a Ha; exact Ha] |].
      intros a Hro Hw. destruct Hro as (Hi & _). pose proof (ly_img_low _ Hi). unfold zwin in Hw. lia.
    - replace (sp0 - 864 + 864) with sp0 by lia.
      apply (eff_store MI A M M4 (sp0 - 16384, sp0) (PMF MI (mkw sp0 16384 ret p c0 L0 R A M model s))); [| exact (proj2 ST4)].
      intros a HF HW. apply (proj1 ST4). intros Hz. apply HW. unfold W_of, zwin in *. cbn. lia.
    - exact Hown_sx.
    - exact Herr_sx.
    - replace (sp0 - 864 + 864) with sp0 by lia. intros a Ha. apply (proj2 (Hwin a Ha)).
    - replace (sp0 - 864 + 864) with sp0 by lia.
      repeat match goal with |- _ /\ _ => split end; try lia.
      + replace (sp0 - 864) with (sp0 - 16 * 54) by lia. apply mod16_sub. exact Hsp16.
      + exact Pconsd.
      + intros Hwz. destruct (WOK Hwz) as (W0 & W4 & Wn & Whi & Wdef & Wpl).
        repeat match goal with |- _ /\ _ => split end; try lia.
        * exact Wpl.
        * intros a Ha. destruct (WDJ Hwz a Ha) as [X1 X2]. split; [exact X1|]. intros Hp. apply X2. left. exact Hp.
    - replace (sp0 - 864 + 864) with sp0 by lia. eapply stores_in_mdef; [exact ST4 | exact HWD].
    - replace (sp0 - 864 + 864) with sp0 by lia. intros a Ha. apply (proj1 (Hwin a Ha)).
    - replace (sp0 - 864 + 864) with sp0 by lia. exact SLOTS.
    - eapply mdef_agree; [| apply AG1; intros a Ha; unfold zwin in Ha; lia].
      intros i Hi. unfold PARSER_SIZE in Hi. destruct (Z.lt_ge_cases i 48); [apply Pdef; lia|]. replace (p + i) with (p + 48 + (i - 48)) by lia. apply Sdef. lia.
    - apply FLD; [exact Pcons | lia | cbn; lia].
    - apply FLD; [exact Puser | lia | cbn; lia].
    - apply FLD; [exact Phdr | lia | cbn; lia].
    - apply FLD; [exact Pins | lia | cbn; lia].
    - apply FLD; [exact Phunk | lia | cbn; lia].
    - unfold O_WORDS. apply FLD; [exact (proj2 Sw0) | lia | cbn; lia].
    - unfold O_N. replace (p + 56) with (p + 48 + 8) by lia. apply FLD; [exact (proj2 Sw1) | lia | cbn; lia].
    - unfold O_DIAG. replace (p + 64) with (p + 48 + 16) by lia. apply FLD; [exact (proj2 Sw2) | lia | cbn; lia].
    - unfold O_WIDX. replace (p + 72) with (p + 48 + 24) by lia. apply FLD; [exact (proj2 Sw3) | lia | cbn; lia].
    - unfold O_ICOUNT. replace (p + 80) with (p + 48 + 32) by lia. apply FLD; [exact (proj2 Sw4) | lia | cbn; lia].
    - unfold O_ENDIAN. replace (p + 88) with (p + 48 + 40) by lia. apply FLD; [exact (proj2 Sw5) | lia | cbn; lia].
    - unfold O_FLAGS. replace (p + 92) with (p + 48 + 44) by lia. apply FLD; [exact (proj2 Sw6) | lia | cbn; lia].
    - pose proof (proj1 Sw5) as R5. cbn in R5. rewrite Fwi, Fic, Ffl. lia.
    - apply FLD; [exact Pconsf | lia | cbn; lia].
    - eapply mdef_agree; [exact Pconsm|]. apply AG1; intros a Ha; unfold zwin in Ha; lia.
    - intros Hwz. destruct (WOK Hwz) as (W0 & W4 & Wn & Whi & Wdef & Wpl). eapply mdef_agree; [exact Wdef|].
      apply AG1; intros a Ha; unfold zwin in Ha; [| lia]. destruct (WDJ Hwz a ltac:(unfold zwin; lia)) as [X1 _]. unfold zwin in X1. lia.
    - unfold O_M1. replace (p + 96) with (p + 48 + 48) by lia.
      eapply (umapx_hi_stores SEGS Ly.L MI 24 Z (nval24 SEGS) (nval24_agree SEGS) ltac:(lia));
        [exact Sm1 | exact AI | exact ST4 | intros a Ha; unfold zwin in Ha; lia].
    - unfold O_M2. replace (p + 136) with (p + 48 + 88) by lia.
      eapply (umapx_hi_stores SEGS Ly.L MI 32 (Z * Z * Z)%type (nval32 SEGS) (nval32_agree SEGS) ltac:(lia));
        [exact Sm2 | exact AI | exact ST4 | intros a Ha; unfold zwin in Ha; lia].
    - unfold O_M3. replace (p + 176) with (p + 48 + 128) by lia.
      eapply (umapx_hi_stores SEGS Ly.L MI 24 Z (nval24 SEGS) (nval24_agree SEGS) ltac:(lia));
        [exact Sm3 | exact AI | exact ST4 | intros a Ha; unfold zwin in Ha; lia].
    - unfold O_V1. replace (p + 216) with (p + 48 + 168) by lia.
      eapply vec_opnd_relive; [eapply vec_opnd_frame; [eapply (vec_opnd_of_vraw_empty A M model); [exact AI | | exact N1 | | lia | lia] |] | intros _ Hl; exact Hl].
      + rewrite <- C1. rewrite E1 at 2. exact Sv1.
      + intros i Hi. replace (p + 48 + 168 + i) with (p + 48 + (168 + i)) by lia. apply Sdef. lia.
      + apply AG1; intros a Ha; unfold vec_opnd_fp, zwin in Ha; lia.
    - unfold O_V2. replace (p + 240) with (p + 48 + 192) by lia.
      eapply vec32_relive; [eapply vec32_frame; [eapply (vec32_of_vraw_empty A M model); [exact AI | | exact N2 | | lia | lia] |] | intros _ Hl; exact Hl].
      + rewrite <- C2. rewrite E2 at 2. exact Sv2.
      + intros i Hi. replace (p + 48 + 192 + i) with (p + 48 + (192 + i)) by lia. apply Sdef. lia.
      + apply AG1; intros a Ha; unfold vec32_fp, zwin, Zlen in Ha; cbn in Ha; lia.
    - unfold O_V3. replace (p + 264) with (p + 48 + 216) by lia.
      eapply vec32_relive; [eapply vec32_frame; [eapply (vec32_of_vraw_empty A M model); [exact AI | | exact N3 | | lia | lia] |] | intros _ Hl; exact Hl].
      + rewrite <- C3. rewrite E3 at 2. exact Sv3.
      + intros i Hi. replace (p + 48 + 216 + i) with (p + 48 + (216 + i)) by lia. apply Sdef. lia.
      + apply AG1; intros a Ha; unfold vec32_fp, zwin, Zlen in Ha; cbn in Ha; lia.
    - rewrite <- (init_blocks c0 FR) in PERM. exact PERM.
    - split; [exact Bcaps|]. split; [exact Bbig|]. exact Bnmax.
  Qed.
End PM.
