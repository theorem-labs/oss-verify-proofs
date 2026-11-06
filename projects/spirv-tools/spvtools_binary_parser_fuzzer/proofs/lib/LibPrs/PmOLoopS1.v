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
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep2S1.PmUpd. From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PmStep2S1 PmLoopS1 PmBody1S1 PmStep3S1 PmODefsS1 PmBody2S1 PmZw.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PeLia.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Local Ltac lia ::= pe3_lia.
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

  #[local] Notation izero := (PmBody1S1.izero).
  #[local] Notation ictx := (PmBody1S1.ictx).
  #[local] Notation nodes := (PmLoopS1.nodes).
  #[local] Notation macct := (PmLoopS1.macct).
  #[local] Notation ipure := (PmODefsS1.ipure (G:=G) (idesc:=idesc)).
  #[local] Notation arm_stmt := (PmODefsS1.arm_stmt (MI:=MI) (ST:=ST) (G:=G) (idesc:=idesc)).

  Lemma flags_hi_byte : forall M (p v : Z),
    fld SEGS M (p + 92) 2 v -> (v = 0 \/ v = 1) -> 0 <= p -> p + 94 < 2 ^ 64 -> cellw SEGS M (p + 93) 1 0.
  Proof using.
    intros M p v F Hv Hp Hhi. split; [cbn; lia|]. unfold CRep.fld in *.
    pose proof (rdn_skipn SEGS M 2 (Z_to_bv 64 (p + 92)) _ 1 F ltac:(lia)) as R.
    rewrite zbv_add_nat in R by lia. replace (p + 92 + Z.of_nat 1) with (p + 93) in R by lia.
    change (N.to_nat 1) with (2 - 1)%nat. rewrite R. destruct Hv as [-> | ->]; reflexivity.
  Qed.

  Lemma pm_check_err : forall (w : pmw MI ST) c0 K (fx : FPState), PMS w c0 K -> frm_zero (@fp_csr fx) -> CHECKK w K fx.
  Proof using AC MI ST.
    intros w c0 K fx PS FZ A M model c R e X Htr BUD Qsp Qgp Qtp Qs0 Qs10 He.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & Gc2 & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof (x_scal X) as (_ & _ & _ & Sc4).
    pose proof (flags_hi_byte M (w_p w) (c_reqconv c) ltac:(pose proof (x_flags X) as F; unfold O_FLAGS in F; exact F) Sc4 ltac:(lia) ltac:(lia)) as C93.
    pose (E := Eseed R [Z_to_bv 64 (w_sp w); Z_to_bv 64 (w_p w); sxw e]).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (26%bv, EVar 34)] R.
    assert (HK : know_ok SEGS E M [KWord (SA (EVar 33) 93) (N.to_nat 1) (ELit 0)]).
    { repeat apply Forall_cons; try apply Forall_nil.
      eapply kword_var; [exact C93 | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | cbn [edenot]; reflexivity]. }
    xruns HR HK 100%nat STOPS (SCR [true] [] []) 50%N.
    { split_scs; try sc_auto1. all: cbn [sc_denot]; evs. all: rewrite PmLoopS1.sextw_sxw by lia; change (Z_to_bv 64 0) with (sxw 0); rewrite br_ne_sxw by lia; bool_lia. }
    postrun. name_run HRn R1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (26%bv) G26.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (PmLoopS1.pm_latch_err w c0 K fx A M model c R1 e PS X Htr BUD FZ G2 G3 G4 G26 He).
  Qed.

  Lemma pm_X1 : forall (w : pmw MI ST) c0 K (fx : FPState) A M model c R (io op t : Z),
    PMS w c0 K -> frm_zero (@fp_csr fx) -> PMX w A M model c -> c_tr c = [] -> pm_bud (w_n w) c -> oregs w R ->
    getr R 23%bv = Z_to_bv 64 io -> getr R 25%bv = Z_to_bv 64 op -> getr R 21%bv = Z_to_bv 64 t ->
    0 <= io < 2 ^ 63 -> 0 <= op < 2 ^ 16 -> 0 <= t < 2 ^ 32 ->
    srealizes SEGS (cfg fx R 0x66e74 M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx A M model c R io op t PS FZ X Htr BUD OR Q23 Q25 Q21 Hio Hop Ht.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & Gc2 & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof OR as OR'. destruct OR' as (Qsp & Qgp & Qtp & Qs0 & Qs1 & Qs3 & Qs4 & Qs8).
    pose (E := Eseed R [Z_to_bv 64 (w_sp w); Z_to_bv 64 (w_p w); Z_to_bv 64 io; Z_to_bv 64 op; Z_to_bv 64 t]).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (23%bv, EVar 34); (25%bv, EVar 35); (21%bv, EVar 36)] R.
    assert (HK : know_ok SEGS E M []) by (apply Forall_nil).
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R1.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12. rreg HRn (13%bv) G13.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_exhausted w c0 K fx A M model c R1 io op t _ PS X BUD ltac:(rewrite Htr; unfold Zlength; cbn; lia) ltac:(cregs_tac G1 G2 G3 G4) G10 G11 G12 G13 Hio Hop Ht).
    intros A' R' M' model' X' KEPT Hres AG.
    keptQ KEPT G2 Qsp'. keptQ KEPT G3 Qgp'. keptQ KEPT G4 Qtp'. keptQ KEPT G8 Qs0'.
    try clear E. pm_seed R' w c [Z_to_bv 64 (2 ^ 64 - 4)].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (10%bv, EVar 39)] R'.
    assert (HK : know_ok SEGS E M' []) by (apply Forall_nil). pose proof (x_ms X') as MS'.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R2. rreg HRn (2%bv) T2. rreg HRn (3%bv) T3. rreg HRn (4%bv) T4. rreg HRn (8%bv) T8. rreg HRn (26%bv) T26.
    clear HRn HR HK. fixregs. rewrite Qgp' in T3. rewrite Qtp' in T4.
    eapply (pm_check_err w c0 K fx PS FZ A' M' model' c R2 (2 ^ 32 - 4) X' Htr BUD T2 T3 T4 T8); [| lia].
    rewrite T26. unfold sxw. apply bv_eq. reflexivity.
  Qed.

  #[local] Notation pmx_updS := (pmx_upd SEGS Ly.L MI ST ly_img_low ly_rw_img ly_relro_img ly_errno_img ly_rw_not_relro ly_errno_rw).
  #[local] Notation live_splitS := (live_split SEGS Ly.L MI ST).
  #[local] Notation live_joinS := (live_join SEGS Ly.L MI ST).
  #[local] Notation vec_xferS := (vec_xfer SEGS Ly.L MI).

  Lemma pm_opnd_pb : forall (w : pmw MI ST) c0 K (fx : FPState) A M model c R (src ret : Z),
    PMS w c0 K -> PMX w A M model c -> c_tr c = [] -> pm_bud (w_n w) c ->
    cregs w R ret -> getr R 10%bv = Z_to_bv 64 (w_p w + O_V1) -> getr R 11%bv = Z_to_bv 64 src ->
    w_sp w <= src -> src + 20 <= w_sp0 w - 104 ->
    (t3b (c_v1 c) = t3c (c_v1 c) -> 40 * t3c (c_v1 c) + 20 <= 2 ^ 23) ->
    (forall A' R' M' model' (b' cap' : Z),
        PMX w A' M' model' (set_v1 c (b', t3b (c_v1 c) + 1, cap')) -> pm_bud (w_n w) (set_v1 c (b', t3b (c_v1 c) + 1, cap')) ->
        kept R R' -> CRep.agree_on (fun a => w_sp w <= a < w_sp0 w) M M' ->
        srealizes SEGS (cfg fx R' ret M' model') K) ->
    srealizes SEGS (cfg fx R (vc_entry (kv_opnd_pb ccS1)) M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx A M model c R src ret PS X Htr BUD CR Ha0 Ha1 Hs1 Hs2 Hgrow CONT.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ai X) as AI.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & Gc2 & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof (cl_mstack _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL) as HMS.
    pose proof (x_caps X) as (_ & _ & HNMAX). unfold LIB_NMAX in HNMAX.
    pose proof BUD as BUD'. destruct BUD' as (_ & _ & _ & _ & Bv1 & _).
    destruct (c_v1 c) as [[b n] cap] eqn:Ev1. cbn [t3a t3b t3c fst snd] in *.
    pose proof (x_v1 X) as V. rewrite Ev1 in V. cbn [t3a t3b t3c fst snd] in V.
    pose proof V as V0. destruct V0 as (_ & _ & _ & Hlen & Hblk & _).
    eapply ((cl_opnd_pb _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL) fx A (w_s w) R M model (w_sp w) ret (w_p w + O_V1) b cap src n K).
    - eapply pmx_cregs_callB; [exact X | exact CR | cbn [vc_stack kv_opnd_pb ccS1]; unfold NEW_STACK, PM_FRAME; lia].
    - exact Ha0. - exact Ha1. - exact V.
    - split; [left; unfold O_V1; lia | intros a Ha; cbn [vc_stack kv_opnd_pb ccS1]; unfold zwin, O_V1, NEW_STACK in *; lia].
    - exact (x_roc X).
    - eapply mdef_sub; [exact (x_wdef X) | unfold w_sp0, PM_FRAME; lia | unfold w_sp0, PM_FRAME; lia].
    - split; [left; lia | intros a Ha; cbn [vc_stack kv_opnd_pb ccS1]; unfold zwin, NEW_STACK in *; lia].
    - lia. - lia.
    - intros a Ha. unfold zwin, O_V1, OPND_SZ in *. split; [lia|]. intros [Hb Hz].
      destruct Hblk as [[-> _]|(_ & _ & _ & _ & Hl & _)]; [lia|]. destruct (ai_live_block MI A M model _ _ AI Hl) as (_ & _ & _ & Hc' & _). unfold OPND_SZ in Hc'. lia.
    - unfold vgrow, OPND_SZ in *. lia.
    - intros Hfull. eapply pmx_ds_room; [exact PS | exact X | exact BUD | unfold vgrow, OPND_SZ, DS_MAXBLK in *; lia].
    - intros A' R' M' model' b' cap' RB V' HX EF. destruct RB as [AI' MS' FS' FDS' SX' KEPT].
      pose proof V' as V1. destruct V1 as (_ & _ & _ & Hlen' & Hblk' & _).
      set (c' := set_v1 c (b', n + 1, cap')).
      assert (X' : PMX w A' M' model' c').
      { eapply (pmx_updS w CV1 A M model c A' M' model' c' (vc_stack (kv_opnd_pb ccS1) + NEW_STACK SEGS Ly.L MI) _ X AI' MS' FS' FDS' EF);
          [cbn [vc_stack kv_opnd_pb ccS1]; unfold NEW_STACK, PM_FRAME; lia | | | intros j Hj; destruct j; cbn; first [reflexivity | exfalso; exact (Hj eq_refl)]
          | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | cbn; exact V' |].
        + intros a [Ha|[[Hb Ha]|Ha]].
          * left. left. unfold O_V1 in *. cbn. exact Ha.
          * left. right. exists (b, OPND_SZ * cap). cbn. rewrite Ev1. cbn. unfold vec_opnd_blocks. destruct (Z.eqb_spec b 0); [lia|]. split; [left; reflexivity | unfold zwin in Ha; cbn; lia].
          * right. left. right. exists (b', OPND_SZ * cap'). cbn. unfold vec_opnd_blocks. destruct (Z.eqb_spec b' 0); [unfold zwin in Ha; lia|]. split; [left; reflexivity | unfold zwin in Ha; cbn; lia].
        + intros a [Ha|[[Hb Ha]|Ha]] Hz; exfalso; unfold zwin, O_V1, w_sp0, PM_FRAME in *; [lia | |].
          * destruct Hblk as [[-> _]|(_ & _ & _ & _ & Hl & _)]; [lia|]. destruct (ai_live_block MI A M model _ _ AI Hl) as (_ & _ & _ & Hc' & _). lia.
          * destruct Hblk' as [[-> ->]|(_ & _ & _ & _ & Hl & _)]; [lia|]. destruct (ai_live_block MI A' M' model' _ _ AI' Hl) as (_ & _ & _ & Hc' & _). lia.
        + eapply (live_joinS w A' c c' CV1); [intros j Hj; destruct j; cbn; first [reflexivity | exfalso; exact (Hj eq_refl)] | reflexivity |].
          cbn [cblocks c' set_v1 c_v1 t3a t3c fst snd]. unfold vec_opnd_blocks.
          eapply (vec_xferS A A' M M' model model' b cap b' cap' OPND_SZ); [exact AI | exact AI' | unfold OPND_SZ; lia | | | | ].
          * pose proof (live_splitS w A M model c CV1 X) as P. cbn [cblocks] in P. rewrite Ev1 in P. cbn [t3a t3c fst snd] in P. unfold vec_opnd_blocks in P. exact P.
          * intros Hb. destruct Hblk as [[? ?]|(_ & _ & Hc & _)]; lia.
          * destruct HX as [(Hlt & -> & -> & E)|(Heq & -> & LA)]; [left; auto | right; split; [unfold vgrow; lia | exact LA]].
          * intros ->. destruct Hblk' as [[_ ->]|(Hb0 & _)]; [reflexivity | lia]. }
      eapply CONT; [exact X' | | exact KEPT |].
      + destruct BUD as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9). unfold pm_bud. cbn [c' set_v1 c_m1 c_m2 c_m3 c_v1 c_v2 c_v3 c_tr t3a t3b t3c fst snd].
        rewrite Ev1 in *. cbn [t3a t3b t3c fst snd] in *.
        repeat (split; [assumption|]). split; [| split; [assumption | split; [assumption | split; assumption]]].
        destruct HX as [(Hlt & -> & -> & E)|(Heq & -> & LA)]; [lia | unfold vgrow, OPND_SZ in *; lia].
      + eapply (pmx_frame_keep SEGS Ly.L MI ST ly_img_low ly_rw_img ly_errno_img); [exact X | exact EF | cbn [vc_stack kv_opnd_pb ccS1]; unfold NEW_STACK; lia |].
        intros a Ha. split; [exact Ha|]. unfold zwin, O_V1, w_sp0, PM_FRAME in *. intros [Hh|[[Hb Hh]|Hh]]; [lia | |].
        * destruct Hblk as [[-> _]|(_ & _ & _ & _ & Hl & _)]; [lia|]. destruct (ai_live_block MI A M model _ _ AI Hl) as (_ & _ & _ & Hc' & _). lia.
        * destruct Hblk' as [[-> ->]|(_ & _ & _ & _ & Hl & _)]; [lia|]. destruct (ai_live_block MI A' M' model' _ _ AI' Hl) as (_ & _ & _ & Hc' & _). lia.
  Qed.

  Definition CSREGS : list reg := [18; 19; 20; 21; 24]%bv.

  Lemma pm_copy_loop : forall (k : nat) (w : pmw MI ST) c0 K (fx : FPState) (I : ictxR) A M model c R (src ia : Z),
    PMS w c0 K -> frm_zero (@fp_csr fx) ->
    PMX w A M model c -> c_tr c = [] -> pm_bud (w_n w) c -> oregs w R -> loop_mem w M ->
    ictx w M (i_io I) (i_fw I) (i_iwc I) (i_op I) (i_d I) -> ifr w M ->
    getr R 18%bv = Z_to_bv 64 ia -> getr R 21%bv = Z_to_bv 64 (c_endian c) -> c_endian c < 2 ->
    getr R 22%bv = Z_to_bv 64 src -> getr R 23%bv = Z_to_bv 64 (4 * Z.of_nat k) -> (0 < k)%nat ->
    w_words w <> 0 -> w_words w <= src -> src + 4 * Z.of_nat k <= w_words w + 4 * w_n w -> src mod 4 = 0 ->
    Zlen (t3b (c_v2 c)) + Z.of_nat k <= 2 ^ 17 ->
    (forall A' M' model' R' (b2 cap2 : Z) (xs2 : list Z),
        PMX w A' M' model' (set_v2 c (b2, xs2, cap2)) -> pm_bud (w_n w) (set_v2 c (b2, xs2, cap2)) ->
        Zlen xs2 = Zlen (t3b (c_v2 c)) + Z.of_nat k ->
        oregs w R' -> getr R' 18%bv = Z_to_bv 64 ia -> loop_mem w M' ->
        ictx w M' (i_io I) (i_fw I) (i_iwc I) (i_op I) (i_d I) -> ifr w M' ->
        srealizes SEGS (cfg fx R' 0x6712c M' model') K) ->
    srealizes SEGS (cfg fx R 0x67104 M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    induction k as [|k IH]; [intros; lia|].
    intros w c0 K fx I A M model c R src ia PS FZ X Htr BUD OR LM IC IFR Q18 Q21 He2 Q22 Q23 _ Hw Hs1 Hs2 Hs4 Hlen CONT.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & Gc2 & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof (x_scal X) as (Sc1 & Sc2 & Sc3 & Sc4).
    pose proof OR as OR'. destruct OR' as (Qsp & Qgp & Qtp & Qs0 & Qs1 & Qs3 & Qs4 & Qs8).
    destruct (Gw Hw) as (W1 & W2 & W3 & W4 & W5).

    destruct (mdef_cell4 M src ltac:(eapply mdef_sub; [exact (x_wbuf X Hw) | lia | lia]) ltac:(lia) ltac:(lia)) as (raw & Craw).
    pose proof (proj1 Craw) as Rraw. cbn in Rraw.
    pm_seed R w c [Z_to_bv 64 src; Z_to_bv 64 (c_endian c); Z_to_bv 64 raw; Z_to_bv 64 ia; Z_to_bv 64 (4 * Z.of_nat (S k))].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (22%bv, EVar 39); (21%bv, EVar 40); (18%bv, EVar 42); (23%bv, EVar 43)] R. seedHK HK w A M model c E X.
    apply (know_more E M [KWord (SA (EVar 39) 0) (N.to_nat 4) (EVar 41)]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil.
         eapply kword_var; [rewrite Z.add_0_r; exact Craw | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity]. }
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R1.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (9%bv) G9. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11.
    rreg HRn (18%bv) G18. rreg HRn (21%bv) G21. rreg HRn (22%bv) G22. rreg HRn (23%bv) G23.
    pose proof (syms_id_sound _ _ _ _ OSREGS HRn eq_refl) as GS.
    clear HRn HR HK. fixregs. pose proof (oregs_glue w R R1 OR GS G2 G3 G4 G8 (or_introl G9)) as OR1. clear GS G9.
    rewrite Qgp in G3. rewrite Qtp in G4. rewrite ext_val_sx4 in G10 by lia.
    assert (He32 : 0 <= c_endian c < 2 ^ 32) by lia.

    eapply (pm_fixword w A M model c fx R1 _ K X (ex_intro _ raw (ex_intro _ (c_endian c) (conj Rraw (conj G10 (conj He32 G11))))) G1 ltac:(apply bv_eq; vm_compute; reflexivity)).
    intros R2 KEPT (r & Rr & Hr). rewrite TablStmts.sx32_prs in Hr.
    keptQ KEPT G2 Qsp2. keptQ KEPT G8 Qs02. keptQ KEPT G3 Qgp2. keptQ KEPT G4 Qtp2. keptQ KEPT G18 Q18b. keptQ KEPT G21 Q21b. keptQ KEPT G22 Q22b. keptQ KEPT G23 Q23b.
    pose proof (oregs_kept w R1 R2 OR1 KEPT) as OR2. clear G1 G2 G3 G4 G8 G10 G11 G18 G21 G22 G23 KEPT OR1.
    assert (Qs12 : getr R2 9%bv = Z_to_bv 64 (w_p w + 240)) by (destruct OR2 as (_ & _ & _ & _ & Q & _); exact Q).

    try clear E. pm_seed R2 w c [Z_to_bv 64 (PrsNeeds.sx32 r); Z_to_bv 64 (w_p w + 240); Z_to_bv 64 ia; Z_to_bv 64 src; Z_to_bv 64 (4 * Z.of_nat (S k)); Z_to_bv 64 (c_endian c)].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (10%bv, EVar 39); (9%bv, EVar 40); (18%bv, EVar 41); (22%bv, EVar 42); (23%bv, EVar 43); (21%bv, EVar 44)] R2. seedHK HK w A M model c E X.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R3.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (9%bv) G9. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11.
    rreg HRn (18%bv) G18. rreg HRn (21%bv) G21. rreg HRn (22%bv) G22. rreg HRn (23%bv) G23.
    pose proof (syms_id_sound _ _ _ _ OSREGS HRn eq_refl) as GS.
    clear HRn HR HK. fixregs. pose proof (oregs_glue w R2 R3 OR2 GS G2 G3 G4 G8 (or_intror G9)) as OR3. clear GS G9.
    rewrite Qgp2 in G3. rewrite Qtp2 in G4. rewrite w_add in G11 by lia.
    rewrite (PmBody1S1.w2lb4_sx32 r) by lia.
    lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ => set (M1 := m) in * end.
    assert (ST1 : stores_in (zwin (w_sp w + 272) (w_sp w + 276)) M M1) by (unfold M1; stin).
    assert (X1 : PMX w A M1 model c).
    { eapply (pmx_frame_stores SEGS Ly.L MI ST ly_img_low ly_rw_img ly_relro_img w A M M1 model c (zwin (w_sp w + 272) (w_sp w + 276)));
        [exact X | exact ST1 | unfold zwin, w_sp0, PM_FRAME; intros; lia]. }
    eapply (PmBody1S1.loop_mem_frame w M M1) in LM; [| lia | lia | eapply stores_in_agree; [exact ST1 | unfold zwin; intros; lia]].
    eapply (PmBody1S1.ictx_agree w M M1) in IC; [| lia | lia | eapply stores_in_agree; [exact ST1 | unfold zwin; intros; lia]].
    eapply (ifr_agree w M M1) in IFR; [| lia | lia | eapply stores_in_agree; [exact ST1 | unfold zwin; intros; lia]].
    assert (Fr : fld SEGS M1 (w_sp w + 272) 4 r) by (unfold M1; rdback).
    clear ST1 X MS Craw. clearbody M1. pose proof (x_ms X1) as MS1.
    eapply (pm_ecw_pb (kv_ecw_pb2 ccS1) (cl_ecw_pb2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL) eq_refl w c0 K fx A M1 model c R3 (w_sp w + 272) r _ PS X1 Htr BUD
              ltac:(cregs_tac G1 G2 G3 G4));
      [unfold O_V2; exact G10 | exact G11 | exact Fr | lia | lia | unfold w_sp0, PM_FRAME; lia
      | intros H0; unfold vgrow in *; lia |].
    intros A4 R4 M4 model4 b2' cap2' X4 BUD4 KEPT AG.
    pose proof (oregs_kept w R3 R4 OR3 KEPT) as OR4.
    keptQ KEPT G2 Qsp4. keptQ KEPT G8 Qs04. keptQ KEPT G3 Qgp4. keptQ KEPT G4 Qtp4. keptQ KEPT G18 Q18d. keptQ KEPT G21 Q21d. keptQ KEPT G22 Q22d. keptQ KEPT G23 Q23d.
    clear G1 G2 G3 G4 G8 G10 G11 G18 G21 G22 G23 KEPT OR3 OR2 Qsp2 Qs02 Qgp2 Qtp2 Qs12 Q18b Q21b Q22b Q23b.
    eapply (PmBody1S1.loop_mem_frame w M1 M4) in LM; [| lia | lia | eapply agree_on_weaken; [exact AG | unfold zwin, w_sp0, PM_FRAME; intros; lia]].
    eapply (PmBody1S1.ictx_agree w M1 M4) in IC; [| lia | lia | eapply agree_on_weaken; [exact AG | unfold zwin, w_sp0, PM_FRAME; cbn; intros; lia]].
    eapply (ifr_agree w M1 M4) in IFR; [| lia | lia | eapply agree_on_weaken; [exact AG | unfold zwin, w_sp0, PM_FRAME; cbn; intros; lia]].
    clear AG X1 MS1 M1 Fr. pose proof (x_ms X4) as MS4.
    set (c4 := set_v2 c (b2', t3b (c_v2 c) ++ [r], cap2')) in *.

    destruct k as [|k'].
    -
      try clear E. pm_seed R4 w c4 [Z_to_bv 64 src; Z_to_bv 64 4; Z_to_bv 64 ia].
      seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (22%bv, EVar 39); (23%bv, ELit 4); (18%bv, EVar 41)] R4. seedHK HK w A4 M4 model4 c4 E X4.
      xruns HR HK 100%nat (0x6712c :: STOPS) (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
      postrun. name_run HRn R5.
      rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (9%bv) G9. rreg HRn (18%bv) G18.
      pose proof (syms_id_sound _ _ _ _ OSREGS HRn eq_refl) as GS.
      clear HRn HR HK. fixregs. pose proof (oregs_glue w R4 R5 OR4 GS G2 G3 G4 G8 (or_introl G9)) as OR5. clear GS G9.
      eapply (CONT A4 M4 model4 R5 b2' cap2' (t3b (c_v2 c) ++ [r]) X4 BUD4); [| exact OR5 | exact G18 | exact LM | exact IC | exact IFR].
      unfold Zlen. rewrite length_app. cbn [length]. lia.
    -
      try clear E. pm_seed R4 w c4 [Z_to_bv 64 src; Z_to_bv 64 (4 * Z.of_nat (S (S k'))); Z_to_bv 64 ia; Z_to_bv 64 (c_endian c)].
      seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (22%bv, EVar 39); (23%bv, EVar 40); (18%bv, EVar 41); (21%bv, EVar 42)] R4. seedHK HK w A4 M4 model4 c4 E X4.
      apply (know_more E M4 [KRange (EVar 40) 8 (2 ^ 40)]) in HK.
      2: { repeat apply Forall_cons; try apply Forall_nil. eapply krange_var; [evs; reflexivity | lia | lia]. }
      xruns HR HK 100%nat (0x67104 :: 0x6712c :: STOPS) (SCR [true] [] []) 50%N. { split_scs; try sc_auto1. }
      postrun. name_run HRn R5.
      rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (9%bv) G9. rreg HRn (18%bv) G18. rreg HRn (21%bv) G21. rreg HRn (22%bv) G22. rreg HRn (23%bv) G23.
      pose proof (syms_id_sound _ _ _ _ OSREGS HRn eq_refl) as GS.
      clear HRn HR HK. fixregs. pose proof (oregs_glue w R4 R5 OR4 GS G2 G3 G4 G8 (or_introl G9)) as OR5. clear GS G9.
      rewrite SymExec.alu64_add_lit in G22, G23.
      eapply (IH w c0 K fx I A4 M4 model4 c4 R5 (src + 4) ia PS FZ X4 Htr BUD4 OR5 LM IC IFR G18);
        [cbn [c4 set_v2 c_endian]; exact G21 | cbn [c4 set_v2 c_endian]; exact He2 | exact G22
        | rewrite G23; f_equal; lia | lia | exact Hw | lia | lia | replace (src + 4) with (src + 1 * 4) by lia; rewrite Z_mod_plus_full; exact Hs4 | | ].
      + cbn [c4 set_v2 c_v2 t3b fst snd]. unfold Zlen in *. rewrite length_app. cbn [length]. lia.
      + intros A' M' model' R' b2 cap2 xs2 X' BUD' Hl OR' Q18' LM' IC' IFR'.
        eapply (CONT A' M' model' R' b2 cap2 xs2); [exact X' | exact BUD' | | exact OR' | exact Q18' | exact LM' | exact IC' | exact IFR'].
        cbn [c4 set_v2 c_v2 t3b fst snd] in Hl. unfold Zlen in *. rewrite length_app in Hl. cbn [length] in Hl. lia.
  Qed.

  Lemma flags_lo_byte : forall M (p v : Z),
    fld SEGS M (p + 92) 2 v -> (v = 0 \/ v = 1) -> cellw SEGS M (p + 92) 1 v.
  Proof using.
    intros M p v F Hv. split; [cbn; lia|]. unfold CRep.fld in *.
    pose proof (rdn_firstn SEGS M 2 (Z_to_bv 64 (p + 92)) _ 1 F ltac:(lia)) as R.
    change (N.to_nat 1) with 1%nat. rewrite R. destruct Hv as [-> | ->]; reflexivity.
  Qed.

  Lemma pm_push_tail : forall (w : pmw MI ST) c0 K (fx : FPState) (I : ictxR) A M model c R (t nw : Z),
    PMS w c0 K -> frm_zero (@fp_csr fx) -> ipure I ->
    OBASE w I A M model c R ->
    getr R 21%bv = Z_to_bv 64 t -> getr R 23%bv = Z_to_bv 64 (i_io I) -> getr R 25%bv = Z_to_bv 64 (i_op I) -> 0 <= t < 2 ^ 32 ->
    cellw SEGS M (w_sp w + 686) 2 nw ->
    i_io I + 1 <= c_widx c -> c_widx c < i_io I + i_iwc I ->
    Zlen (t3b (c_v2 c)) <= c_widx c - i_io I ->
    (t3b (c_v1 c) = t3c (c_v1 c) -> 40 * t3c (c_v1 c) + 20 <= 2 ^ 23) ->
    (forall A' M' model' R' (b1 cap1 : Z) (v2 : Z * list Z * Z),
        OBASE w I A' M' model' (set_scal (set_v2 (set_v1 c (b1, t3b (c_v1 c) + 1, cap1)) v2) (c_widx c + nw) (c_icount c) (c_endian c) (c_reqconv c)) R' ->
        Zlen (t3b v2) <= Zlen (t3b (c_v2 c)) + nw -> c_widx c + nw <= w_n w ->
        srealizes SEGS (cfg fx R' 0x66e94 M' model') K) ->
    srealizes SEGS (cfg fx R 0x670c4 M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx I A M model c R t nw PS FZ IP OB Q21 Q23 Q25 Ht Cnw Hw1 Hw2 Hv2 Hgrow HEADK.
    destruct OB as (X & Htr & BUD & OR & LM & IC & IFR & Hic & He2 & Hw & MACC & FR3).
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & Gc2 & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof (x_scal X) as (Sc1 & Sc2 & Sc3 & Sc4). pose proof (ipure_ranges I IP) as (Riwc & Rop). pose proof IP as IP'. destruct IP' as (_ & _ & _ & _ & _ & _ & Rio).
    pose proof OR as OR'. destruct OR' as (Qsp & Qgp & Qtp & Qs0 & Qs1 & Qs3 & Qs4 & Qs8).
    pose proof (proj1 Cnw) as Rnw. cbn in Rnw.

    pm_seed R w c (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R. seedHK HK w A M model c E X.
    apply (know_more E M [KWord (SA (EVar 32) 136) (N.to_nat 8) (EAlu ALU_ADD (EVar 33) (ELit 216))]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil.
         eapply kword_var; [eapply (PmBody1S1.loop_mem_cell w _ 136 (w_p w + 216) LM); [(first [ solve [cbn [In]; repeat (first [left; reflexivity | right])] | cbn; repeat (first [left; reflexivity | right]) ]) | lia] | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | cbn [edenot]; evs; rewrite w_add by lia; reflexivity]. }
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R1.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (9%bv) G9. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11.
    rreg HRn (21%bv) G21. rreg HRn (23%bv) G23. rreg HRn (25%bv) G25.
    pose proof (syms_id_sound _ _ _ _ OSREGS HRn eq_refl) as GS.
    clear HRn HR HK. fixregs. pose proof (oregs_glue w R R1 OR GS G2 G3 G4 G8 (or_introl G9)) as OR1. clear GS G9.
    rewrite Qgp in G3. rewrite Qtp in G4. rewrite w_add in G10, G11 by lia.
    replace (Z_to_bv 5 (Z.of_N 21)) with (21%bv : reg) in G21 by (apply bv_eq; reflexivity). rewrite Q21 in G21.
    replace (Z_to_bv 5 (Z.of_N 23)) with (23%bv : reg) in G23 by (apply bv_eq; reflexivity). rewrite Q23 in G23.
    replace (Z_to_bv 5 (Z.of_N 25)) with (25%bv : reg) in G25 by (apply bv_eq; reflexivity). rewrite Q25 in G25.
    eapply (pm_opnd_pb w c0 K fx A M model c R1 (w_sp w + 684) _ PS X Htr BUD ltac:(cregs_tac G1 G2 G3 G4));
      [unfold O_V1; exact G10 | exact G11 | lia | unfold w_sp0, PM_FRAME; lia | exact Hgrow |].
    intros A1 R2 M1 model1 b1 cap1 X1 BUD1 KEPT AG.
    pose proof (oregs_kept w R1 R2 OR1 KEPT) as OR2.
    keptQ KEPT G2 Qsp2. keptQ KEPT G8 Qs02. keptQ KEPT G3 Qgp2. keptQ KEPT G4 Qtp2. keptQ KEPT G21 Q21b. keptQ KEPT G23 Q23b. keptQ KEPT G25 Q25b.
    clear G1 G2 G3 G4 G8 G10 G11 G21 G23 G25 KEPT OR1.
    eapply (PmBody1S1.loop_mem_frame w M M1) in LM; [| lia | lia | eapply agree_on_weaken; [exact AG | unfold zwin, w_sp0, PM_FRAME; intros; lia]].
    eapply (PmBody1S1.ictx_agree w M M1) in IC; [| lia | lia | eapply agree_on_weaken; [exact AG | unfold zwin, w_sp0, PM_FRAME; cbn; intros; lia]].
    eapply (ifr_agree w M M1) in IFR; [| lia | lia | eapply agree_on_weaken; [exact AG | unfold zwin, w_sp0, PM_FRAME; cbn; intros; lia]].
    eapply (PmBody1S1.cellw_frame M M1) in Cnw; [| lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold zwin, w_sp0, PM_FRAME; cbn; intros; lia]].
    clear AG X MS. pose proof (x_ms X1) as MS1.
    set (c1 := set_v1 c (b1, t3b (c_v1 c) + 1, cap1)) in *.

    pose proof (fld_cellw M1 _ 8 _ (x_widx X1) ltac:(cbn [c1 set_v1 c_widx]; lia)) as Cwi. unfold O_WIDX in Cwi. cbn [c1 set_v1 c_widx] in Cwi.
    pose proof (fld_cellw M1 _ 8 _ (x_n X1) ltac:(cbn; lia)) as Cn. unfold O_N in Cn.
    pose proof (flags_lo_byte M1 (w_p w) (c_reqconv c) ltac:(pose proof (x_flags X1) as F; unfold O_FLAGS in F; exact F) Sc4) as C92.
    pose proof (fld_cellw M1 _ 4 _ (x_endian X1) ltac:(cbn [c1 set_v1 c_endian]; lia)) as Ce. unfold O_ENDIAN in Ce. cbn [c1 set_v1 c_endian] in Ce.
    pose proof (fld_cellw M1 _ 8 _ (x_words X1) ltac:(destruct (Gw Hw); lia)) as Cws. unfold O_WORDS in Cws.
    destruct (Z.lt_ge_cases (w_n w) (c_widx c + nw)) as [Hov|Hfit].
    {
      pm_seed R2 w c1 [Z_to_bv 64 nw].
      seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R2. seedHK HK w A1 M1 model1 c1 E X1.
      apply (know_more E M1 [KWord (SA (EVar 33) 72) (N.to_nat 8) (EVar 38); KWord (SA (EVar 32) 686) (N.to_nat 2) (EVar 39); KWord (SA (EVar 33) 56) (N.to_nat 8) (EVar 35)]) in HK.
      2: { repeat apply Forall_cons; try apply Forall_nil.
           - eapply kword_var; [exact Cwi | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
           - eapply kword_var; [exact Cnw | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
           - eapply kword_var; [exact Cn | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity]. }
      xruns HR HK 100%nat (0x66e74 :: STOPS) (SCR [true] [] []) 50%N.
      { split_scs; try sc_auto1. all: cbn [sc_denot]; evs; cbn [c1 set_v1 c_widx c_endian]; rewrite ?ext_val_zx2, ?w_add by lia; rewrite ?br_ltu, ?br_eq, ?br_ne by lia; bool_lia. }
      postrun. name_run HRn R3.
      rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (9%bv) G9. rreg HRn (21%bv) G21. rreg HRn (23%bv) G23. rreg HRn (25%bv) G25.
      pose proof (syms_id_sound _ _ _ _ OSREGS HRn eq_refl) as GS.
      clear HRn HR HK. fixregs. pose proof (oregs_glue w R2 R3 OR2 GS G2 G3 G4 G8 (or_introl G9)) as OR3. clear GS G9.
      replace (Z_to_bv 5 (Z.of_N 21)) with (21%bv : reg) in G21 by (apply bv_eq; reflexivity). rewrite Q21b in G21.
      replace (Z_to_bv 5 (Z.of_N 23)) with (23%bv : reg) in G23 by (apply bv_eq; reflexivity). rewrite Q23b in G23.
      replace (Z_to_bv 5 (Z.of_N 25)) with (25%bv : reg) in G25 by (apply bv_eq; reflexivity). rewrite Q25b in G25.
      eapply (pm_X1 w c0 K fx A1 M1 model1 c1 R3 (i_io I) (i_op I) t PS FZ X1 Htr BUD1 OR3 G23 G25 G21); lia. }

    assert (TAIL : forall A2 M2 model2 R4 (v2 : Z * list Z * Z),
              PMX w A2 M2 model2 (set_v2 c1 v2) -> pm_bud (w_n w) (set_v2 c1 v2) -> Zlen (t3b v2) <= Zlen (t3b (c_v2 c)) + nw ->
              oregs w R4 -> getr R4 18%bv = Z_to_bv 64 (c_widx c + nw) -> loop_mem w M2 ->
              ictx w M2 (i_io I) (i_fw I) (i_iwc I) (i_op I) (i_d I) -> ifr w M2 ->
              srealizes SEGS (cfg fx R4 0x6712c M2 model2) K).
    { intros A2 M2 model2 R4 v2 X2 BUD2 Hl2 OR4 Q18 LM2 IC2 IFR2. pose proof (x_ms X2) as MS2.
      pose proof OR4 as OR'. destruct OR' as (Usp & Ugp & Utp & Us0 & Us1 & Us3 & Us4 & Us8).
      set (c2 := set_v2 c1 v2) in *.
      pm_seed R4 w c2 [Z_to_bv 64 (c_widx c + nw)].
      seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (18%bv, EVar 39)] R4. seedHK HK w A2 M2 model2 c2 E X2.
      xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
      postrun. name_run HRn R5a.
      rreg HRn (2%bv) F2. rreg HRn (3%bv) F3. rreg HRn (4%bv) F4. rreg HRn (8%bv) F8. rreg HRn (9%bv) F9. rreg HRn (26%bv) F26.
      pose proof (syms_id_sound _ _ _ _ OSREGS HRn eq_refl) as GS.
      clear HRn HR HK. fixregs. pose proof (oregs_glue w R4 R5a OR4 GS F2 F3 F4 F8 (or_introl F9)) as OR5a. clear GS F9.
      lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?m _) _) _ => set (M3 := m) in * end.

      try clear E. pm_seed R5a w c2 (@nil word).
      seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (26%bv, ELit 0)] R5a.
      assert (HK : know_ok SEGS E M3 []) by (apply Forall_nil).
      xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
      postrun. name_run HRn R5.
      rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (9%bv) G9.
      pose proof (syms_id_sound _ _ _ _ OSREGS HRn eq_refl) as GS.
      clear HRn HR HK. fixregs. pose proof (oregs_glue w R5a R5 OR5a GS G2 G3 G4 G8 (or_introl G9)) as OR5. clear GS G9 F2 F3 F4 F8 F26 OR5a.
      assert (ST3 : stores_in (zwin (w_p w + 72) (w_p w + 80)) M2 M3) by (unfold M3; stin).
      pose proof (x_scal X2) as (T1 & T2 & T3 & T4). cbn [c2 c1 set_v2 set_v1 c_widx c_icount c_endian c_reqconv] in T1, T2, T3, T4.
      assert (X3 : PMX w A2 M3 model2 (set_scal c2 (c_widx c + nw) (c_icount c2) (c_endian c2) (c_reqconv c2))).
      { eapply (pmx_stores SEGS Ly.L MI ST ly_img_low ly_rw_img ly_relro_img);
          [exact X2 | exact ST3 | intros a Ha; right; unfold scal_win, zwin, O_WIDX, O_FLAGS, w_sp0, PM_FRAME in *; lia
          | unfold M3, O_WIDX; rdback
          | eapply fld_keep; [exact ST3 | exact (x_icount X2) | unfold O_ICOUNT; lia | unfold O_ICOUNT; cbn; lia | unfold O_ICOUNT, zwin; cbn; intros; lia]
          | eapply fld_keep; [exact ST3 | exact (x_endian X2) | unfold O_ENDIAN; lia | unfold O_ENDIAN; cbn; lia | unfold O_ENDIAN, zwin; cbn; intros; lia]
          | eapply fld_keep; [exact ST3 | exact (x_flags X2) | unfold O_FLAGS; lia | unfold O_FLAGS; cbn; lia | unfold O_FLAGS, zwin; cbn; intros; lia]
          | lia | cbn [c2 c1 set_v2 set_v1 c_widx c_icount]; lia | cbn [c2 c1 set_v2 set_v1 c_endian]; lia | cbn [c2 c1 set_v2 set_v1 c_reqconv]; exact Sc4]. }
      eapply (PmBody1S1.loop_mem_frame w M2 M3) in LM2; [| lia | lia | eapply stores_in_agree; [exact ST3 | unfold zwin; intros; lia]].
      eapply (PmBody1S1.ictx_agree w M2 M3) in IC2; [| lia | lia | eapply stores_in_agree; [exact ST3 | unfold zwin; intros; lia]].
      eapply (ifr_agree w M2 M3) in IFR2; [| lia | lia | eapply stores_in_agree; [exact ST3 | unfold zwin; intros; lia]].
      eapply (HEADK A2 M3 model2 R5 b1 cap1 v2); [| exact Hl2 | lia].
      split; [exact X3|]. split; [exact Htr|]. split; [exact BUD2|]. split; [exact OR5|]. split; [exact LM2|]. split; [exact IC2|]. split; [exact IFR2|].
      unfold PmLoopS1.macct in *. cbn [c2 c1 set_v2 set_v1 set_scal c_icount c_endian c_v3 c_m1 c_m2 c_m3 t3a t3b t3c fst snd] in *.
      match goal with H : _ /\ _ /\ _ /\ PmLoopS1.m3ok _ |- _ => destruct H as (? & ? & ? & ?) end. repeat split; try assumption; try lia. }

    pose proof (Z.mod_pos_bound nw 1) as _.
    destruct (Z.eq_dec (c_reqconv c) 0) as [Hrc0|Hrc1].
    {
      pm_seed R2 w c1 [Z_to_bv 64 nw].
      seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R2. seedHK HK w A1 M1 model1 c1 E X1.
      apply (know_more E M1 [KWord (SA (EVar 33) 72) (N.to_nat 8) (EVar 38); KWord (SA (EVar 32) 686) (N.to_nat 2) (EVar 39); KWord (SA (EVar 33) 56) (N.to_nat 8) (EVar 35);
                              KWord (SA (EVar 33) 92) (N.to_nat 1) (ELit 0)]) in HK.
      2: { repeat apply Forall_cons; try apply Forall_nil.
           - eapply kword_var; [exact Cwi | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
           - eapply kword_var; [exact Cnw | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
           - eapply kword_var; [exact Cn | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
           - eapply kword_var; [rewrite Hrc0 in C92; exact C92 | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | cbn [edenot]; reflexivity]. }
      xruns HR HK 100%nat (0x6712c :: STOPS) (SCR [false] [] []) 50%N.
      { split_scs; try sc_auto1. all: cbn [sc_denot]; evs; cbn [c1 set_v1 c_widx c_endian]; rewrite ?ext_val_zx2, ?w_add by lia; rewrite ?br_ltu, ?br_eq, ?br_ne by lia; bool_lia. }
      postrun. name_run HRn R3.
      rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (9%bv) G9. rreg HRn (18%bv) G18.
      pose proof (syms_id_sound _ _ _ _ OSREGS HRn eq_refl) as GS.
      clear HRn HR HK. fixregs. pose proof (oregs_glue w R2 R3 OR2 GS G2 G3 G4 G8 (or_introl G9)) as OR3. clear GS G9.
      rewrite ext_val_zx2 in G18 by lia. rewrite SymExec.alu64_add_lit in G18. cbn [c1 set_v1 c_widx] in G18.
      eapply (TAIL A1 M1 model1 R3 (c_v2 c) X1 BUD1 ltac:(lia) OR3 G18 LM IC IFR). }
    assert (Hrc : c_reqconv c = 1) by lia.
    destruct (Z.eq_dec nw 0) as [Hnw0|Hnw1].
    {
      pm_seed R2 w c1 (@nil word).
      seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R2. seedHK HK w A1 M1 model1 c1 E X1.
      apply (know_more E M1 [KWord (SA (EVar 33) 72) (N.to_nat 8) (EVar 38); KWord (SA (EVar 32) 686) (N.to_nat 2) (ELit 0); KWord (SA (EVar 33) 56) (N.to_nat 8) (EVar 35);
                              KWord (SA (EVar 33) 92) (N.to_nat 1) (ELit 1)]) in HK.
      2: { repeat apply Forall_cons; try apply Forall_nil.
           - eapply kword_var; [exact Cwi | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
           - eapply kword_var; [rewrite Hnw0 in Cnw; exact Cnw | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | cbn [edenot]; reflexivity].
           - eapply kword_var; [exact Cn | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
           - eapply kword_var; [rewrite Hrc in C92; exact C92 | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | cbn [edenot]; reflexivity]. }
      xruns HR HK 100%nat (0x6712c :: STOPS) (SCR [false] [] []) 50%N.
      { split_scs; try sc_auto1. all: cbn [sc_denot]; evs; cbn [c1 set_v1 c_widx c_endian]; rewrite ?ext_val_zx2, ?w_add by lia; rewrite ?br_ltu, ?br_eq, ?br_ne by lia; bool_lia. }
      postrun. name_run HRn R3.
      rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (9%bv) G9. rreg HRn (18%bv) G18.
      pose proof (syms_id_sound _ _ _ _ OSREGS HRn eq_refl) as GS.
      clear HRn HR HK. fixregs. pose proof (oregs_glue w R2 R3 OR2 GS G2 G3 G4 G8 (or_introl G9)) as OR3. clear GS G9.
      rewrite ?SymExec.alu64_add_lit in G18. cbn [c1 set_v1 c_widx] in G18.
      eapply (TAIL A1 M1 model1 R3 (c_v2 c) X1 BUD1 ltac:(lia) OR3); [rewrite G18, Hnw0; f_equal; lia | exact LM | exact IC | exact IFR]. }

    destruct (Gw Hw) as (W1 & W2 & W3 & W4 & W5).
    pm_seed R2 w c1 [Z_to_bv 64 nw; Z_to_bv 64 (c_endian c)].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R2. seedHK HK w A1 M1 model1 c1 E X1.
    apply (know_more E M1 [KWord (SA (EVar 33) 72) (N.to_nat 8) (EVar 38); KWord (SA (EVar 32) 686) (N.to_nat 2) (EVar 39); KWord (SA (EVar 33) 56) (N.to_nat 8) (EVar 35);
                            KWord (SA (EVar 33) 92) (N.to_nat 1) (ELit 1); KWord (SA (EVar 33) 48) (N.to_nat 8) (EVar 34); KWord (SA (EVar 33) 88) (N.to_nat 4) (EVar 40);
                            KRange (EVar 39) 1 (2 ^ 16)]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil.
         - eapply kword_var; [exact Cwi | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
         - eapply kword_var; [exact Cnw | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
         - eapply kword_var; [exact Cn | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
         - eapply kword_var; [rewrite Hrc in C92; exact C92 | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | cbn [edenot]; reflexivity].
         - eapply kword_var; [exact Cws | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
         - eapply kword_var; [exact Ce | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
         - eapply krange_var; [evs; reflexivity | lia | lia]. }

    xruns HR HK 100%nat (0x67104 :: STOPS) (SCR [false; false] [] []) 50%N.
    { split_scs; try sc_auto1. all: cbn [sc_denot]; evs; cbn [c1 set_v1 c_widx c_endian]; rewrite ?ext_val_zx2, ?w_add by lia; rewrite ?br_ltu, ?br_eq, ?br_ne by lia; bool_lia. }
    postrun. name_run HRn R3.
    rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (9%bv) G9. rreg HRn (18%bv) G18. rreg HRn (21%bv) G21. rreg HRn (22%bv) G22. rreg HRn (23%bv) G23.
    pose proof (syms_id_sound _ _ _ _ OSREGS HRn eq_refl) as GS.
    clear HRn HR HK. fixregs. pose proof (oregs_glue w R2 R3 OR2 GS G2 G3 G4 G8 (or_introl G9)) as OR3. clear GS G9.
    rewrite ext_val_zx2 in G18, G23 by lia. rewrite SymExec.alu64_add_lit in G18. cbn [c1 set_v1 c_widx] in G18, G22.
    rewrite ext_val_sx4, sx32_small in G21 by lia. rewrite w_mul in G22, G23 by lia. rewrite w_add in G22 by lia.
    assert (Hk : Z.of_nat (Z.to_nat nw) = nw) by lia.
    eapply (pm_copy_loop (Z.to_nat nw) w c0 K fx I A1 M1 model1 c1 R3 (w_words w + 4 * c_widx c) (c_widx c + nw) PS FZ X1 Htr BUD1 OR3 LM IC IFR G18);
      [cbn [c1 set_v1 c_endian]; exact G21 | cbn [c1 set_v1 c_endian]; exact He2 | exact G22 | rewrite Hk; exact G23 | lia | exact Hw | lia | rewrite Hk; lia
      | replace (w_words w + 4 * c_widx c) with (w_words w + c_widx c * 4) by lia; rewrite Z_mod_plus_full; exact W2
      | rewrite Hk; cbn [c1 set_v1 c_v2]; lia |].
    intros A' M' model' R' b2 cap2 xs2 X' BUD' Hl OR' Q18' LM' IC' IFR'.
    eapply (TAIL A' M' model' R' (b2, xs2, cap2) X' BUD' _ OR' Q18' LM' IC' IFR').
  Unshelve. all: try (cbn [c1 set_v1 c_v2 t3b fst snd] in *; rewrite ?Hk in *; lia).
  Qed.
End PM.
