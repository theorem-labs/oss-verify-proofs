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
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep2U1.PmUpdU1. From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PmStep2U1 PmLoopU1 PmInstU1 PmStep3U1 PmODefsU1 PmStep4U1 PmZw.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PeLia.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Local Ltac lia ::= pe3_lia.
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
  #[local] Notation pm_ecw_pbs1 := (PmStep2U1.pm_ecw_pbs1 CL).
  #[local] Notation pm_ecw_pbs2 := (PmStep2U1.pm_ecw_pbs2 CL).
  #[local] Notation pmx_upd_foot := (PmStep2U1.pmx_upd_foot).
  #[local] Notation pm_v2_push_fast := (PmStep2U1.pm_v2_push_fast).
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
  #[local] Notation ipure := (PmODefsU1.ipure (G:=G) (idesc:=idesc)).
  #[local] Notation arm_stmt := (PmODefsU1.arm_stmt (MI:=MI) (ST:=ST) (G:=G) (idesc:=idesc)).
  #[local] Notation pm_opnd_pbs_stmt := (cu_opnd_pbs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).

  Lemma flags_hi_byte : forall M (p v : Z),
    fld SEGS M (p + 92) 2 v -> (v = 0 \/ v = 1) -> 0 <= p -> p + 94 < 2 ^ 64 -> cellw SEGS M (p + 93) 1 0.
  Proof using.
    intros M p v F Hv Hp Hhi. split; [cbn; lia|]. unfold CRep.fld in *.
    pose proof (rdn_skipn SEGS M 2 (Z_to_bv 64 (p + 92)) _ 1 F ltac:(lia)) as R.
    rewrite zbv_add_nat in R by lia. replace (p + 92 + Z.of_nat 1) with (p + 93) in R by lia.
    change (N.to_nat 1) with (2 - 1)%nat. rewrite R. destruct Hv as [-> | ->]; reflexivity.
  Qed.
  Lemma flags_lo_byte : forall M (p v : Z),
    fld SEGS M (p + 92) 2 v -> (v = 0 \/ v = 1) -> cellw SEGS M (p + 92) 1 v.
  Proof using.
    intros M p v F Hv. split; [cbn; lia|]. unfold CRep.fld in *.
    pose proof (rdn_firstn SEGS M 2 (Z_to_bv 64 (p + 92)) _ 1 F ltac:(lia)) as R.
    change (N.to_nat 1) with 1%nat. rewrite R. destruct Hv as [-> | ->]; reflexivity.
  Qed.

  Lemma pm_check_err : forall (w : pmw MI ST) c0 K (fx : FPState), PMS w c0 K -> frm_zero (@fp_csr fx) -> CHECKK w K fx.
  Proof using AC MI ST.
    intros w c0 K fx PS FZ A M model c R e X Htr BUD Qsp Qgp Qtp Qs0 Qs6 He.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & [Gc2 Gcal] & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof (x_scal X) as (_ & _ & _ & Sc4).
    pose proof (flags_hi_byte M (w_p w) (c_reqconv c) ltac:(pose proof (x_flags X) as F; unfold O_FLAGS in F; exact F) Sc4 ltac:(lia) ltac:(lia)) as C93.
    pose (E := Eseed R [Z_to_bv 64 (w_sp w); Z_to_bv 64 (w_p w); sxw e]).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (22%bv, EVar 34)] R.
    assert (HK : know_ok SEGS E M [KWord (SA (EVar 33) 93) (N.to_nat 1) (ELit 0)]).
    { repeat apply Forall_cons; try apply Forall_nil.
      eapply kword_var; [exact C93 | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | cbn [edenot]; reflexivity]. }
    xruns HR HK 100%nat STOPS (SCR [false; false] [] []) 50%N.
    { split_scs; try sc_auto1; cbn [sc_denot]; evs; match goal with |- ?G => idtac G end;
      first [ rewrite PmLoopU1.sextw_sxw by lia; change (Z_to_bv 64 0) with (sxw 0); rewrite br_eq_sxw by lia; bool_lia
            | rewrite <- (Z_to_bv_bv_unsigned 64 (getr R _)); rewrite br_ltu by (pose proof (u64_range (getr R (Z_to_bv 5 (Z.of_N 18)))); lia);
              apply Z.ltb_ge; pose proof (u64_range (getr R (Z_to_bv 5 (Z.of_N 18)))); lia ]. }
    postrun. name_run HRn R1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (22%bv) G22.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (PmLoopU1.pm_latch_err w c0 K fx A M model c R1 e PS X Htr BUD FZ G2 G3 G4 G22 He).
  Qed.

  Lemma pm_X1 : forall (w : pmw MI ST) c0 K (fx : FPState) A M model c R (io op t : Z),
    PMS w c0 K -> frm_zero (@fp_csr fx) -> PMX w A M model c -> c_tr c = [] -> pm_bud (w_n w) c -> oregs w R ->
    getr R 23%bv = Z_to_bv 64 io -> getr R 26%bv = Z_to_bv 64 op -> getr R 27%bv = Z_to_bv 64 t ->
    0 <= io < 2 ^ 63 -> 0 <= op < 2 ^ 16 -> 0 <= t < 2 ^ 32 ->
    srealizes SEGS (cfg fx R 0x677ac M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx A M model c R io op t PS FZ X Htr BUD OR Q23 Q26 Q27 Hio Hop Ht.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & [Gc2 Gcal] & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof OR as OR'. destruct OR' as (Qsp & Qgp & Qtp & Qs0 & Qs1 & Qs2 & Qs3 & Qs4 & Qs5 & Qs9).
    pose (E := Eseed R [Z_to_bv 64 (w_sp w); Z_to_bv 64 (w_p w); Z_to_bv 64 io; Z_to_bv 64 op; Z_to_bv 64 t]).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (23%bv, EVar 34); (26%bv, EVar 35); (27%bv, EVar 36)] R.
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
    postrun. name_run HRn R2. rreg HRn (2%bv) T2. rreg HRn (3%bv) T3. rreg HRn (4%bv) T4. rreg HRn (8%bv) T8. rreg HRn (22%bv) T22.
    clear HRn HR HK. fixregs. rewrite Qgp' in T3. rewrite Qtp' in T4.
    eapply (pm_check_err w c0 K fx PS FZ A' M' model' c R2 (2 ^ 32 - 4) X' Htr BUD T2 T3 T4 T8); [| lia].
    rewrite T22. unfold sxw. apply bv_eq. reflexivity.
  Qed.

  #[local] Notation pmx_updS := (pmx_upd SEGS Ly.L MI ST ly_img_low ly_rw_img ly_relro_img ly_errno_img ly_rw_not_relro ly_errno_rw).
  #[local] Notation live_splitS := (live_split SEGS Ly.L MI ST).
  #[local] Notation live_joinS := (live_join SEGS Ly.L MI ST).
  #[local] Notation vec_xferS := (vec_xfer SEGS Ly.L MI).

  Lemma pm_v1_push_fast : forall (w : pmw MI ST) A M M1 model c (b n cap : Z),
    PMX w A M model c -> c_v1 c = (b, n, cap) -> n < cap ->
    let e := b + OPND_SZ * n in
    stores_in (zwin e (e + OPND_SZ)) M M1 ->
    let M2 := wbytes M1 (Z_to_bv 64 (w_p w + 224)) (word_to_le_bytes 8 (Z_to_bv 64 (e + OPND_SZ))) in
    PMX w A M2 model (set_v1 c (b, n + 1, cap)).
  Proof using AC MI ST.
    intros w A M M1 model c b n cap X Ev1 Hroom. cbn zeta. intros ST1.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ai X) as AI.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & [Gc2 Gcal] & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof (x_v1 X) as V. rewrite Ev1 in V. cbn [t3a t3b t3c fst snd] in V.
    pose proof V as V0. destruct V0 as (V1 & V2 & V3 & V4 & Hblk & F0 & F1 & F2). unfold O_V1, OPND_SZ in *.
    destruct Hblk as [[-> ->] | (Hb0 & Hbal & Hc0 & Hbc & HIn & Hdj)]; [lia|].
    destruct (ai_live_block MI A M model b (20 * cap) AI HIn) as (_ & _ & _ & Hbce & Hall).
    set (e := b + 20 * n) in *. set (M2 := wbytes M1 _ _).
    assert (SI : stores_in (fun a => zwin e (e + 20) a \/ zwin (w_p w + 224) (w_p w + 232) a) M M2).
    { unfold M2. eapply stores_in_wbytes_more;
        [ eapply stores_in_weaken; [exact ST1 | intros a Ha; left; exact Ha]
        | lia | w2blen; cbn; lia | intros a' Ha'; rewrite length_N_to_le_bytes in Ha'; cbn in Ha'; unfold zwin; lia ]. }
    eapply (pmx_upd_foot CV1 w A M M2 model c _ _ X SI);
      [ | intros j Hj; destruct j; cbn; first [reflexivity | exfalso; exact (Hj eq_refl)]
      | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | cbn; rewrite Ev1; reflexivity |].
    - intros a [Ha|Ha]; unfold cfoot; cbn [chdr fst snd cblocks]; rewrite ?Ev1; cbn [t3a t3c fst snd]; unfold vec_opnd_blocks.
      + right. exists (b, OPND_SZ * cap). destruct (Z.eqb_spec b 0); [lia|]. split; [left; reflexivity | cbn; unfold zwin, OPND_SZ in *; lia].
      + left. unfold O_V1, zwin in *. lia.
    - cbn [crep set_v1 c_v1 t3a t3b t3c fst snd]. unfold O_V1, CRep.vec_opnd, OPND_SZ.
      split; [exact V1|]. split; [exact V2|]. split; [eapply stores_in_mdef; [exact SI | exact V3]|]. split; [lia|].
      split; [right; repeat split; try assumption; lia|].
      split; [eapply fld_keep; [exact SI | exact F0 | lia | cbn; lia | unfold zwin; cbn; intros; lia]|].
      split; [replace (w_p w + 216 + 8) with (w_p w + 224) by lia; replace (b + 20 * (n + 1)) with (e + 20) by (unfold e; lia); unfold M2; rdback|].
      eapply fld_keep; [exact SI | exact F2 | lia | cbn; lia | unfold zwin; cbn; intros; lia].
  Qed.

  Lemma pm_opnd_pbs : forall (w : pmw MI ST) c0 K (fx : FPState) A M model c R (src ret : Z),
    PMS w c0 K -> PMX w A M model c -> c_tr c = [] -> pm_bud (w_n w) c ->
    cregs w R ret -> getr R 10%bv = Z_to_bv 64 (w_p w + O_V1) -> getr R 11%bv = Z_to_bv 64 src ->
    w_sp w <= src -> src + 20 <= w_sp0 w - 104 -> src mod 4 = 0 ->
    t3b (c_v1 c) = t3c (c_v1 c) -> 40 * t3c (c_v1 c) + 20 <= 2 ^ 23 ->
    (forall A' R' M' model' (b' : Z),
        PMX w A' M' model' (set_v1 c (b', t3b (c_v1 c) + 1, vgrow (t3c (c_v1 c)))) ->
        pm_bud (w_n w) (set_v1 c (b', t3b (c_v1 c) + 1, vgrow (t3c (c_v1 c)))) ->
        kept R R' -> getr R' 10%bv = Z_to_bv 64 (b' + OPND_SZ * (t3b (c_v1 c) + 1)) ->
        CRep.agree_on (fun a => w_sp w <= a < w_sp0 w) M M' ->
        srealizes SEGS (cfg fx R' ret M' model') K) ->
    srealizes SEGS (cfg fx R (vc_entry (ku_opnd_pbs ccU1)) M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx A M model c R src ret PS X Htr BUD CR Ha0 Ha1 Hs1 Hs2 Hal Hfull Hgrow CONT.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ai X) as AI.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & [Gc2 Gcal] & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof (cu_mstack _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL) as HMS.
    pose proof (x_caps X) as (_ & _ & HNMAX). unfold LIB_NMAX in HNMAX.
    pose proof BUD as BUD'. destruct BUD' as (_ & _ & _ & _ & Bv1 & _).
    destruct (c_v1 c) as [[b n] cap] eqn:Ev1. cbn [t3a t3b t3c fst snd] in *. subst n.
    pose proof (x_v1 X) as V. rewrite Ev1 in V. cbn [t3a t3b t3c fst snd] in V.
    pose proof V as V0. destruct V0 as (_ & _ & _ & Hlen & Hblk & _).
    eapply ((cu_opnd_pbs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL) fx A (w_s w) R M model (w_sp w) ret (w_p w + O_V1) b cap src K).
    - eapply pmx_cregs_callB; [exact X | exact CR | cbn [vc_stack ku_opnd_pbs ccU1]; unfold NEW_STACK, PM_FRAME; lia].
    - exact Ha0. - exact Ha1. - exact V.
    - split; [left; unfold O_V1; lia | intros a Ha; cbn [vc_stack ku_opnd_pbs ccU1]; unfold zwin, O_V1, NEW_STACK in *; lia].
    - unfold O_V1. apply mod16_8; [exact Gp16 | reflexivity].
    - exact (x_roc X).
    - eapply mdef_sub; [exact (x_wdef X) | unfold w_sp0, PM_FRAME; lia | unfold w_sp0, PM_FRAME; lia].
    - split; [left; lia | intros a Ha; cbn [vc_stack ku_opnd_pbs ccU1]; unfold zwin, NEW_STACK in *; lia].
    - lia. - lia. - exact Hal.
    - intros a Ha. unfold zwin, O_V1, OPND_SZ in *. lia.
    - unfold vgrow, OPND_SZ in *. lia.
    - eapply pmx_ds_room; [exact PS | exact X | exact BUD | unfold vgrow, OPND_SZ, DS_MAXBLK in *; lia].
    - intros A' R' M' model' b' RB V' Hend LA EF. destruct RB as [AI' MS' FS' FDS' SX' KEPT].
      pose proof V' as V1. destruct V1 as (_ & _ & _ & Hlen' & Hblk' & _).
      set (c' := set_v1 c (b', cap + 1, vgrow cap)).
      assert (X' : PMX w A' M' model' c').
      { eapply (pmx_updS w CV1 A M model c A' M' model' c' (vc_stack (ku_opnd_pbs ccU1) + NEW_STACK SEGS Ly.L MI) _ X AI' MS' FS' FDS' EF);
          [cbn [vc_stack ku_opnd_pbs ccU1]; unfold NEW_STACK, PM_FRAME; lia | | | intros j Hj; destruct j; cbn; first [reflexivity | exfalso; exact (Hj eq_refl)]
          | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | cbn; exact V' |].
        + intros a [Ha|[[Hb Ha]|Ha]].
          * left. left. unfold O_V1 in *. cbn. exact Ha.
          * left. right. exists (b, OPND_SZ * cap). cbn. rewrite Ev1. cbn. unfold vec_opnd_blocks. destruct (Z.eqb_spec b 0); [lia|]. split; [left; reflexivity | unfold zwin in Ha; cbn; lia].
          * right. left. right. exists (b', OPND_SZ * vgrow cap). cbn. unfold vec_opnd_blocks. destruct (Z.eqb_spec b' 0); [unfold zwin in Ha; lia|]. split; [left; reflexivity | unfold zwin in Ha; cbn; lia].
        + intros a [Ha|[[Hb Ha]|Ha]] Hz; exfalso; unfold zwin, O_V1, w_sp0, PM_FRAME in *; [lia | |].
          * destruct Hblk as [[-> _]|(_ & _ & _ & _ & Hl & _)]; [lia|]. destruct (ai_live_block MI A M model _ _ AI Hl) as (_ & _ & _ & Hc' & _). lia.
          * destruct Hblk' as [[-> E0]|(_ & _ & _ & _ & Hl & _)]; [unfold vgrow in E0; lia|]. destruct (ai_live_block MI A' M' model' _ _ AI' Hl) as (_ & _ & _ & Hc' & _). lia.
        + eapply (live_joinS w A' c c' CV1); [intros j Hj; destruct j; cbn; first [reflexivity | exfalso; exact (Hj eq_refl)] | reflexivity |].
          cbn [cblocks c' set_v1 c_v1 t3a t3c fst snd]. unfold vec_opnd_blocks.
          eapply (vec_xferS A A' M M' model model' b cap b' (vgrow cap) OPND_SZ); [exact AI | exact AI' | unfold OPND_SZ; lia | | | | ].
          * pose proof (live_splitS w A M model c CV1 X) as P. cbn [cblocks] in P. rewrite Ev1 in P. cbn [t3a t3c fst snd] in P. unfold vec_opnd_blocks in P. exact P.
          * intros Hb. destruct Hblk as [[? ?]|(_ & _ & Hc & _)]; lia.
          * right. split; [unfold vgrow; lia | exact LA].
          * intros ->. destruct Hblk' as [[_ E0]|(Hb0 & _)]; [unfold vgrow in E0; lia | lia]. }
      eapply CONT; [exact X' | | exact KEPT | rewrite Hend; reflexivity |].
      + destruct BUD as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9). unfold pm_bud. cbn [c' set_v1 c_m1 c_m2 c_m3 c_v1 c_v2 c_v3 c_tr t3a t3b t3c fst snd].
        rewrite Ev1 in *. cbn [t3a t3b t3c fst snd] in *.
        repeat (split; [assumption|]). split; [| split; [assumption | split; [assumption | split; assumption]]]. unfold vgrow, OPND_SZ in *; lia.
      + eapply (pmx_frame_keep SEGS Ly.L MI ST ly_img_low ly_rw_img ly_errno_img); [exact X | exact EF | cbn [vc_stack ku_opnd_pbs ccU1]; unfold NEW_STACK; lia |].
        intros a Ha. split; [exact Ha|]. unfold zwin, O_V1, w_sp0, PM_FRAME in *. intros [Hh|[[Hb Hh]|Hh]]; [lia | |].
        * destruct Hblk as [[-> _]|(_ & _ & _ & _ & Hl & _)]; [lia|]. destruct (ai_live_block MI A M model _ _ AI Hl) as (_ & _ & _ & Hc' & _). lia.
        * destruct Hblk' as [[-> E0]|(_ & _ & _ & _ & Hl & _)]; [unfold vgrow in E0; lia|]. destruct (ai_live_block MI A' M' model' _ _ AI' Hl) as (_ & _ & _ & Hc' & _). lia.
  Qed.

  Lemma pm_v1_end_store : forall (w : pmw MI ST) A M model c (b n cap : Z),
    PMX w A M model c -> c_v1 c = (b, n, cap) ->
    PMX w A (wbytes M (Z_to_bv 64 (w_p w + 224)) (word_to_le_bytes 8 (Z_to_bv 64 (b + OPND_SZ * n)))) model c.
  Proof using AC MI ST.
    intros w A M model c b n cap X Ev1. pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & [Gc2 Gcal] & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof (x_v1 X) as V. rewrite Ev1 in V. cbn [t3a t3b t3c fst snd] in V.
    destruct V as (V1 & V2 & V3 & V4 & V5 & F0 & F1 & F2). unfold O_V1, OPND_SZ in *.
    assert (Hbn : 0 <= b + 20 * n < 2 ^ 64).
    { destruct V5 as [[-> ->]|(Hb0 & _ & Hc0 & Hbc & _)]; lia. }
    assert (SI : stores_in (zwin (w_p w + 224) (w_p w + 232)) M (wbytes M (Z_to_bv 64 (w_p w + 224)) (word_to_le_bytes 8 (Z_to_bv 64 (b + 20 * n))))) by stin.
    eapply (pmx_upd_own CV1 w A M _ model c c _ X SI);
      [intros a Ha; cbn; unfold O_V1, zwin in *; lia | intros j Hj; destruct j; cbn; reflexivity
      | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity |].
    cbn [crep]. rewrite Ev1. cbn [t3a t3b t3c fst snd]. unfold O_V1, CRep.vec_opnd, OPND_SZ.
    split; [exact V1|]. split; [exact V2|]. split; [eapply stores_in_mdef; [exact SI | exact V3]|]. split; [lia|]. split; [exact V5|].
    split; [eapply fld_keep; [exact SI | exact F0 | lia | cbn; lia | unfold zwin; cbn; intros; lia]|].
    split; [replace (w_p w + 216 + 8) with (w_p w + 224) by lia; rdback|].
    eapply fld_keep; [exact SI | exact F2 | lia | cbn; lia | unfold zwin; cbn; intros; lia].
  Qed.

  Definition PREGS : list reg := [23; 24; 26; 27]%bv.

  Ltac oregs_seeded HRn Qgp Qtp :=
    let G2 := fresh in let G3 := fresh in let G4 := fresh in let G8 := fresh in let G9 := fresh in
    let G18 := fresh in let G19 := fresh in let G20 := fresh in let G21 := fresh in let G25 := fresh in
    rreg HRn 2%bv G2; rreg HRn 3%bv G3; rreg HRn 4%bv G4; rreg HRn 8%bv G8; rreg HRn 9%bv G9;
    rreg HRn 18%bv G18; rreg HRn 19%bv G19; rreg HRn 20%bv G20; rreg HRn 21%bv G21; rreg HRn 25%bv G25;
    unfold oregs, loop_regs; rewrite G2, G3, G4, G8, G9, G18, G19, G20, G21, G25; fixregs; rewrite ?Qgp, ?Qtp;
    rewrite ?SymExec.alu64_add_lit; repeat split; reflexivity.

  Lemma pm_push : forall (w : pmw MI ST) c0 K (fx : FPState) A M model c R,
    PMS w c0 K -> PMX w A M model c -> c_tr c = [] -> pm_bud (w_n w) c -> oregs w R -> loop_mem w M ->
    (t3b (c_v1 c) = t3c (c_v1 c) -> 40 * t3c (c_v1 c) + 20 <= 2 ^ 23) ->
    (forall A' M' model' R' (b1 cap1 : Z),
        PMX w A' M' model' (set_v1 c (b1, t3b (c_v1 c) + 1, cap1)) -> pm_bud (w_n w) (set_v1 c (b1, t3b (c_v1 c) + 1, cap1)) ->
        oregs w R' -> (forall r, In r PREGS -> getr R' r = getr R r) ->
        CRep.agree_on (fun a => w_sp w <= a < w_sp0 w) M M' ->
        srealizes SEGS (cfg fx R' 0x67fec M' model') K) ->
    srealizes SEGS (cfg fx R 0x67f60 M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx A M model c R PS X Htr BUD OR LM Hgrow CONT.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS. pose proof (x_ai X) as AI.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & [Gc2 Gcal] & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof OR as OR'. destruct OR' as (Qsp & Qgp & Qtp & Qs0 & Qs1 & Qs2 & Qs3 & Qs4 & Qs5 & Qs9).
    pose proof BUD as BUD'. destruct BUD' as (_ & _ & _ & _ & Bv1 & _).
    destruct (c_v1 c) as [[b n] cap] eqn:Ev1. cbn [t3a t3b t3c fst snd] in *.
    pose proof (x_v1 X) as V. rewrite Ev1 in V. cbn [t3a t3b t3c fst snd] in V.
    pose proof V as V0. destruct V0 as (_ & _ & _ & Hlen & Hblk & F0 & F1 & F2). unfold O_V1, OPND_SZ in F0, F1, F2, Hblk.
    assert (WD : forall t k, w_sp w <= t -> t + k <= w_sp w + 864 -> mdef M t k).
    { intros t k Ht Hk i Hi. pose proof (x_wdef X (t + i - (w_sp w + 864 - w_STK w)) ltac:(unfold w_sp0, PM_FRAME; lia)) as D.
      unfold w_sp0, PM_FRAME in D. replace (w_sp w + 864 - w_STK w + (t + i - (w_sp w + 864 - w_STK w))) with (t + i) in D by lia. exact D. }
    destruct (mdef_cell4 M (w_sp w + 716) (WD (w_sp w + 716) 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)) as [v716 C716].
    destruct (mdef_cell4 M (w_sp w + 720) (WD (w_sp w + 720) 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)) as [v720 C720].
    destruct (mdef_cell4 M (w_sp w + 724) (WD (w_sp w + 724) 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)) as [v724 C724].
    destruct (mdef_cell4 M (w_sp w + 728) (WD (w_sp w + 728) 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)) as [v728 C728].
    destruct (mdef_cell4 M (w_sp w + 732) (WD (w_sp w + 732) 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)) as [v732 C732].
    pose proof (proj1 C716) as R716. pose proof (proj1 C720) as R720. pose proof (proj1 C724) as R724. pose proof (proj1 C728) as R728. pose proof (proj1 C732) as R732. cbn in R716, R720, R724, R728, R732.
    assert (Hbn : 0 <= n <= cap) by lia.
    pose proof (fld_cellw M _ 8 _ F1 ltac:(destruct Hblk as [[-> ->]|(Hb0 & _ & _ & Hbc & _)]; lia)) as Cend.
    pose proof (fld_cellw M _ 8 _ F2 ltac:(destruct Hblk as [[-> ->]|(Hb0 & _ & _ & Hbc & _)]; lia)) as Ccap.
    replace (w_p w + 216 + 8) with (w_p w + 224) in Cend by lia. replace (w_p w + 216 + 16) with (w_p w + 232) in Ccap by lia.
    destruct (Z.lt_ge_cases n cap) as [Hlt | Hge].
    -
      destruct Hblk as [[-> ->]|(Hb0 & Hbal & Hc0 & Hbc & HIn & Hdj)]; [lia|].
      destruct (ai_live_block MI A M model b (20 * cap) AI HIn) as (_ & _ & _ & Hbce & Hall).
      assert (Hspan : 0 <= 20 * n /\ 20 * n + 20 <= 20 * cap) by lia.
      assert (Hb16 : 16 <= b) by (pose proof (Z.div_mod b 16 ltac:(lia)); lia).
      set (e := b + 20 * n) in *.
      assert (He4 : e mod 4 = 0).
      { unfold e. replace (b + 20 * n) with (b + 5 * n * 4) by lia. rewrite Z.add_mod, Z_mod_mult, Z.add_0_r, Z.mod_mod by lia.
        replace b with (b / 16 * 4 * 4) by (pose proof (Z.div_mod b 16 ltac:(lia)); lia). apply Z_mod_mult. }
      assert (WRe : mdef M e 20) by (intros i Hi; exact (proj2 (proj2 (Hall (e + i) ltac:(unfold e; lia))))).
      pm_seed R w c [Z_to_bv 64 e; Z_to_bv 64 (b + 20 * cap); sxw v716; sxw v720; sxw v724; sxw v728; sxw v732].
      seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (9%bv, EAlu ALU_ADD (EVar 33) (ELit 88)); (18%bv, ELit 1); (19%bv, ELit (2 ^ 61)); (20%bv, ELit 20); (21%bv, EAlu ALU_ADD (EVar 33) (ELit 264)); (25%bv, ELit 5)] R.
      seedHK HK w A M model c E X.
      apply (know_more E M [KWord (SA (EVar 33) 224) (N.to_nat 8) (EVar 39); KWord (SA (EVar 33) 232) (N.to_nat 8) (EVar 40);
                            KWr (SA (EVar 39) 0) (ELit 20); KRange (EVar 39) 16 (2 ^ 47); KAlign (EVar 39) 4;
                            KDisj (SA (EVar 32) 0) (ELit 864) (SA (EVar 39) 0) (ELit 20)]) in HK.
      2: { repeat apply Forall_cons; try apply Forall_nil.
           - eapply kword_var; [exact Cend | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
           - eapply kword_var; [exact Ccap | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
           - eapply kwr_mdef; [evs; reflexivity | replace (e + 0) with e by lia; exact WRe | unfold e; lia | unfold e; lia | unfold e; lia | lia].
           - eapply krange_var; [evs; reflexivity | unfold e; lia | unfold e; lia].
           - eapply kalign_var; [evs; reflexivity | unfold e; lia | lia | exact He4].
           - eapply kdisj_vars; [evs; reflexivity | evs; reflexivity | lia | unfold e; lia | lia | lia | unfold e; lia]. }
      xruns HR HK 100%nat (0x67fec :: STOPS) (SCR [false] [EVar 45; EVar 44; EVar 43; EVar 42; EVar 41] []) 50%N.
      { split_scs; try sc_auto1; first [sc_rd_sx C732 | sc_rd_sx C728 | sc_rd_sx C724 | sc_rd_sx C720 | sc_rd_sx C716]. }
      postrun. name_run HRn R1. rewrite ?SymExec.alu64_add_lit.
      assert (OR1 : oregs w R1) by (oregs_seeded HRn Qgp Qtp).
      pose proof (syms_id_sound _ _ _ _ PREGS HRn eq_refl) as GP.
      clear HRn HR HK.
      lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ (wbytes ?m1 _ _) _) _) _ => set (M1 := m1) in * end.
      assert (ST1 : stores_in (zwin e (e + OPND_SZ)) M M1) by (unfold M1, OPND_SZ; stin).
      pose proof (pm_v1_push_fast w A M M1 model c b n cap X Ev1 Hlt ST1) as X1. cbn zeta in X1. unfold OPND_SZ in X1.
      replace (b + 20 * n) with e in X1 by reflexivity.
      eapply (CONT A _ model R1 b cap X1).
      + destruct BUD as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9). unfold pm_bud. cbn [set_v1 c_m1 c_m2 c_m3 c_v1 c_v2 c_v3 c_tr t3a t3b t3c fst snd].
        rewrite Ev1 in *. cbn [t3a t3b t3c fst snd] in *. repeat (split; [assumption|]). exact B9.
      + exact OR1.
      + exact GP.
      + assert (ST2 : stores_in (fun a => zwin e (e + 20) a \/ zwin (w_p w + 224) (w_p w + 232) a) M
                  (wbytes M1 (Z_to_bv 64 (w_p w + 224)) (word_to_le_bytes 8 (Z_to_bv 64 (e + 20))))).
        { eapply stores_in_wbytes_more; [eapply stores_in_weaken; [exact ST1 | unfold OPND_SZ; intros a Ha; left; exact Ha] | lia | w2blen; cbn; lia
            | intros a' Ha'; rewrite length_N_to_le_bytes in Ha'; cbn in Ha'; unfold zwin; lia]. }
        eapply stores_in_agree; [exact ST2|]. intros a Ha. unfold zwin, e in *. split; [lia | lia].
    -
      assert (Hfull : n = cap) by lia. subst n.
      pm_seed R w c [Z_to_bv 64 (b + 20 * cap); Z_to_bv 64 (b + 20 * cap)].
      seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (9%bv, EAlu ALU_ADD (EVar 33) (ELit 88)); (18%bv, ELit 1); (19%bv, ELit (2 ^ 61)); (20%bv, ELit 20); (21%bv, EAlu ALU_ADD (EVar 33) (ELit 264)); (25%bv, ELit 5)] R.
      seedHK HK w A M model c E X.
      apply (know_more E M [KWord (SA (EVar 33) 224) (N.to_nat 8) (EVar 39); KWord (SA (EVar 33) 232) (N.to_nat 8) (EVar 40);
                            KWord (SA (EVar 32) 104) (N.to_nat 8) (EAlu ALU_ADD (EVar 33) (ELit 216))]) in HK.
      2: { repeat apply Forall_cons; try apply Forall_nil.
           - eapply kword_var; [exact Cend | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
           - eapply kword_var; [exact Ccap | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
           - eapply kword_var; [eapply (loop_mem_cell w _ 104 (w_p w + 216) LM); [(first [ solve [cbn [In]; repeat (first [left; reflexivity | right])] | cbn; repeat (first [left; reflexivity | right]) ]) | lia] | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | cbn [edenot]; evs; rewrite w_add by lia; reflexivity]. }
      xruns HR HK 100%nat (0x67fec :: STOPS) (SCR [true] [] []) 50%N.
      { split_scs; try sc_auto1. }
      postrun. name_run HRn R1.
      rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11.
      assert (OR1 : oregs w R1) by (oregs_seeded HRn Qgp Qtp).
      pose proof (syms_id_sound _ _ _ _ PREGS HRn eq_refl) as GP.
      clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
      rewrite w_add in G10, G11 by lia.
      eapply (pm_opnd_pbs w c0 K fx A M model c R1 (w_sp w + 716) _ PS X Htr BUD ltac:(cregs_tac G1 G2 G3 G4));
        [unfold O_V1; exact G10 | exact G11 | lia | unfold w_sp0, PM_FRAME; lia | apply mod16_4; [exact Gsp16 | reflexivity] | rewrite Ev1; reflexivity | rewrite Ev1; cbn [t3c snd]; exact (Hgrow eq_refl) |].
      rewrite Ev1. cbn [t3a t3b t3c fst snd].
      intros A2 R2 M2 model2 b2 X2 BUD2 KEPT Hend AG.
      pose proof (oregs_kept w R1 R2 OR1 KEPT) as OR2. pose proof (x_ms X2) as MS2.
      keptQ KEPT G2 Qsp2. keptQ KEPT G8 Qs02.
      assert (GP2 : forall r, In r PREGS -> getr R2 r = getr R r).
      { intros r Hr. rewrite (KEPT r) by (revert Hr; clear; unfold PREGS; cbn; intuition (subst; (first [solve [clear; cbv; tauto] | cbv; tauto]))). exact (GP r Hr). }

      pose proof OR2 as OR2'. destruct OR2' as (Psp & Pgp & Ptp & Ps0 & Ps1 & Ps2 & Ps3 & Ps4 & Ps5 & Ps9).
      pose proof (x_v1 X2) as V2'. cbn [set_v1 c_v1 t3a t3b t3c fst snd] in V2'.
      destruct V2' as (_ & _ & _ & _ & Hblk2 & _). destruct Hblk2 as [[-> E0]|(Hb2 & Hbal2 & _ & Hbc2 & HIn2 & _)]; [unfold vgrow in E0; lia|].
      destruct (ai_live_block MI A2 M2 model2 _ _ (x_ai X2) HIn2) as (_ & _ & _ & Hbce2 & _). unfold OPND_SZ in Hbc2, Hbce2, Hend.
      assert (Hb216 : 16 <= b2) by (pose proof (Z.div_mod b2 16 ltac:(lia)); lia).
      assert (He2al : (b2 + 20 * (cap + 1)) mod 4 = 0).
      { replace (b2 + 20 * (cap + 1)) with (b2 + 5 * (cap + 1) * 4) by lia. rewrite Z.add_mod, Z_mod_mult, Z.add_0_r, Z.mod_mod by lia.
        replace b2 with (b2 / 16 * 4 * 4) by (pose proof (Z.div_mod b2 16 ltac:(lia)); lia). apply Z_mod_mult. }
      try clear E. pm_seed R2 w c [Z_to_bv 64 (b2 + 20 * (cap + 1))].
      seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (10%bv, EVar 39); (9%bv, EAlu ALU_ADD (EVar 33) (ELit 88)); (18%bv, ELit 1); (19%bv, ELit (2 ^ 61)); (20%bv, ELit 20); (21%bv, EAlu ALU_ADD (EVar 33) (ELit 264)); (25%bv, ELit 5)] R2.
      seedHK HK w A2 M2 model2 (set_v1 c (b2, cap + 1, vgrow cap)) E X2.
      apply (know_more E M2 [KRange (EVar 39) 36 (2 ^ 47); KAlign (EVar 39) 4]) in HK.
      2: { repeat apply Forall_cons; try apply Forall_nil.
           - eapply krange_var; [evs; reflexivity | unfold vgrow in *; lia | unfold vgrow in *; lia].
           - eapply kalign_var; [evs; reflexivity | unfold vgrow in *; lia | lia | exact He2al]. }
      xruns HR HK 100%nat (0x67fec :: STOPS) (SCR [] [] []) 50%N.
      { split_scs; try sc_auto1. }
      postrun. name_run HRn R3.
      assert (OR3 : oregs w R3) by (oregs_seeded HRn Pgp Ptp).
      pose proof (syms_id_sound _ _ _ _ PREGS HRn eq_refl) as GP3. clear HRn HR HK.
      pose proof (pm_v1_end_store w A2 M2 model2 _ b2 (cap + 1) (vgrow cap) X2 eq_refl) as X3. unfold OPND_SZ in X3.
      eapply (CONT A2 _ model2 R3 b2 (vgrow cap) X3 BUD2 OR3).
      + intros r Hr. rewrite (GP3 r Hr). exact (GP2 r Hr).
      + intros a Ha. pose proof (AG a Ha) as E0. unfold zwin in Ha.
        rewrite wbytes_outside; [exact E0 | w2blen; rewrite u64_of_Z by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
        w2blen. rewrite !u64_of_Z by lia. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
  Qed.

End PM.
