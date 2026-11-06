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
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts HStmtsU1 HCommonU1 HLib HConstsU1 HWord.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsGrammar PrsNeeds PrsInv PrsStmts PmBaseU1 PmHyps PmHypsU1 PmCoreU1 PmStepU1. Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep2U1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep2U1.PmUpdU1. From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PmStep2U1 PmLoopU1 PmInstU1 PmStep3U1 PmZw PmODefsU1 PmStep4U1 PmStep5U1 PmArm_RidLibU1.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PeLia.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Local Ltac lia ::= pe3_lia.
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
  #[local] Notation set_m3 := (PmArm_RidLibU1.set_m3).
  #[local] Notation pmx_upd_blk := (PmArm_RidLibU1.pmx_upd_blk (MI:=MI) (ST:=ST)).
  #[local] Notation umapx_set_val24 := (PmArm_RidLibU1.umapx_set_val24 (MI:=MI)).
  #[local] Notation pmx_updS := (pmx_upd SEGS Ly.L MI ST ly_img_low ly_rw_img ly_relro_img ly_errno_img ly_rw_not_relro ly_errno_rw).
  #[local] Notation live_splitS := (live_split SEGS Ly.L MI ST).
  #[local] Notation live_joinS := (live_join SEGS Ly.L MI ST).
  #[local] Notation hi_unownedS := (hi_unowned MI ly_img_low ly_rw_img).
  #[local] Notation HCL := (cu_classes _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
  #[local] Notation pmx_roomS := (pmx_room SEGS Ly.L MI ST (proj1 HCL) (proj1 (proj2 HCL)) (proj2 (proj2 HCL)) (cu_RB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL)).
  #[local] Notation pmx_room2S := (pmx_room2 SEGS Ly.L MI ST (proj1 HCL) (proj1 (proj2 HCL)) (proj2 (proj2 HCL)) (cu_RB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL)).
  Ltac fixregs3 := fixregs;
    try replace (Z_to_bv 5 (Z.of_N 1)) with (1%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 2)) with (2%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 10)) with (10%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 11)) with (11%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 12)) with (12%bv : reg) in * by (apply bv_eq; reflexivity);
    try replace (Z_to_bv 5 (Z.of_N 13)) with (13%bv : reg) in * by (apply bv_eq; reflexivity).

  Lemma pm_m3_setval : forall (w : pmw MI ST) A M model c l1 l2 (p k v v' : Z),
    PMX w A M model c -> t3c (c_m3 c) = l1 ++ (p, (k, v)) :: l2 -> 0 <= v' < 2 ^ 32 ->
    PMX w A (wbytes M (Z_to_bv 64 (p + 20)) (word_to_le_bytes 4 (Z_to_bv 64 v'))) model
        (set_m3 c (t3a (c_m3 c), t3b (c_m3 c), l1 ++ (p, (k, v')) :: l2)).
  Proof using AC MI ST.
    intros w A M model c l1 l2 p k v v' X E Hv'.
    pose proof (x_m3 X) as U. rewrite E in U.
    pose proof U as U0. destruct U0 as [_ _ _ _ _ _ _ _ _ _ _ _ _ _ Unode _].
    destruct (Unode p k v ltac:(apply in_app_iff; right; left; reflexivity)) as (Hlive & Hp0 & Hp47 & _).
    assert (SI : stores_in (zwin (p + 20) (p + 24)) M (wbytes M (Z_to_bv 64 (p + 20)) (word_to_le_bytes 4 (Z_to_bv 64 v')))) by stin.
    eapply (pmx_upd_blk CM3 w A M _ model c _ _ (p, 24) X SI).
    - cbn [cblocks]. unfold umap_blocks. apply in_app_iff. right. apply in_map_iff. exists (p, (k, v)). split; [reflexivity|]. rewrite E. apply in_app_iff. right. left. reflexivity.
    - intros a Ha. unfold zwin in Ha. cbn. lia.
    - intros j Hj. destruct j; cbn; first [reflexivity | exfalso; exact (Hj eq_refl)].
    - reflexivity. - reflexivity. - reflexivity. - reflexivity. - reflexivity.
    - cbn [cblocks set_m3 c_m3 t3a t3b t3c fst snd]. rewrite E. unfold umap_blocks. rewrite !map_app. reflexivity.
    - cbn [crep set_m3 c_m3 t3a t3b t3c fst snd]. exact (umapx_set_val24 A M _ _ _ l1 l2 p k v v' U Hv').
  Qed.

  Lemma pm_index_m3 : forall (w : pmw MI ST) c0 K (fx : FPState) A M model c R (key keyp ret : Z),
    PMS w c0 K -> frm_zero (@fp_csr fx) -> fconsts fx ->
    PMX w A M model c -> pm_bud (w_n w) c -> PmLoopU1.macct c ->
    3 * (Zlen (t3c (c_m3 c)) + 1) <= w_n w + 3 ->
    cregs w R ret ->
    getr R 10%bv = Z_to_bv 64 (w_p w + O_M3) -> getr R 11%bv = Z_to_bv 64 keyp ->
    cell4 SEGS M keyp key -> keyp mod 4 = 0 ->
    w_sp w <= keyp -> keyp + 4 <= w_sp0 w - 104 ->
    (forall (fx' : FPState) A' R' M' model' (p v : Z) (m1' : Z * Z * list (Z * (Z * Z))),
        frm_zero (@fp_csr fx') -> fconsts fx' -> PMX w A' M' model' (set_m3 c m1') -> pm_bud (w_n w) (set_m3 c m1') -> PmLoopU1.macct (set_m3 c m1') ->
        Zlen (t3c (c_m3 c)) <= Zlen (t3c m1') <= Zlen (t3c (c_m3 c)) + 1 ->
        kept R R' -> getr R' 10%bv = Z_to_bv 64 (p + 20) -> In (p, (key, v)) (t3c m1') -> 0 <= v < 2 ^ 32 ->
        CRep.agree_on (fun a => w_sp w <= a < w_sp0 w) M M' ->
        srealizes SEGS (cfg fx' R' ret M' model') K) ->
    srealizes SEGS (cfg fx R (ku_idx_ext ccU1) M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx A M model c R key keyp ret PS FZ FC X BUD MACC ACC1 CR Ha0 Ha1 Ckey Hk4 Hk1 Hk2 CONT.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ai X) as AI. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & [Gc2 Gcal] & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof (x_scal X) as (S1 & S2 & S3 & S4). pose proof (x_caps X) as (_ & _ & HNMAX).
    pose proof (cu_mstack _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL) as HMS.
    pose proof BUD as BUD'. destruct BUD' as ((Bn1 & Bn2 & Bn3) & B1 & B2 & B3 & _).
    destruct (c_m3 c) as [[bl bc] ents] eqn:Em3.
    pose proof (x_m3 X) as U. rewrite Em3 in U. cbn [t3a t3b t3c fst snd] in U. unfold O_M3 in U |- *.
    unfold PmLoopU1.macct in MACC. rewrite ?Em3 in *. cbn [t3a t3b t3c fst snd] in ACC1, MACC, B3, Bn3.
    destruct MACC as (MACC1 & MACC2 & MACC3 & M3OK).
    pose proof U as U0. destruct U0 as [_ _ _ _ Ubseq Uload _ _ _ _ _ _ _ _ _ _].
    unfold Zlen, Zlength in *.
    assert (Hz123 : 0 <= Z.of_nat (length ents) /\ 0 <= Z.of_nat (length (t3c (c_m2 c))) /\ 0 <= Z.of_nat (length (t3c (c_m1 c)))) by lia.
    assert (Hlast : bc <> BSEQ_LAST) by (unfold BSEQ_LAST; lia).
    assert (WD : forall t n, w_sp w + 864 - w_STK w <= t -> t + n <= w_sp w + 864 -> mdef M t n).
    { intros t n Ht Hn i Hi. pose proof (x_wdef X (t + i - (w_sp w + 864 - w_STK w)) ltac:(unfold w_sp0, PM_FRAME; lia)) as D.
      unfold w_sp0, PM_FRAME in D. replace (w_sp w + 864 - w_STK w + (t + i - (w_sp w + 864 - w_STK w))) with (t + i) in D by lia. exact D. }
    assert (HES : INDEX_STACK (NEW_STACK SEGS Ly.L MI) (MALLOC_STACK MI) <= 8336 /\ 128 <= INDEX_STACK (NEW_STACK SEGS Ly.L MI) (MALLOC_STACK MI)).
    { unfold INDEX_STACK, EMPLACE_STACK, NEW_STACK. lia. }
    destruct HES as [HES1 HES2].
    pose proof (proj1 Ckey) as Rkey. cbn in Rkey.
    eapply ((cu_index_ext _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL) fx A (w_s w) R M model (w_sp w) ret (w_p w + 176) bl bc keyp key ents K).
    - eapply pmx_cregs_callB; [exact X | exact CR | unfold PM_FRAME; lia].
    - exact FZ.
    - exact Ha0. - exact Ha1.
    - exact U.
    - split; [lia|]. split; [lia|]. intros i Hi. eapply hi_unownedS; [exact AI | lia].
    - eapply (pmx_above_sp_frame SEGS Ly.L MI ST ly_img_low ly_rw_img); [exact X | lia | unfold w_sp0, PM_FRAME; lia].
    - exact Ckey. - exact Hk4.
    - exact (x_roc X).
    - unfold Zlen, Zlength in *. lia.
    - unfold LIB_NMAX in *. lia.
    - exact Hlast.
    - eapply pmx_roomS; [exact X | exact BUD | exact (ps_budS _ _ _ PS) | exact (ps_budN _ _ _ PS) | exact (ps_budB _ _ _ PS) | lia].
    - intros Hfull. pose proof (PmStep5U1.bseq_next_le bc Ubseq Hlast) as [Hb1 H28].
      eapply pmx_room2S; [exact X | exact BUD | exact (ps_budS _ _ _ PS) | exact (ps_budN _ _ _ PS) | exact (ps_budB _ _ _ PS) | lia | lia | lia].
    - intros fx' A' R' M' model' p v bl' bc' ents' inserted rehashed RB FZ' FK' Hp U' Hin Hnoins Hins Hnorh Hrh LA EF.
      destruct RB as [AI' MS' FS' FDS' SX' KEPT].
      set (c' := set_m3 c (bl', bc', ents')).
      pose proof U' as U1. destruct U1 as [_ _ _ _ Ubseq' Uload' Ublive' _ Ubl0' _ _ _ _ _ Unode' _]. unfold Zlen, Zlength in Uload', Hrh |- *.
      assert (X' : PMX w A' M' model' c').
      { eapply (pmx_updS w CM3 A M model c A' M' model' c' (INDEX_STACK (NEW_STACK SEGS Ly.L MI) (MALLOC_STACK MI)) _ X AI' MS' FS' FDS' EF);
          [unfold PM_FRAME; lia | | | intros j Hj; destruct j; cbn; first [reflexivity | exfalso; exact (Hj eq_refl)]
          | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | cbn; unfold O_M3; exact U' |].
        + intros a [Ha|Ha].
          * left. destruct (umap_foot_cases 24 (w_p w + 176) bl bc ents a Ha) as [H|H];
              [left; unfold zwin, O_M3; cbn [chdr fst snd]; unfold O_M3; lia | right; cbn [cblocks]; rewrite Em3; cbn [t3a t3b t3c fst snd]; exact H].
          * right; left. destruct (umap_foot_cases 24 (w_p w + 176) bl' bc' ents' a Ha) as [H|H];
              [left; unfold zwin, O_M3; cbn [chdr fst snd]; unfold O_M3; lia | right; cbn [cblocks c' set_m3 c_m3 t3a t3b t3c fst snd]; exact H].
        + intros a [Ha|Ha] Hz; unfold zwin, w_sp0, PM_FRAME in Hz; exfalso.
          * destruct (umap_foot_cases 24 (w_p w + 176) bl bc ents a Ha) as [H|([q k] & Hb & Hab)]; [lia|]. cbn in Hab.
            destruct (ai_live_block MI A M model q k AI (umapx_blocks_live _ _ _ _ _ _ _ _ _ _ _ _ _ _ U Hb)) as (_ & _ & _ & Hc' & _). lia.
          * destruct (umap_foot_cases 24 (w_p w + 176) bl' bc' ents' a Ha) as [H|([q k] & Hb & Hab)]; [lia|]. cbn in Hab.
            destruct (ai_live_block MI A' M' model' q k AI' (umapx_blocks_live _ _ _ _ _ _ _ _ _ _ _ _ _ _ U' Hb)) as (_ & _ & _ & Hc' & _). lia.
        + eapply (live_joinS w A' c c' CM3); [intros j Hj; destruct j; cbn; first [reflexivity | exfalso; exact (Hj eq_refl)] | reflexivity |].
          cbn [cblocks c' set_m3 c_m3 t3a t3b t3c fst snd].
          pose proof (live_splitS w A M model c CM3 X) as P0. cbn [cblocks] in P0. rewrite Em3 in P0. cbn [t3a t3b t3c fst snd] in P0.
          destruct (PmStep5U1.lapply_app_inv _ _ _ _ LA) as (lv1 & LA1 & LA2).
          unfold umap_blocks in P0 |- *. rewrite <- app_assoc in P0 |- *.
          destruct (PmStep5U1.umap_xfer_ins 24 (live MI A) lv1 (if bc =? 0 then [] else [(bl, 8 * bc)]) _ p (key, 0) ents ents' inserted
                      (ai_live_nodup MI A M model AI) P0
                      ltac:(intros Hf; destruct (Hnoins Hf) as [-> _]; reflexivity)
                      ltac:(intros Ht; exact (proj2 (Hins Ht))) LA1) as [P1 N1].
          assert (Hrh' : rehashed = true -> bc' <> 0) by (intros Hr; destruct (Hrh Hr) as [_ ->]; pose proof (PmStep5U1.bseq_next_le bc Ubseq Hlast); lia).
          exact (PmStep5U1.umap_xfer_rh lv1 (live MI A') _ bl bc bl' bc' rehashed N1 (ai_live_nodup MI A' M' model' AI') ltac:(lia) P1 Hnorh Hrh' LA2). }
      assert (LEN : Z.of_nat (length ents') <= Z.of_nat (length ents) + 1 /\ Z.of_nat (length ents) <= Z.of_nat (length ents')).
      { destruct inserted.
        - pose proof (Permutation_length (proj2 (Hins eq_refl))) as E. rewrite E. cbn [length]. lia.
        - destruct (Hnoins eq_refl) as [-> _]. lia. }
      assert (BC' : 8 * bc' <= 16 * Z.of_nat (length ents') + 504).
      { destruct rehashed.
        - destruct (Hrh eq_refl) as [Hfull ->]. pose proof (PmStep5U1.bseq_next_le bc Ubseq Hlast). lia.
        - destruct (Hnorh eq_refl) as [-> ->]. lia. }
      destruct (Unode' p key v Hin) as (_ & _ & _ & _ & _ & _ & _ & NV & _). pose proof (proj1 NV) as Rv. cbn in Rv.
      eapply (CONT fx' A' R' M' model' p v (bl', bc', ents') FZ' (PmStep5U1.fconsts_fkept fx fx' FC FK') X'); [| | cbn [t3c snd]; unfold Zlen, Zlength in *; lia | exact KEPT | exact Hp | exact Hin | exact Rv |].
      + unfold pm_bud. cbn [c' set_m3 c_m1 c_m2 c_m3 c_v1 c_v2 c_v3 c_tr t3a t3b t3c fst snd]. unfold Zlen, Zlength in *.
        destruct BUD as ((C1a & C1b & C1c) & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9). rewrite Em3 in *. cbn [t3a t3b t3c fst snd] in *.
        pose proof (PmStep5U1.bseq_next_le bc Ubseq Hlast) as [_ H28].
        refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))); try assumption; try lia.
        all: cbn [length Z.of_nat]; try lia; try (intros b0 Hb0; exfalso; exact Hb0).
      + unfold PmLoopU1.macct. cbn [c' set_m3 c_m1 c_m2 c_m3 t3a t3b t3c fst snd]. unfold Zlen, Zlength in *. split; [lia|]. split; [lia|]. split; [lia |]. split; [| exact (proj2 M3OK)].
        { unfold PmLoopU1.m3ok in *. destruct inserted.
          - destruct (Hins eq_refl) as [-> HP]. eapply (Permutation_Forall (Permutation_sym HP)). constructor; [cbn; lia | exact (proj1 M3OK)].
          - destruct (Hnoins eq_refl) as [-> _]. exact (proj1 M3OK). }
      + eapply (pmx_frame_keep SEGS Ly.L MI ST ly_img_low ly_rw_img ly_errno_img); [exact X | exact EF | lia |].
        intros a Ha. split; [unfold w_sp0, PM_FRAME; exact Ha|]. unfold w_sp0, PM_FRAME in Ha. intros [Hf|Hf].
        * destruct (umap_foot_cases 24 (w_p w + 176) bl bc ents a Hf) as [H|([q k] & Hb & Hab)]; [lia|]. cbn in Hab.
          destruct (ai_live_block MI A M model q k AI (umapx_blocks_live _ _ _ _ _ _ _ _ _ _ _ _ _ _ U Hb)) as (_ & _ & _ & Hc' & _). lia.
        * destruct (umap_foot_cases 24 (w_p w + 176) bl' bc' ents' a Hf) as [H|([q k] & Hb & Hab)]; [lia|]. cbn in Hab.
          destruct (ai_live_block MI A' M' model' q k AI' (umapx_blocks_live _ _ _ _ _ _ _ _ _ _ _ _ _ _ U' Hb)) as (_ & _ & _ & Hc' & _). lia.
  Qed.
  Lemma mdef_words : forall M (k : nat) a, mdef M a (4 * Z.of_nat k) -> 0 <= a -> a + 4 * Z.of_nat k < 2 ^ 64 ->
    exists ws : list Z, Zlen ws = Z.of_nat k /\ forall i, 0 <= i < Z.of_nat k -> 0 <= Znth i ws < 2 ^ 32 /\ fld SEGS M (a + 4 * i) 4 (Znth i ws).
  Proof using.
    intros M k. induction k as [|k IH]; intros a HD Ha Hhi.
    - exists []. split; [reflexivity | intros i Hi; lia].
    - destruct (IH a ltac:(eapply mdef_sub; [exact HD | lia | lia]) Ha ltac:(lia)) as (ws & Hlen & Hws).
      destruct (mdef_cell4 M (a + 4 * Z.of_nat k) ltac:(eapply mdef_sub; [exact HD | lia | lia]) ltac:(lia) ltac:(lia)) as (v & [Rv Fv]).
      exists (ws ++ [v]). split; [rewrite Zlen_app, Zlen_cons, Zlen_nil; lia|].
      intros i Hi. destruct (Z.lt_ge_cases i (Z.of_nat k)) as [Hlt|Hge].
      + rewrite Znth_app_l by lia. apply Hws. lia.
      + assert (i = Zlen ws) as -> by lia. rewrite Znth_app_r1. replace (Zlen ws) with (Z.of_nat k) by lia. cbn in Rv. split; [lia | exact Fv].
  Qed.

  Lemma pmx_room_ms : forall (w : pmw MI ST) c0 K A M model c (n0 : Z),
    PMS w c0 K -> PMX w A M model c -> pm_bud (w_n w) c -> c_tr c = [] -> 0 < n0 <= 8 * w_n w + 48 ->
    (n0 < BIG MI -> count_class SEGS Ly.L MI A (size_class MI n0) + 2 <= caps MI A (size_class MI n0)
                    /\ count_class SEGS Ly.L MI A (size_class MI n0 + 1) + 2 <= caps MI A (size_class MI n0 + 1))
    /\ (BIG MI <= n0 -> big_bytes SEGS Ly.L MI A + 2 * round_big MI n0 <= bigcap MI A).
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K A M model c n0 PS X B Htr Hn0.
    pose proof (x_geo X) as GEO. destruct GEO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Gn & _).
    pose proof (x_caps X) as (Ccaps & Cbig & Cnmax). pose proof (x_live X) as PL.
    pose proof (ai_size_class_range MI) as SCR. pose proof (ai_big_pos MI) as BP.
    pose proof (ps_budS _ _ _ PS) as HS. pose proof (ps_budN _ _ _ PS) as HN. pose proof (ps_budB _ _ _ PS) as HB.
    pose proof (cu_RB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL) as RB.
    unfold count_class, big_bytes. rewrite Ccaps, Cbig. split.
    - intros Hsmall. pose proof (SCR n0 ltac:(lia)) as Hcls.
      rewrite !(count_class_f_perm _ _ _ _ _ PL), !count_class_f_app.
      pose proof (cnt_c_blocks SEGS Ly.L MI (proj1 HCL) (proj1 (proj2 HCL)) (proj2 (proj2 HCL)) (w_n w) c (size_class MI n0) B ltac:(lia)) as C1.
      pose proof (cnt_c_blocks SEGS Ly.L MI (proj1 HCL) (proj1 (proj2 HCL)) (proj2 (proj2 HCL)) (w_n w) c (size_class MI n0 + 1) B ltac:(lia)) as C2.
      unfold PM_SMALL_SLACK, CAP_SMALL, CAP_NODE in *.
      split.
      + destruct (Z.ltb_spec (size_class MI n0) 4).
        * rewrite lib_caps_node by lia. pose proof (HN (size_class MI n0) ltac:(lia)). unfold CAP_NODE in *. lia.
        * rewrite lib_caps_small by lia. pose proof (HS (size_class MI n0) ltac:(lia)). unfold CAP_SMALL in *. lia.
      + destruct (Z.ltb_spec (size_class MI n0 + 1) 4).
        * rewrite lib_caps_node by lia. pose proof (HN (size_class MI n0 + 1) ltac:(lia)). unfold CAP_NODE in *. lia.
        * rewrite lib_caps_small by lia. pose proof (HS (size_class MI n0 + 1) ltac:(lia)). unfold CAP_SMALL in *. lia.
    - intros Hbigreq. rewrite (big_bytes_f_perm _ _ _ _ PL), big_bytes_f_app.

      assert (BB0 : big_bytes_f (round_big MI) (BIG MI) (c_blocks c) <= 24 * w_n w + 2 ^ 28).
      { destruct B as ((Bn1 & Bn2 & Bn3) & B1 & B2 & B3 & Bv1 & Bv2 & Bv3 & Btr & Btrp).
        unfold c_blocks, vec_opnd_blocks. rewrite Htr. rewrite !(bigb_app SEGS Ly.L MI). cbn [big_bytes_f].
        pose proof (bigb_umap SEGS Ly.L MI (proj2 (proj2 HCL)) RB 24 (t3a (c_m1 c)) (t3b (c_m1 c)) (t3c (c_m1 c)) (or_introl eq_refl) ltac:(lia)).
        pose proof (bigb_umap SEGS Ly.L MI (proj2 (proj2 HCL)) RB 32 (t3a (c_m2 c)) (t3b (c_m2 c)) (t3c (c_m2 c)) (or_intror eq_refl) ltac:(lia)).
        pose proof (bigb_umap SEGS Ly.L MI (proj2 (proj2 HCL)) RB 24 (t3a (c_m3 c)) (t3b (c_m3 c)) (t3c (c_m3 c)) (or_introl eq_refl) ltac:(lia)).
        pose proof (bigb_opt_le SEGS Ly.L MI RB (t3a (c_v1 c) =? 0) (t3a (c_v1 c)) (OPND_SZ * t3c (c_v1 c)) ltac:(lia)).
        pose proof (bigb_opt_le SEGS Ly.L MI RB (t3a (c_v2 c) =? 0) (t3a (c_v2 c)) (4 * t3c (c_v2 c)) ltac:(lia)).
        pose proof (bigb_opt_le SEGS Ly.L MI RB (t3a (c_v3 c) =? 0) (t3a (c_v3 c)) (4 * t3c (c_v3 c)) ltac:(lia)).
        lia. }
      pose proof (RB n0 ltac:(lia)). unfold PM_BIG, LIB_BIGCAP in *. lia.
  Qed.

  #[local] Notation pmx_throughS := (pmx_through SEGS Ly.L MI ST ly_img_low ly_rw_img ly_relro_img ly_errno_img ly_rw_not_relro ly_errno_rw).

  Lemma pm_makestring : forall (w : pmw MI ST) c0 K (fx : FPState) A M model c R (ret : Z),
    PMS w c0 K -> PMX w A M model c -> c_tr c = [] -> pm_bud (w_n w) c -> w_words w <> 0 ->
    cregs w R ret ->
    getr R 10%bv = Z_to_bv 64 (w_sp w + 280) -> getr R 11%bv = Z_to_bv 64 (w_words w + 4 * c_widx c) ->
    getr R 12%bv = Z_to_bv 64 (w_n w - c_widx c) ->
    (forall A' R' M' model' (m' : sbuf) (ws : list Z),
        Zlen ws = w_n w - c_widx c ->
        PMX w A' M' model' (set_tr c (str_blocks m')) -> pm_bud (w_n w) (set_tr c (str_blocks m')) ->
        kept R R' -> CRep.str_rep MI A' M' (w_sp w + 280) m' (ms_chars ws) -> sbuf_asz_le m' (8 * (w_n w - c_widx c) + 2) ->
        CRep.agree_on (fun a => w_sp w <= a < w_sp0 w /\ ~ zwin (w_sp w + 280) (w_sp w + 304) a) M M' ->
        srealizes SEGS (cfg fx R' ret M' model') K) ->
    srealizes SEGS (cfg fx R (sc_makestring (ku_str ccU1)) M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx A M model c R ret PS X Htr BUD Hw CR Ha0 Ha1 Ha2 CONT.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ai X) as AI. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & [Gc2 Gcal] & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof (x_scal X) as (Sc1 & Sc2 & Sc3 & Sc4). pose proof (x_caps X) as (_ & _ & HNMAX). unfold LIB_NMAX in HNMAX.
    pose proof (cu_mstack _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL) as HMS.
    destruct (Gw Hw) as (W1 & W2 & W3 & W4 & W5).
    set (nw := w_n w - c_widx c) in *.
    destruct (mdef_words M (Z.to_nat nw) (w_words w + 4 * c_widx c) ltac:(rewrite Z2Nat.id by lia; eapply mdef_sub; [exact (x_wbuf X Hw) | lia | lia]) ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia)) as (ws & Hlen & WS).
    rewrite Z2Nat.id in Hlen, WS by lia.
    assert (WD : forall t n, w_sp w + 864 - w_STK w <= t -> t + n <= w_sp w + 864 -> mdef M t n).
    { intros t n Ht Hn i Hi. pose proof (x_wdef X (t + i - (w_sp w + 864 - w_STK w)) ltac:(unfold w_sp0, PM_FRAME; lia)) as D.
      unfold w_sp0, PM_FRAME in D. replace (w_sp w + 864 - w_STK w + (t + i - (w_sp w + 864 - w_STK w))) with (t + i) in D by lia. exact D. }
    eapply ((cu_makestring _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL) fx A (w_s w) R M model (w_sp w) ret (w_sp w + 280) (w_words w + 4 * c_widx c) nw ws K);
      cbn [sc_ms_stack sc_makestring ku_str ccU1].
    - eapply pmx_cregs_callB; [exact X | exact CR | unfold NEW_STACK, PM_FRAME; lia].
    - exact Ha0. - exact Ha1. - exact Ha2.
    - lia. - lia.
    - apply WD; lia.
    - split; [left; lia | intros a Ha; unfold zwin, NEW_STACK in *; lia].
    - lia. - exact Hlen. - lia. - lia.
    - rewrite (Z.mul_comm 4 (c_widx c)), Z_mod_plus_full. exact W2.
    - exact WS.
    - split; [| intros a Ha; unfold NEW_STACK in *; destruct (W5 a ltac:(unfold zwin in *; lia)) as [Hn _]; unfold zwin in *; lia].
      destruct W4 as [Hhi | (q & k & Hqk & Hq1 & Hq2)]; [left; lia | right].
      exists q, k. split; [| lia]. apply (Permutation_in (q, k) (Permutation_sym (x_live X))). apply in_app_iff. left. exact Hqk.
    - intros a Ha Hz. destruct (W5 a ltac:(unfold zwin in *; lia)) as [Hn _]. unfold zwin in *. lia.
    - lia.
    - intros n1 Hgs Hn1. destruct Hgs as (k & Hk & ->). assert (0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
      apply (pmx_room_ms w c0 K A M model c (48 * 2 ^ k) PS X BUD Htr). lia.
    - intros A' R' M' model' m' J RB STR LV DJ' JK ASZ EF. destruct RB as [AI' MS' FS' FDS' SX' KEPT].
      pose proof STR as STR'. destruct STR' as (_ & _ & HDstr & HlenS & Hm & _).
      assert (BLK : forall d asz, m' = SLong d asz -> In (d, asz) (live MI A') /\ ~ In d (map fst (live MI A)) /\ 0 < d /\ d + asz <= alloc_ceiling /\
                    (forall q k a, In (q, k) (live MI A) -> q <= a < q + k -> ~ (d <= a < d + asz))).
      { intros d asz ->. destruct Hm as (Hd0 & _ & _ & _ & _ & Hin & _). pose proof (DJ' d asz (or_introl eq_refl)) as Hnd.
        destruct (ai_live_block MI A' M' model' d asz AI' Hin) as (_ & _ & _ & Hdc & _).
        split; [exact Hin|]. split; [exact Hnd|]. split; [lia|]. split; [lia|].
        intros q k a Hqk Ha Hda. assert (Hqk' : In (q, k) (live MI A')) by (apply LV; left; exact Hqk).
        assert (Hne : q <> d) by (intros ->; apply Hnd; apply in_map_iff; exists (d, k); auto).
        destruct (ai_live_disjoint MI A' M' model' q k d asz AI' Hqk' Hin Hne); lia. }
      assert (X' : PMX w A' M' model' (set_tr c (str_blocks m'))).
      { eapply (pmx_throughS w A M model c A' M' model' (128 + NEW_STACK SEGS Ly.L MI) _ (str_blocks m'));
          [exact X | exact AI' | exact MS' | exact FS' | exact FDS' | exact EF | unfold NEW_STACK, PM_FRAME; lia | | | | |].
        + intros a [Ha|[Ha|Ha]] HP.
          * unfold fprot in HP. destruct HP as [HP|[HP|[HP|[[_ HP]|([bq bk] & Hb & Hab)]]]]; unfold zwin, w_sp0, PM_FRAME, PARSER_SIZE in *; try lia.
            -- destruct (W5 a ltac:(lia)) as [Hn _]. lia.
            -- cbn in Hab. destruct (ai_live_block MI A M model bq bk AI (cblk_live w (bq, bk) X Hb)) as (_ & _ & _ & Hbc & _). lia.
          * destruct m' as [|d asz]; [exact Ha|]. cbn [sbuf_fp] in Ha. destruct (BLK d asz eq_refl) as (Hin & Hnd & Hd0 & Hdc & Hdis).
            unfold fprot in HP. destruct HP as [HP|[HP|[HP|[[_ HP]|([bq bk] & Hb & Hab)]]]]; unfold zwin, w_sp0, PM_FRAME, PARSER_SIZE in *; try lia.
            -- destruct W4 as [Hhi | (q & k & Hqk & Hq1 & Hq2)]; [lia|].
               exact (Hdis q k a ltac:(apply (Permutation_in (q, k) (Permutation_sym (x_live X))); apply in_app_iff; left; exact Hqk) ltac:(lia) Ha).
            -- cbn in Hab. exact (Hdis bq bk a (cblk_live w (bq, bk) X Hb) Hab Ha).
          * exact (junk_not_fprot SEGS Ly.L MI ST w A M model c J a X JK Ha HP).
        + intros a [Ha|[Ha|Ha]].
          * right. unfold zwin, w_sp0, PM_FRAME in *. lia.
          * destruct m' as [|d asz]; [destruct Ha|]. cbn [sbuf_fp] in Ha. destruct (BLK d asz eq_refl) as (Hin & Hnd & Hd0 & Hdc & Hdis).
            left. right. destruct (ai_live_block MI A' M' model' d asz AI' Hin) as (_ & _ & _ & _ & Hpay). destruct (Hpay a ltac:(unfold zwin in Ha; lia)) as (_ & Himg & _).
            split; [unfold zwin in Ha; lia|]. split; [exact Himg|]. intros q k Hqk Hqa.
            exact (Hdis q k a ltac:(apply (Permutation_in (q, k) (Permutation_sym (x_live X))); apply in_app_iff; left; exact Hqk) Hqa ltac:(unfold zwin in Ha; lia)).
          * left. right. exact (junk_junkL SEGS Ly.L MI ST w A M model c J a X JK Ha).
        + intros a [Ha|[Ha|Ha]] Hz.
          * pose proof (HDstr (a - (w_sp w + 280)) ltac:(unfold zwin in Ha; lia)) as D.
            replace (w_sp w + 280 + (a - (w_sp w + 280))) with a in D by lia. exact D.
          * exfalso. destruct m' as [|d asz]; [destruct Ha|]. cbn [sbuf_fp] in Ha. destruct (BLK d asz eq_refl) as (Hin & Hnd & Hd0 & Hdc & Hdis).
            unfold zwin, w_sp0, PM_FRAME in *. lia.
          * exfalso. pose proof (proj1 (JK a Ha)). unfold zwin, w_sp0, PM_FRAME, NEW_STACK in *. lia.
        + intros [q k] Hb. apply (proj2 (LV q k)). left. exact (cblk_live w (q, k) X Hb).
        + assert (PERM' : Permutation (live MI A') (str_blocks m' ++ live MI A)).
          { apply live_equiv_perm.
            - exact (ai_live_nodup MI A' M' model' AI').
            - destruct m' as [|d asz]; cbn [str_blocks map fst app]; [exact (ai_live_nodup MI A M model AI)|].
              apply NoDup_cons_2; [| exact (ai_live_nodup MI A M model AI)].
              intros Hin. apply (proj1 (proj2 (BLK d asz eq_refl))). apply list_elem_of_In in Hin. exact Hin.
            - intros q k. rewrite (LV q k), in_app_iff. tauto. }
          rewrite PERM', (x_live X), c_blocks_split, Htr, app_nil_r.
          etransitivity; [apply Permutation_app_comm|]. rewrite app_assoc. reflexivity. }
      eapply (CONT A' R' M' model' m' ws Hlen X').
      * destruct BUD as (B0 & B1 & B2 & B3 & Bv1 & Bv2 & Bv3 & Btr & Btrp). destruct c as [cw ci ce cr cm1 cm2 cm3 cv1 cv2 cv3 ctr]; unfold pm_bud, set_tr in *; cbn [c_m1 c_m2 c_m3 c_v1 c_v2 c_v3 c_tr] in *.
        split; [exact B0|]. split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. split; [exact Bv1|]. split; [exact Bv2|]. split; [exact Bv3|].
        destruct m' as [|d asz]; cbn [str_blocks]; [split; [unfold Zlength; cbn; lia | intros b []]|].
        cbn [str_blocks]. split; [rewrite Zlength_cons, Zlength_nil; lia|]. intros b [<-|[]]. cbn [snd]. cbn [sbuf_asz_le] in ASZ.
        destruct Hm as (_ & _ & _ & _ & Hcap & _). unfold SSO_CAP in Hcap. lia.
      * exact KEPT.
      * exact STR.
      * exact ASZ.
      * eapply (pmx_frame_keep SEGS Ly.L MI ST ly_img_low ly_rw_img ly_errno_img); [exact X | exact EF | unfold NEW_STACK, PM_FRAME; lia |].
        intros a [Ha Hnz]. split; [exact Ha|]. intros [Hf|[Hf|Hf]].
        -- apply Hnz. unfold zwin in *. lia.
        -- destruct m' as [|d asz]; [destruct Hf|]. cbn [sbuf_fp] in Hf. destruct (BLK d asz eq_refl) as (Hin & Hnd & Hd0 & Hdc & Hdis).
           unfold zwin, w_sp0, PM_FRAME in *. lia.
        -- pose proof (proj1 (JK a Hf)). unfold zwin, w_sp0, PM_FRAME, NEW_STACK in *. lia.
  Qed.

  #[local] Notation pmx_throughD := (pmx_through SEGS Ly.L MI ST ly_img_low ly_rw_img ly_relro_img ly_errno_img ly_rw_not_relro ly_errno_rw).
  Lemma pm_del_tr : forall (w : pmw MI ST) c0 K (fx : FPState) A M model c R (ret d asz : Z),
    PMS w c0 K -> PMX w A M model c -> c_tr c = [(d, asz)] -> pm_bud (w_n w) c ->
    cregs w R ret -> getr R 10%bv = Z_to_bv 64 d ->
    (forall A' R' M' model',
        PMX w A' M' model' (set_tr c []) -> pm_bud (w_n w) (set_tr c []) -> kept R R' ->
        CRep.agree_on (fun a => w_sp w <= a < w_sp0 w) M M' ->
        srealizes SEGS (cfg fx R' ret M' model') K) ->
    srealizes SEGS (cfg fx R (ku_del1 ccU1) M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx A M model c R ret d asz PS X Htr BUD CR Ha0 CONT.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ai X) as AI. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & [Gc2 Gcal] & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof (cu_mstack _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL) as HMS.
    pose proof (x_live X) as PL. rewrite c_blocks_split, Htr in PL.
    assert (HIn : In (d, asz) (live MI A)).
    { apply (Permutation_in (d, asz) (Permutation_sym PL)). rewrite !in_app_iff. right; right; left; reflexivity. }
    destruct (ai_live_block MI A M model d asz AI HIn) as (Hasz0 & _ & Hd0 & Hdc & Hpay).
    pose proof (perm_nodup_fst _ _ PL (ai_live_nodup MI A M model AI)) as NDL.
    assert (Hne : forall q k, In (q, k) (w_L0 w ++ cblk c) -> q <> d).
    { intros q k Hqk. rewrite app_assoc in NDL.
      eapply (nodup_app_ne (w_L0 w ++ cblk c) [(d, asz)] q d NDL); [| left; reflexivity].
      apply in_map_iff. exists (q, k). split; [reflexivity | exact Hqk]. }
    assert (Hdis : forall q k a, In (q, k) (w_L0 w ++ cblk c) -> q <= a < q + k -> ~ (d <= a < d + asz)).
    { intros q k a Hqk Hqa Hda.
      assert (HqkA : In (q, k) (live MI A)) by (apply (Permutation_in (q, k) (Permutation_sym PL)); rewrite app_assoc, in_app_iff; left; exact Hqk).
      exact (live_payload_disjoint SEGS Ly.L MI A M model d asz q k a AI HIn HqkA ltac:(intros E; exact (Hne q k Hqk (eq_sym E))) Hda Hqa). }
    pose proof (pmx_cregs_callB w A M model c R ret (MALLOC_STACK MI) X CR ltac:(unfold PM_FRAME; lia)) as CB.
    destruct CB as [_ _ ROC _ _ CRG CCEIL CROOM CWIN _ _].
    eapply ((cu_del1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL) fx A R M model d asz (w_sp w) ret K).
    - exact AI. - exact MS. - exact ROC. - exact CRG. - exact Ha0.
    - right. exact HIn.
    - exact CCEIL. - exact CROOM.
    - intros a Ha. exact (proj1 (CWIN a Ha)).
    - intros A' R' M' model' AI' MS' FS' FDS' KEPT LDEL CAPS' BIG' OWN' FR' DEF'.
      assert (EF : eff MI A A' M M' (w_sp w - MALLOC_STACK MI, w_sp w) (fun a => d <= a < d + asz)).
      { eapply (eff_of_del MI A A' M M' _ (fun a => d <= a < d + asz) d asz); try eassumption.
        + intros a Ha. unfold W_of, zwin in *. cbn. lia.
        + intros a Ha. exact Ha.
        + intros a Ha. eapply (live_offimg Ly.L MI); [exact AI | exact HIn | exact Ha]. }
      assert (X' : PMX w A' M' model' (set_tr c [])).
      { eapply (pmx_throughD w A M model c A' M' model' (MALLOC_STACK MI) _ []);
          [exact X | exact AI' | exact MS' | exact FS' | exact FDS' | exact EF | unfold PM_FRAME; lia | | | | |].
        + intros a Ha HP. cbn beta in Ha. unfold fprot in HP.
          destruct HP as [HP|[HP|[HP|[[Hwz HP]|([bq bk] & Hb & Hab)]]]]; unfold zwin, w_sp0, PM_FRAME, PARSER_SIZE in *; try lia.
          * destruct (Gw Hwz) as (_ & _ & _ & W4 & _). destruct W4 as [Hhi | (q & k & Hqk & Hq1 & Hq2)]; [lia|].
            exact (Hdis q k a ltac:(apply in_app_iff; left; exact Hqk) ltac:(lia) Ha).
          * cbn in Hab. exact (Hdis bq bk a ltac:(apply in_app_iff; right; exact Hb) Hab Ha).
        + intros a Ha. cbn beta in Ha. left. right. split; [lia|]. split; [eapply (live_offimg Ly.L MI); [exact AI | exact HIn | exact Ha]|].
          intros q k Hqk Hqa. exact (Hdis q k a ltac:(apply in_app_iff; left; exact Hqk) Hqa Ha).
        + intros a Ha Hz. cbn beta in Ha. exfalso. unfold zwin, w_sp0, PM_FRAME in *. lia.
        + intros [q k] Hb. apply (proj2 (LDEL q k)). split; [exact (cblk_live w (q, k) X Hb) | exact (Hne q k ltac:(apply in_app_iff; right; exact Hb))].
        + rewrite app_nil_r. eapply (live_del_perm d asz (w_L0 w ++ cblk c) (live MI A) (live MI A')).
          * eapply Permutation_trans; [exact PL|]. rewrite app_assoc. apply Permutation_sym. apply Permutation_cons_append.
          * exact (ai_live_nodup MI A M model AI).
          * exact LDEL.
          * exact (ai_live_nodup MI A' M' model' AI'). }
      eapply (CONT A' R' M' model' X').
      + destruct BUD as (B0 & B1 & B2 & B3 & Bv1 & Bv2 & Bv3 & Btr & Btrp).
        destruct c as [cw ci ce cr cm1 cm2 cm3 cv1 cv2 cv3 ctr]; unfold pm_bud, set_tr in *; cbn [c_m1 c_m2 c_m3 c_v1 c_v2 c_v3 c_tr] in *.
        repeat (split; [assumption|]). split; [unfold Zlength; cbn; lia | intros b []].
      + exact KEPT.
      + eapply (pmx_frame_keep SEGS Ly.L MI ST ly_img_low ly_rw_img ly_errno_img); [exact X | exact EF | lia |].
        intros a Ha. split; [unfold w_sp0, PM_FRAME; exact Ha|]. intros Hf. unfold zwin, w_sp0, PM_FRAME in *. lia.
  Qed.

  Lemma take_nz_nz : forall cs, Forall (fun c => c <> 0) (fst (take_nz cs)).
  Proof using.
    induction cs as [|c cs IH]; [constructor|]. cbn [take_nz]. destruct (Z.eqb_spec c 0); [constructor|].
    destruct (take_nz cs) as [p f]. cbn [fst] in *. constructor; [exact n | exact IH].
  Qed.
  Lemma ms_chars_nz : forall ws, Forall (fun c => c <> 0) (ms_chars ws).
  Proof using.
    induction ws as [|x ws IH]; [constructor|]. cbn [ms_chars].
    pose proof (take_nz_nz (word_chars (x mod 2 ^ 32) 4)) as T. destruct (take_nz _) as [p f]. cbn [fst] in T.
    destruct f; [exact T | apply Forall_app; split; [exact T | exact IH]].
  Qed.
  Lemma Forall_Znth : forall (P : Z -> Prop) l i, Forall P l -> 0 <= i < Zlen l -> P (Znth i l).
  Proof using.
    intros P l i H Hi. apply (proj1 (Forall_nth _ _) H). unfold Zlen in Hi. lia.
  Qed.

  Lemma pm_import : forall (w : pmw MI ST) A M model c (fx : FPState) R (m : sbuf) (cs : list Z) (ret : Z) K,
    PMX w A M model c -> c_tr c = str_blocks m ->
    CRep.str_rep MI A M (w_sp w + 280) m cs -> Forall (fun ch => ch <> 0) cs ->
    getr R 10%bv = Z_to_bv 64 (str_data (w_sp w + 280) m) ->
    getr R 2%bv = Z_to_bv 64 (w_sp w) ->
    getr R 1%bv = Z_to_bv 64 ret -> ret_ok (Z_to_bv 64 ret) ->
    (forall R' M' (r : Z), kept R R' -> getr R' 10%bv = Z_to_bv 64 r -> 0 <= r < 2 ^ 31 ->
        PMX w A M' model c -> CRep.agree_on (fun a => w_sp w <= a < w_sp0 w \/ 0 <= a < alloc_ceiling) M M' ->
        srealizes SEGS (cfg fx R' ret M' model) K) ->
    srealizes SEGS (cfg fx R (tc_import_type_get tcU1) M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w A M model c fx R m cs ret K X Htr STR NZ Ha0 Hsp Hra Hret CONT.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS. pose proof (x_ai X) as AI.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & [Gc2 Gcal] & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof (x_scal X) as (S1 & S2 & S3 & S4).
    assert (WD : forall t n, w_sp w + 864 - w_STK w <= t -> t + n <= w_sp w + 864 -> mdef M t n).
    { intros t n Ht Hn i Hi. pose proof (x_wdef X (t + i - (w_sp w + 864 - w_STK w)) ltac:(unfold w_sp0, PM_FRAME; lia)) as D.
      unfold w_sp0, PM_FRAME in D. replace (w_sp w + 864 - w_STK w + (t + i - (w_sp w + 864 - w_STK w))) with (t + i) in D by lia. exact D. }
    pose proof STR as STR'. destruct STR' as (_ & _ & HDs & Hlen & Hm & HC & HZ).
    set (p := str_data (w_sp w + 280) m) in *. set (n := Zlen cs) in *.

    assert (PL : 0 < p /\ p + n + 1 <= 2 ^ 47 /\ mdef M p (n + 1) /\ placed MI A p (n + 1) /\ (p + n + 1 <= alloc_ceiling \/ w_sp w + 281 = p)).
    { subst p n. destruct m as [|d asz]; cbn [str_data str_cap] in *.
      - unfold SSO_CAP in Hlen. split; [lia|]. split; [lia|]. split; [apply WD; lia|]. split; [left; lia | right; lia].
      - destruct Hm as (Hd0 & _ & _ & _ & _ & HIn & _). destruct (ai_live_block MI A M model d asz AI HIn) as (_ & _ & _ & Hdc & Hpay).
        split; [lia|]. split; [lia|]. split; [intros i Hi; exact (proj2 (proj2 (Hpay (d + i) ltac:(lia))))|].
        split; [right; exists d, asz; split; [exact HIn | lia] | left; lia]. }
    destruct PL as (P0 & P47 & PD & PP & PW).
    destruct ((cu_import_type_get _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL) fx A R M model p n (w_sp w) (Z_to_bv 64 ret) AI (x_roc X) Ha0 Hsp
                P0 P47 ltac:(lia) PD
                ltac:(intros i Hi; exists (Znth i cs); pose proof (HC i Hi) as [Ri Fi]; pose proof (Forall_Znth _ cs i NZ Hi) as NZi; cbn beta in NZi; split; [lia | exact Fi])
                HZ PP
                ltac:(intros a Ha; cbn [tc_import_stack tcU1]; unfold zwin in *; lia)
                ltac:(unfold stack_room; cbn [tc_import_stack tcU1]; apply (mdef_store_ok SEGS M _ 64); [apply WD; lia | lia | lia | lia])
                ltac:(cbn [tc_import_stack tcU1]; lia) ltac:(lia) Gsp16 Hra Hret)
      as (R' & M' & r & MSx & KP & Hr & Rr & FE & DK). cbn [tc_import_stack tcU1] in FE.
    pose proof (stores_in_of_frame_eq _ M M' FE DK) as SI.
    eapply srz_msteps; [exact (ms_halt _ MS) | exact (ms_lazy _ MS) | exact MSx |].
    eapply (CONT R' M' r KP Hr Rr).
    - rewrite <- (set_scal_id c).
      eapply (pmx_stores SEGS Ly.L MI ST ly_img_low ly_rw_img ly_relro_img); [exact X | exact SI | | | | | | lia | lia | lia | exact S4].
      + intros a Ha; unfold zwin, scal_win, w_sp0, PM_FRAME in *; left; lia.
      + eapply fld_keep; [exact SI | exact (x_widx X) | unfold O_WIDX; lia | unfold O_WIDX; cbn; lia | unfold O_WIDX, zwin; cbn; intros; lia].
      + eapply fld_keep; [exact SI | exact (x_icount X) | unfold O_ICOUNT; lia | unfold O_ICOUNT; cbn; lia | unfold O_ICOUNT, zwin; cbn; intros; lia].
      + eapply fld_keep; [exact SI | exact (x_endian X) | unfold O_ENDIAN; lia | unfold O_ENDIAN; cbn; lia | unfold O_ENDIAN, zwin; cbn; intros; lia].
      + eapply fld_keep; [exact SI | exact (x_flags X) | unfold O_FLAGS; lia | unfold O_FLAGS; cbn; lia | unfold O_FLAGS, zwin; cbn; intros; lia].
    - eapply stores_in_agree; [exact SI|]. intros a Ha. unfold zwin in *. split; [lia | lia].
  Qed.

  Definition SREGS : list reg := [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

  Definition shdr (w : pmw MI ST) (M : mem) (m : sbuf) (len : Z) : Prop :=
    match m with
    | SShort => fld SEGS M (w_sp w + 280) 1 (2 * len) /\ 0 <= len <= SSO_CAP
    | SLong d asz => fld SEGS M (w_sp w + 280) 8 (asz + 1) /\ fld SEGS M (w_sp w + 288) 8 len /\ fld SEGS M (w_sp w + 296) 8 d /\
                     asz mod 8 = 0 /\ 0 < d /\ d + asz <= 2 ^ 63 /\ 24 <= asz /\ 0 <= len < asz
    end.

  Lemma shdr_of_str : forall (w : pmw MI ST) A M m cs, CRep.str_rep MI A M (w_sp w + 280) m cs -> shdr w M m (Zlen cs).
  Proof using AC MI ST.
    intros w A M m cs (Hs & Hs' & HD & Hlen & Hm & HC & HZ). destruct m as [|d asz]; cbn [str_cap] in Hlen; cbn [shdr].
    - split; [exact Hm | exact Hlen].
    - destruct Hm as (Hd0 & Hal & Hd63 & Hm8 & Hcap & Hin & Hsep & F0 & F1 & F2).
      replace (w_sp w + 280 + 8) with (w_sp w + 288) in F1 by lia. replace (w_sp w + 280 + 16) with (w_sp w + 296) in F2 by lia.
      unfold SSO_CAP in Hcap. repeat match goal with |- _ /\ _ => split end; first [assumption | lia].
  Qed.

  Lemma shdr_agree : forall (w : pmw MI ST) M M' m len,
    shdr w M m len -> 0 <= w_sp w -> w_sp w + 304 < 2 ^ 64 ->
    CRep.agree_on (zwin (w_sp w + 280) (w_sp w + 304)) M M' -> shdr w M' m len.
  Proof using AC MI ST.
    intros w M M' m len SH Hlo Hhi AG. destruct m as [|d asz]; cbn [shdr] in *.
    - destruct SH as [F R]. split; [| exact R]. eapply fld_agree; [lia | cbn; lia | exact F | eapply agree_on_weaken; [exact AG | unfold zwin; cbn; intros; lia]].
    - destruct SH as (F0 & F1 & F2 & R).
      split; [| split; [| split; [| exact R]]];
        (eapply fld_agree; [lia | cbn; lia | eassumption | eapply agree_on_weaken; [exact AG | unfold zwin; cbn; intros; lia]]).
  Qed.

  Lemma ext_val_zx1 : forall v, 0 <= v < 256 -> ext_val false 0 1 (Z_to_bv 64 v) = Z_to_bv 64 v.
  Proof using. intros v Hv. apply ext_val_zx_id. rewrite u64_of_Z by lia. cbn. lia. Qed.

  Lemma ls_sdtor : forall (w : pmw MI ST) c0 K (fx : FPState) A M model c R (m : sbuf) (len : Z),
    PMS w c0 K -> PMX w A M model c -> c_tr c = str_blocks m -> pm_bud (w_n w) c -> shdr w M m len ->
    getr R 2%bv = Z_to_bv 64 (w_sp w) -> getr R 3%bv = Z_to_bv 64 (ly_gp Ly.L) -> getr R 4%bv = Z_to_bv 64 (ly_tp Ly.L) ->
    (forall A' R' M' model',
        PMX w A' M' model' (set_tr c []) -> pm_bud (w_n w) (set_tr c []) ->
        getr R' 2%bv = Z_to_bv 64 (w_sp w) -> (forall r, In r SREGS -> getr R' r = getr R r) ->
        CRep.agree_on (fun a => w_sp w <= a < w_sp0 w) M M' ->
        srealizes SEGS (cfg fx R' 0x6854c M' model') K) ->
    srealizes SEGS (cfg fx R 0x68530 M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx A M model c R m len PS X Htr BUD SH Qsp Qgp Qtp CONT.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & [Gc2 Gcal] & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    destruct m as [|d asz]; cbn [str_blocks shdr] in Htr, SH.
    -
      destruct SH as [F0 Rlen]. unfold SSO_CAP in Rlen.
      assert (C280 : cellw SEGS M (w_sp w + 280) 1 (2 * len)) by (split; [cbn; lia | exact F0]).
      pm_seed R w c [Z_to_bv 64 (2 * len)].
      seedHR HR E [(2%bv, EVar 32)] R. seedHK HK w A M model c E X.
      apply (know_more E M [KWord (SA (EVar 32) 280) (N.to_nat 1) (EVar 39)]) in HK.
      2: { repeat apply Forall_cons; try apply Forall_nil.
           eapply kword_var; [exact C280 | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity]. }
      xruns HR HK 100%nat (0x6854c :: STOPS) (SCR [true] [] []) 50%N.
      { split_scs; try sc_auto1. all: cbn [sc_denot]; evs; rewrite ext_val_zx1 by lia; rewrite ?w_and by lia; rewrite ?even_land_1 by lia; rewrite ?br_eq, ?br_ne by (rewrite ?even_land_1 by lia; lia); bool_lia. }
      postrun. name_run HRn R1.
      rreg HRn (2%bv) G2. pose proof (syms_id_sound _ _ _ _ SREGS HRn eq_refl) as GS.
      clear HRn HR HK.
      eapply (CONT A R1 M model); [rewrite <- Htr, set_tr_id; exact X | rewrite <- Htr, set_tr_id; exact BUD | exact G2 | exact GS | intros a Ha; reflexivity].
    -
      destruct SH as (F0 & F1 & F2 & Hm8 & Hd0 & Hd63 & Hasz & Hlen).
      pose proof (Z.mod_pos_bound (asz + 1) 256 ltac:(lia)) as Hb0.
      assert (C280 : cellw SEGS M (w_sp w + 280) 1 ((asz + 1) mod 256)).
      { split; [cbn; lia | change (N.to_nat 1) with 1%nat; rewrite (fld8_byte0 SEGS M _ _ F0); rewrite w1_bytes_small by lia; reflexivity]. }
      assert (C280w : cellw SEGS M (w_sp w + 280) 8 (asz + 1)) by (split; [cbn; lia | exact F0]).
      assert (C296 : cellw SEGS M (w_sp w + 296) 8 d) by (split; [cbn; lia | exact F2]).
      pm_seed R w c [Z_to_bv 64 ((asz + 1) mod 256); Z_to_bv 64 (asz + 1); Z_to_bv 64 d].
      seedHR HR E [(2%bv, EVar 32)] R. seedHK HK w A M model c E X.
      apply (know_more E M [KWord (SA (EVar 32) 280) (N.to_nat 1) (EVar 39); KWord (SA (EVar 32) 280) (N.to_nat 8) (EVar 40); KWord (SA (EVar 32) 296) (N.to_nat 8) (EVar 41)]) in HK.
      2: { repeat apply Forall_cons; try apply Forall_nil.
           - eapply kword_var; [exact C280 | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
           - eapply kword_var; [exact C280w | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
           - eapply kword_var; [exact C296 | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity]. }
      xruns HR HK 100%nat (0x6854c :: STOPS) (SCR [false] [] []) 50%N.
      { split_scs; try sc_auto1. all: cbn [sc_denot]; evs; rewrite ext_val_zx1 by lia; rewrite ?w_and by lia; rewrite ?odd_byte0 by lia; rewrite ?br_eq, ?br_ne by lia; bool_lia. }
      postrun. name_run HRn R1.
      rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (10%bv) G10.
      pose proof (syms_id_sound _ _ _ _ SREGS HRn eq_refl) as GS.
      clear HRn HR HK. fixregs3. rewrite Qgp in G3. rewrite Qtp in G4.
      eapply (pm_del_tr w c0 K fx A M model c R1 0x6854c d asz PS X Htr BUD ltac:(cregs_tac G1 G2 G3 G4) G10).
      intros A' R' M' model' X' BUD' KEPT AG.
      eapply (CONT A' R' M' model' X' BUD'); [rewrite (KEPT 2%bv) by (clear; apply in_reg_list; reflexivity); exact G2 | | exact AG].
      intros r Hr. rewrite (KEPT r) by (revert Hr; clear; intros Hr; apply in_reg_list; cbn in Hr; decompose [or] Hr; try contradiction; subst r; reflexivity).
      apply GS. exact Hr.
  Qed.

  Tactic Notation "gsr" constr(GS) constr(r) ident(Q) := rewrite <- (GS r) in Q by (clear; cbn; tauto).

  Lemma ls_etail : forall (w : pmw MI ST) c0 K (fx : FPState) A M model c R (m : sbuf) (len e : Z),
    PMS w c0 K -> frm_zero (@fp_csr fx) -> CHECKK w K fx -> PMX w A M model c -> c_tr c = str_blocks m -> pm_bud (w_n w) c -> shdr w M m len ->
    getr R 2%bv = Z_to_bv 64 (w_sp w) -> getr R 3%bv = Z_to_bv 64 (ly_gp Ly.L) -> getr R 4%bv = Z_to_bv 64 (ly_tp Ly.L) ->
    getr R 8%bv = Z_to_bv 64 (w_p w) -> getr R 22%bv = sxw e -> 0 < e < 2 ^ 32 ->
    srealizes SEGS (cfg fx R 0x6852c M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx A M model c R m len e PS FZ CK X Htr BUD SH Qsp Qgp Qtp Qs0 Qs6 He.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & [Gc2 Gcal] & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.

    pm_seed R w c (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R. seedHK HK w A M model c E X.
    xruns HR HK 100%nat (0x68530 :: STOPS) (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R0.
    rreg HRn (2%bv) P2. rreg HRn (8%bv) P8. rreg HRn (24%bv) P24. pose proof (syms_id_sound _ _ _ _ [3; 4; 22]%bv HRn eq_refl) as GS0.
    clear HRn HR HK. fixregs.
    eapply (ls_sdtor w c0 K fx A M model c R0 m len PS X Htr BUD SH P2 ltac:(rewrite (GS0 3%bv) by (clear; cbn; tauto); exact Qgp) ltac:(rewrite (GS0 4%bv) by (clear; cbn; tauto); exact Qtp)).
    intros A' R' M' model' X' BUD' Q2 GS AG. pose proof (x_ms X') as MS'.
    assert (Q24 : getr R' 24%bv = Z_to_bv 64 0) by (rewrite (GS 24%bv) by (clear; cbn; tauto); exact P24).
    assert (Q8 : getr R' 8%bv = Z_to_bv 64 (w_p w)) by (rewrite (GS 8%bv) by (clear; cbn; tauto); exact P8).
    pm_seed R' w (set_tr c []) (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (24%bv, ELit 0)] R'. seedHK HK w A' M' model' (set_tr c []) E X'.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R2.
    rreg HRn (2%bv) T2. rreg HRn (3%bv) T3. rreg HRn (4%bv) T4. rreg HRn (8%bv) T8. rreg HRn (22%bv) T22.
    clear HRn HR HK. fixregs3. try replace (Z_to_bv 5 (Z.of_N 22)) with (22%bv : reg) in * by (apply bv_eq; reflexivity).
    rewrite (GS 3%bv) in T3 by (clear; cbn; tauto). rewrite (GS 4%bv) in T4 by (clear; cbn; tauto). rewrite (GS 22%bv) in T22 by (clear; cbn; tauto).
    rewrite (GS0 3%bv) in T3 by (clear; cbn; tauto). rewrite (GS0 4%bv) in T4 by (clear; cbn; tauto). rewrite (GS0 22%bv) in T22 by (clear; cbn; tauto).
    rewrite Qgp in T3. rewrite Qtp in T4. rewrite Qs6 in T22.
    exact (CK A' M' model' (set_tr c []) R2 e X' eq_refl BUD' T2 T3 T4 T8 T22 He).
  Qed.

  Lemma sxw_m4 : Z_to_bv 64 (2 ^ 64 - 4) = sxw (2 ^ 32 - 4).
  Proof using. unfold sxw. apply bv_eq. vm_compute. reflexivity. Qed.

  Lemma ls_exh : forall (w : pmw MI ST) c0 K (fx : FPState) A M model c R (m : sbuf) (len io op t : Z),
    PMS w c0 K -> frm_zero (@fp_csr fx) -> CHECKK w K fx -> PMX w A M model c -> c_tr c = str_blocks m -> pm_bud (w_n w) c -> shdr w M m len ->
    getr R 2%bv = Z_to_bv 64 (w_sp w) -> getr R 3%bv = Z_to_bv 64 (ly_gp Ly.L) -> getr R 4%bv = Z_to_bv 64 (ly_tp Ly.L) ->
    getr R 8%bv = Z_to_bv 64 (w_p w) -> getr R 23%bv = Z_to_bv 64 io -> getr R 26%bv = Z_to_bv 64 op -> getr R 27%bv = Z_to_bv 64 t ->
    0 <= io < 2 ^ 63 -> 0 <= op < 2 ^ 16 -> 0 <= t < 2 ^ 32 ->
    srealizes SEGS (cfg fx R 0x68168 M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx A M model c R m len io op t PS FZ CK X Htr BUD SH Qsp Qgp Qtp Qs0 Qs7 Qs10 Qs11 Hio Hop Ht.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & [Gc2 Gcal] & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pm_seed R w c [Z_to_bv 64 io; Z_to_bv 64 op; Z_to_bv 64 t].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (23%bv, EVar 39); (26%bv, EVar 40); (27%bv, EVar 41)] R. seedHK HK w A M model c E X.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R1.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8.
    rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12. rreg HRn (13%bv) G13.
    clear HRn HR HK. fixregs3. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_exhausted w c0 K fx A M model c R1 io op t 0x6817c PS X BUD ltac:(rewrite Htr; destruct m; unfold str_blocks, Zlength; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; lia) ltac:(cregs_tac G1 G2 G3 G4) G10 G11 G12 G13 Hio Hop Ht).
    intros A' R' M' model' X' KEPT Ha0 AG. pose proof (x_ms X') as MS'.
    keptQ KEPT G2 Q2. keptQ KEPT G3 Q3. keptQ KEPT G4 Q4. keptQ KEPT G8 Q8.
    assert (SH' : shdr w M' m len) by (eapply (shdr_agree w M M'); [exact SH | lia | lia | eapply agree_on_weaken; [exact AG | unfold zwin, w_sp0, PM_FRAME; cbn; intros; lia]]).

    pm_seed R' w c [Z_to_bv 64 (2 ^ 64 - 4)].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (10%bv, EVar 39)] R'. seedHK HK w A' M' model' c E X'.
    xruns HR HK 100%nat (0x6852c :: STOPS) (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R2.
    rreg HRn (2%bv) T2. rreg HRn (3%bv) T3. rreg HRn (4%bv) T4. rreg HRn (8%bv) T8. rreg HRn (22%bv) T22.
    clear HRn HR HK. fixregs. rewrite Q3 in T3. rewrite Q4 in T4. rewrite sxw_m4 in T22.
    eapply (ls_etail w c0 K fx A' M' model' c R2 m len (2 ^ 32 - 4) PS FZ CK X' Htr BUD SH' T2 T3 T4 T8 T22 ltac:(lia)).
  Qed.

  Lemma zlen_str_blocks : forall m, Zlength (str_blocks m) <= 1.
  Proof using. intros [|d asz]; cbn [str_blocks]; [rewrite Zlength_nil | rewrite Zlength_cons, Zlength_nil]; lia. Qed.

  Ltac lm_keep LM AG := eapply (loop_mem_frame _ _ _); [exact LM | lia | lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
  Ltac sh_keep SH AG := eapply (shdr_agree _ _ _); [exact SH | lia | lia | eapply agree_on_weaken; [exact AG | unfold frame_but, zwin, w_sp0, PM_FRAME, DS_SIZE; cbn; intros; lia]].
  Lemma half_even : forall n, 0 <= n -> 2 * n / 2 ^ 1 = n.
  Proof using. intros n Hn. change (2 ^ 1) with 2. rewrite Z.mul_comm. apply Z.div_mul. lia. Qed.

  Lemma ls_dtail : forall (w : pmw MI ST) c0 K (fx : FPState) A M model c R (m : sbuf) (len dlen p n : Z) (B : list (Z * Z)),
    PMS w c0 K -> frm_zero (@fp_csr fx) -> CHECKK w K fx -> PMX w A M model c -> c_tr c = B ++ str_blocks m -> pm_bud (w_n w) c ->
    ds_rep A M (w_sp w + 304) (-4) dlen B -> ro_cstr SEGS Ly.L p n -> 0 <= n -> dlen + n <= DS_MAXLEN ->
    shdr w M m len ->
    cregs w R 0x68520 ->
    getr R 8%bv = Z_to_bv 64 (w_p w) -> getr R 10%bv = Z_to_bv 64 (w_sp w + 304) -> getr R 11%bv = Z_to_bv 64 p -> getr R 12%bv = Z_to_bv 64 n ->
    srealizes SEGS (cfg fx R (dc_put_cstr dcU1) M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx A M model c R m len dlen p n B PS FZ CK X Htr BUD DS RO Hn Hlen SH CR Qs0 Ha0 Ha1 Ha2.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & [Gc2 Gcal] & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof (zlen_str_blocks m) as Hrest. pose proof CR as (C1 & C2 & C3 & C4 & C5 & C6).
    eapply (pm_put_cstr w c0 K fx A M model c R (-4) _ p n n _ B (str_blocks m));
      [exact PS | exact X | exact Htr | exact BUD | exact Hrest | exact DS | exact CR | exact Ha0 | exact Ha1 | exact Ha2 | exact RO | lia | exact Hlen |].
    intros A6 R6c M6 model6 B6 X6 BUD6 KEPT _ DS6 AG.
    keptQ KEPT C4 Qsp6. keptQ KEPT C5 Qgp6. keptQ KEPT C6 Qtp6. keptQ KEPT Qs0 Qs06.
    assert (SH6 : shdr w M6 m len) by sh_keep SH AG.
    clear KEPT AG. pose proof (x_ms X6) as MS6. cbn [set_tr] in X6, BUD6.

    pose proof (dl_err _ _ _ _ _ _ DL _ _ _ _ _ _ DS6) as Herrc. unfold CRep.fld in Herrc.
    assert (Cerr : cell4 SEGS M6 (w_sp w + 304 + 360) ((-4) mod 2 ^ 32)).
    { split; [pose proof (Z.mod_pos_bound (-4) (2 ^ 32)); cbn; lia | exact Herrc]. }
    pm_seed R6c w (set_tr c (B6 ++ str_blocks m)) [sxw ((-4) mod 2 ^ 32)].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R6c. seedHK HK w A6 M6 model6 (set_tr c (B6 ++ str_blocks m)) E X6.
    xruns HR HK 100%nat STOPS (SCR [] [EVar 39] []) 50%N. { split_scs; try sc_auto1. all: sc_rd_sx Cerr. }
    postrun. name_run HRn R7. rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (22%bv) G22.
    clear HRn HR HK. fixregs. rewrite Qgp6 in G3. rewrite Qtp6 in G4. rewrite w_add in G10 by lia.
    try replace (Z_to_bv 5 (Z.of_N 22)) with (22%bv : reg) in * by (apply bv_eq; reflexivity).
    eapply (pm_dtor w c0 K fx A6 M6 model6 (set_tr c (B6 ++ str_blocks m)) R7 (-4) _ _ B6 (str_blocks m));
      [exact PS | exact X6 | reflexivity | exact BUD6 | exact Hrest | exact DS6 | cregs_tac G1 G2 G3 G4 | exact G10 |].
    intros Ad Rd Md modeld Xd BUDd KEPT AGd.
    keptQ KEPT G2 Qsp'. keptQ KEPT G3 Qgp'. keptQ KEPT G4 Qtp'. keptQ KEPT G8 Qs0'. keptQ KEPT G22 Qs6.
    assert (SHd : shdr w Md m len) by sh_keep SH6 AGd.
    pose proof (x_ms Xd) as MSd. cbn [set_tr] in Xd, BUDd.
    assert (Hm4 : (-4) mod 2 ^ 32 = 2 ^ 32 - 4) by reflexivity. rewrite Hm4 in Qs6.
    exact (ls_etail w c0 K fx Ad Md modeld (set_tr c (str_blocks m)) Rd m len (2 ^ 32 - 4) PS FZ CK Xd ltac:(reflexivity) BUDd SHd Qsp' Qgp' Qtp' Qs0' Qs6 ltac:(lia)).
  Qed.

  Lemma ls_toolong : forall (w : pmw MI ST) c0 K (fx : FPState) A M model c R (m : sbuf) (len nwq : Z),
    PMS w c0 K -> frm_zero (@fp_csr fx) -> CHECKK w K fx -> PMX w A M model c -> c_tr c = str_blocks m -> pm_bud (w_n w) c ->
    shdr w M m len -> loop_mem w M ->
    getr R 2%bv = Z_to_bv 64 (w_sp w) -> getr R 3%bv = Z_to_bv 64 (ly_gp Ly.L) -> getr R 4%bv = Z_to_bv 64 (ly_tp Ly.L) ->
    getr R 8%bv = Z_to_bv 64 (w_p w) -> getr R 22%bv = Z_to_bv 64 nwq -> 0 <= nwq < 2 ^ 62 ->
    srealizes SEGS (cfg fx R 0x682d8 M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx A M model c R m len nwq PS FZ CK X Htr BUD SH LM Qsp Qgp Qtp Qs0 Qs6 Hnwq.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & [Gc2 Gcal] & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof (x_scal X) as (Sc1 & Sc2 & Sc3 & Sc4). pose proof (zlen_str_blocks m) as Hrest.

    pm_seed R w c (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R. seedHK HK w A M model c E X.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R1.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    pose proof (syms_id_sound _ _ _ _ [22]%bv HRn eq_refl) as GS1.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_pdiagQ w c0 K fx A M model c R1 (-4) _ (str_blocks m));
      [exact PS | exact X | exact Htr | exact BUD | exact Hrest | cregs_tac G1 G2 G3 G4 | exact G10 | exact G11 | rewrite G12; apply bv_eq; vm_compute; reflexivity | lia |].
    intros A1 R1c M1 model1 B1 X1 BUD1 KEPT DS1 AG.
    keptQ KEPT G2 Qsp1. keptQ KEPT G8 Qs01. keptQ KEPT G3 Qgp1. keptQ KEPT G4 Qtp1.
    assert (Qs61 : getr R1c 22%bv = Z_to_bv 64 nwq) by (rewrite (KEPT 22%bv) by (clear; apply in_reg_list; reflexivity); rewrite (GS1 22%bv) by (first [solve [clear; cbn; tauto] | cbn; tauto]); exact Qs6).
    assert (LM1 : loop_mem w M1) by lm_keep LM AG. assert (SH1 : shdr w M1 m len) by sh_keep SH AG.
    clear G1 G2 G3 G4 G8 G10 G11 G12 KEPT AG GS1. pose proof (x_ms X1) as MS1.

    pm_seed R1c w (set_tr c (B1 ++ str_blocks m)) (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R1c. seedHK HK w A1 M1 model1 (set_tr c (B1 ++ str_blocks m)) E X1.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R2.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    pose proof (syms_id_sound _ _ _ _ [22]%bv HRn eq_refl) as GS2.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp1 in G3. rewrite Qtp1 in G4.
    eapply (pm_put_cstr w c0 K fx A1 M1 model1 (set_tr c (B1 ++ str_blocks m)) R2 (-4) _ 0x12995 30 30 _ B1 (str_blocks m));
      [exact PS | exact X1 | reflexivity | exact BUD1 | exact Hrest | exact DS1 | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | apply ro_cstr_of_chk; vm_compute; reflexivity | lia | unfold DS_MAXLEN; lia |].
    intros A2 R2c M2 model2 B2 X2 BUD2 KEPT _ DS2 AG.
    keptQ KEPT G2 Qsp2. keptQ KEPT G8 Qs02. keptQ KEPT G3 Qgp2. keptQ KEPT G4 Qtp2.
    assert (Qs62 : getr R2c 22%bv = Z_to_bv 64 nwq) by (rewrite (KEPT 22%bv) by (clear; apply in_reg_list; reflexivity); rewrite (GS2 22%bv) by (first [solve [clear; cbn; tauto] | cbn; tauto]); exact Qs61).
    assert (LM2 : loop_mem w M2) by lm_keep LM1 AG. assert (SH2 : shdr w M2 m len) by sh_keep SH1 AG.
    clear G1 G2 G3 G4 G8 G10 G11 G12 KEPT AG GS2 X1 BUD1 DS1 LM1 SH1 MS1. pose proof (x_ms X2) as MS2. cbn [set_tr] in X2, BUD2.

    pm_seed R2c w (set_tr c (B2 ++ str_blocks m)) (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R2c. seedHK HK w A2 M2 model2 (set_tr c (B2 ++ str_blocks m)) E X2.
    apply (know_more E M2 [KWord (SA (EVar 32) 24) (N.to_nat 8) (ELit 65535)]) in HK.
    2: { repeat apply Forall_cons; try apply Forall_nil.
         eapply kword_var; [eapply (loop_mem_cell w M2 24); [exact LM2 | (first [ solve [cbn [In]; repeat (first [left; reflexivity | right])] | cbn; repeat (first [left; reflexivity | right]) ]) | lia] | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity]. }
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R3.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11.
    pose proof (syms_id_sound _ _ _ _ [22]%bv HRn eq_refl) as GS3.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp2 in G3. rewrite Qtp2 in G4.
    eapply (pm_put_u16 w c0 K fx A2 M2 model2 (set_tr c (B2 ++ str_blocks m)) R3 (-4) _ 65535 _ B2 (str_blocks m));
      [exact PS | exact X2 | reflexivity | exact BUD2 | exact Hrest | exact DS2 | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | lia | unfold DS_MAXLEN; lia |].
    intros A3 R3c M3 model3 B3 X3 BUD3 KEPT _ DS3 AG.
    keptQ KEPT G2 Qsp3. keptQ KEPT G8 Qs03. keptQ KEPT G3 Qgp3. keptQ KEPT G4 Qtp3.
    assert (Qs63 : getr R3c 22%bv = Z_to_bv 64 nwq) by (rewrite (KEPT 22%bv) by (clear; apply in_reg_list; reflexivity); rewrite (GS3 22%bv) by (first [solve [clear; cbn; tauto] | cbn; tauto]); exact Qs62).
    assert (LM3 : loop_mem w M3) by lm_keep LM2 AG. assert (SH3 : shdr w M3 m len) by sh_keep SH2 AG.
    clear G1 G2 G3 G4 G8 G10 G11 KEPT AG GS3 X2 BUD2 DS2 LM2 SH2 MS2. pose proof (x_ms X3) as MS3. cbn [set_tr] in X3, BUD3.

    pm_seed R3c w (set_tr c (B3 ++ str_blocks m)) (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R3c. seedHK HK w A3 M3 model3 (set_tr c (B3 ++ str_blocks m)) E X3.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R4.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    pose proof (syms_id_sound _ _ _ _ [22]%bv HRn eq_refl) as GS4.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp3 in G3. rewrite Qtp3 in G4.
    eapply (pm_put_cstr w c0 K fx A3 M3 model3 (set_tr c (B3 ++ str_blocks m)) R4 (-4) _ 0x123fb 8 8 _ B3 (str_blocks m));
      [exact PS | exact X3 | reflexivity | exact BUD3 | exact Hrest | exact DS3 | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | apply ro_cstr_of_chk; vm_compute; reflexivity | lia | unfold DS_MAXLEN; lia |].
    intros A4 R4c M4 model4 B4 X4 BUD4 KEPT _ DS4 AG.
    keptQ KEPT G2 Qsp4. keptQ KEPT G8 Qs04. keptQ KEPT G3 Qgp4. keptQ KEPT G4 Qtp4.
    assert (Qs64 : getr R4c 22%bv = Z_to_bv 64 nwq) by (rewrite (KEPT 22%bv) by (clear; apply in_reg_list; reflexivity); rewrite (GS4 22%bv) by (first [solve [clear; cbn; tauto] | cbn; tauto]); exact Qs63).
    assert (LM4 : loop_mem w M4) by lm_keep LM3 AG. assert (SH4 : shdr w M4 m len) by sh_keep SH3 AG.
    clear G1 G2 G3 G4 G8 G10 G11 G12 KEPT AG GS4 X3 BUD3 DS3 LM3 SH3 MS3. pose proof (x_ms X4) as MS4. cbn [set_tr] in X4, BUD4.

    pm_seed R4c w (set_tr c (B4 ++ str_blocks m)) [Z_to_bv 64 nwq].
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33); (22%bv, EVar 39)] R4c. seedHK HK w A4 M4 model4 (set_tr c (B4 ++ str_blocks m)) E X4.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R5.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp4 in G3. rewrite Qtp4 in G4.
    eapply (pm_put_u64 w c0 K fx A4 M4 model4 (set_tr c (B4 ++ str_blocks m)) R5 (-4) _ nwq _ B4 (str_blocks m));
      [exact PS | exact X4 | reflexivity | exact BUD4 | exact Hrest | exact DS4 | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | lia | unfold DS_MAXLEN; lia |].
    intros A5 R5c M5 model5 B5 X5 BUD5 KEPT _ DS5 AG.
    keptQ KEPT G2 Qsp5. keptQ KEPT G8 Qs05. keptQ KEPT G3 Qgp5. keptQ KEPT G4 Qtp5.
    assert (LM5 : loop_mem w M5) by lm_keep LM4 AG. assert (SH5 : shdr w M5 m len) by sh_keep SH4 AG.
    clear G1 G2 G3 G4 G8 G10 G11 KEPT AG X4 BUD4 DS4 LM4 SH4 MS4. pose proof (x_ms X5) as MS5. cbn [set_tr] in X5, BUD5.

    pm_seed R5c w (set_tr c (B5 ++ str_blocks m)) (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R5c. seedHK HK w A5 M5 model5 (set_tr c (B5 ++ str_blocks m)) E X5.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R6.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp5 in G3. rewrite Qtp5 in G4.
    lazymatch type of G11 with _ = Z_to_bv 64 ?p => lazymatch type of G12 with _ = Z_to_bv 64 ?n =>
      assert (RO2 : ro_cstr SEGS Ly.L p n) by (apply ro_cstr_of_chk; vm_compute; reflexivity) end end.
    eapply (ls_dtail w c0 K fx A5 M5 model5 (set_tr c (B5 ++ str_blocks m)) R6 m len _ _ _ B5 PS FZ CK X5 ltac:(reflexivity) BUD5 DS5 RO2 ltac:(lia) ltac:(unfold DS_MAXLEN; lia) SH5
              ltac:(cregs_tac G1 G2 G3 G4) G8 G10 G11 G12).
  Qed.

  Lemma ls_badimport : forall (w : pmw MI ST) c0 K (fx : FPState) A M model c R (m : sbuf) (len : Z),
    PMS w c0 K -> frm_zero (@fp_csr fx) -> CHECKK w K fx -> PMX w A M model c -> c_tr c = str_blocks m -> pm_bud (w_n w) c ->
    shdr w M m len -> len < 0x3fffc ->
    getr R 2%bv = Z_to_bv 64 (w_sp w) -> getr R 3%bv = Z_to_bv 64 (ly_gp Ly.L) -> getr R 4%bv = Z_to_bv 64 (ly_tp Ly.L) ->
    getr R 8%bv = Z_to_bv 64 (w_p w) ->
    srealizes SEGS (cfg fx R 0x6846c M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx A M model c R m len PS FZ CK X Htr BUD SH Hcs Qsp Qgp Qtp Qs0.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & [Gc2 Gcal] & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof (x_scal X) as (Sc1 & Sc2 & Sc3 & Sc4). pose proof (zlen_str_blocks m) as Hrest.
    assert (Hlen0 : 0 <= len) by (destruct m; cbn [shdr] in SH; lia).

    pm_seed R w c (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R. seedHK HK w A M model c E X.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R1.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_pdiagQ w c0 K fx A M model c R1 (-4) _ (str_blocks m));
      [exact PS | exact X | exact Htr | exact BUD | exact Hrest | cregs_tac G1 G2 G3 G4 | exact G10 | exact G11 | rewrite G12; apply bv_eq; vm_compute; reflexivity | lia |].
    intros A1 R1c M1 model1 B1 X1 BUD1 KEPT DS1 AG.
    keptQ KEPT G2 Qsp1. keptQ KEPT G8 Qs01. keptQ KEPT G3 Qgp1. keptQ KEPT G4 Qtp1.
    assert (SH1 : shdr w M1 m len) by sh_keep SH AG.
    clear G1 G2 G3 G4 G8 G10 G11 G12 KEPT AG. pose proof (x_ms X1) as MS1.

    pm_seed R1c w (set_tr c (B1 ++ str_blocks m)) (@nil word).
    seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R1c. seedHK HK w A1 M1 model1 (set_tr c (B1 ++ str_blocks m)) E X1.
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R2.
    rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
    rewrite w_add in G10 by lia.
    clear HRn HR HK. fixregs. rewrite Qgp1 in G3. rewrite Qtp1 in G4.
    eapply (pm_put_cstr w c0 K fx A1 M1 model1 (set_tr c (B1 ++ str_blocks m)) R2 (-4) _ 0x11bd6 37 37 _ B1 (str_blocks m));
      [exact PS | exact X1 | reflexivity | exact BUD1 | exact Hrest | exact DS1 | cregs_tac G1 G2 G3 G4
      | exact G10 | exact G11 | exact G12 | apply ro_cstr_of_chk; vm_compute; reflexivity | lia | unfold DS_MAXLEN; lia |].
    intros A2 R2c M2 model2 B2 X2 BUD2 KEPT _ DS2 AG.
    keptQ KEPT G2 Qsp2. keptQ KEPT G8 Qs02. keptQ KEPT G3 Qgp2. keptQ KEPT G4 Qtp2. cbn [set_tr] in X2, BUD2.
    assert (SH2 : shdr w M2 m len) by sh_keep SH1 AG.
    clear G1 G2 G3 G4 G8 G10 G11 G12 KEPT AG X1 BUD1 DS1 SH1 MS1. pose proof (x_ms X2) as MS2. pose proof (x_ai X2) as AI2.
    pose proof (dl_blocks _ _ _ _ _ _ DL _ _ _ _ _ _ DS2) as [HB2len HB2in].
    assert (WD2 : forall t n, w_sp w <= t -> t + n <= w_sp w + 864 -> mdef M2 t n).
    { intros t n Ht Hn i Hi. pose proof (x_wdef X2 (t + i - (w_sp w + 864 - w_STK w)) ltac:(unfold w_sp0, PM_FRAME; lia)) as D.
      unfold w_sp0, PM_FRAME in D. replace (w_sp w + 864 - w_STK w + (t + i - (w_sp w + 864 - w_STK w))) with (t + i) in D by lia. exact D. }

    assert (STREAM : forall R3 (p : Z), cregs w R3 0x6850c -> getr R3 8%bv = Z_to_bv 64 (w_p w) ->
              getr R3 10%bv = Z_to_bv 64 (w_sp w + 304) -> getr R3 11%bv = Z_to_bv 64 p -> getr R3 12%bv = Z_to_bv 64 len ->
              p = str_data (w_sp w + 280) m ->
              srealizes SEGS (cfg fx R3 (dc_put_cstr dcU1) M2 model2) K).
    { intros R3 p CR3 Y8 Y10 Y11 Y12 Hp. pose proof CR3 as (C1 & C2 & C3 & C4 & C5 & C6).
      assert (HP : 0 < p /\ p + len <= 2 ^ 47 /\ mdef M2 p len /\
                   (forall a, zwin p (p + len) a -> ~ zwin (w_sp w + 304) (w_sp w + 304 + DS_SIZE) a /\
                      (w_sp w <= a \/ (exists q k, In (q, k) (live MI A2) /\ q <= a < q + k /\ ~ In (q, k) B2)))).
      { subst p. destruct m as [|d asz]; cbn [str_data shdr str_blocks] in *.
        - destruct SH2 as [F0 Rl]. unfold SSO_CAP in Rl. split; [lia|]. split; [lia|]. split; [apply WD2; lia|].
          intros a Ha. unfold zwin, DS_SIZE in *. split; [lia | left; lia].
        - destruct SH2 as (F0 & F1 & F2 & Hm8 & Hd0 & Hd63 & Hasz & Hl0).
          pose proof (x_live X2) as PL. rewrite c_blocks_split in PL. cbn [c_tr set_tr] in PL.
          assert (HIn : In (d, asz) (live MI A2)).
          { apply (Permutation_in (d, asz) (Permutation_sym PL)). rewrite !in_app_iff. right; right; right; left; reflexivity. }
          assert (HnB : ~ In (d, asz) B2).
          { intros HdB. pose proof (perm_nodup_fst _ _ PL (ai_live_nodup MI A2 M2 model2 AI2)) as ND.
            rewrite !app_assoc in ND. rewrite map_app in ND. apply (proj1 (list_relations.list.NoDup_app _ _)) in ND. destruct ND as (_ & HX & _).
            apply (HX d); apply list_elem_of_In; [rewrite map_app, in_app_iff; right; apply in_map_iff; exists (d, asz); auto | cbn; left; reflexivity]. }
          destruct (ai_live_block MI A2 M2 model2 d asz AI2 HIn) as (_ & _ & _ & Hdc & Hpay).
          split; [lia|]. split; [lia|]. split; [intros i Hi; exact (proj2 (proj2 (Hpay (d + i) ltac:(lia))))|].
          intros a Ha. unfold zwin, DS_SIZE in *. split; [lia | right]. exists d, asz. split; [exact HIn|]. split; [lia | exact HnB]. }
      destruct HP as (P0 & P47 & PD & PW).
      eapply (pm_put_chars w c0 K fx A2 M2 model2 (set_tr c (B2 ++ str_blocks m)) R3 (-4) _ p len _ B2 (str_blocks m));
        [exact PS | exact X2 | reflexivity | exact BUD2 | exact Hrest | exact DS2 | exact CR3 | exact Y10 | exact Y11 | exact Y12 | lia | exact P0 | exact P47 | exact PD | exact PW | unfold DS_MAXLEN; lia |].
      intros A3 R3c M3 model3 B3 X3 BUD3 KEPT Ha0 DS3 AG.
      keptQ KEPT C4 Qsp3. keptQ KEPT Y8 Qs03. keptQ KEPT C5 Qgp3. keptQ KEPT C6 Qtp3. cbn [set_tr] in X3, BUD3.
      assert (SH3 : shdr w M3 m len) by sh_keep SH2 AG.
      clear KEPT AG. pose proof (x_ms X3) as MS3.

      pm_seed R3c w (set_tr c (B3 ++ str_blocks m)) (@nil word).
      seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R3c. seedHK HK w A3 M3 model3 (set_tr c (B3 ++ str_blocks m)) E X3.
      xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
      postrun. name_run HRn R4.
      rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
      rewrite w_add in G10 by lia.
      clear HRn HR HK. fixregs. rewrite Qgp3 in G3. rewrite Qtp3 in G4.
      lazymatch type of G11 with _ = Z_to_bv 64 ?p' => lazymatch type of G12 with _ = Z_to_bv 64 ?n' =>
        assert (RO2 : ro_cstr SEGS Ly.L p' n') by (apply ro_cstr_of_chk; vm_compute; reflexivity) end end.
      eapply (ls_dtail w c0 K fx A3 M3 model3 (set_tr c (B3 ++ str_blocks m)) R4 m len _ _ _ B3 PS FZ CK X3 ltac:(reflexivity) BUD3 DS3 RO2 ltac:(lia) ltac:(unfold DS_MAXLEN; lia) SH3
                ltac:(cregs_tac G1 G2 G3 G4) G8 G10 G11 G12). }
    destruct m as [|d asz]; cbn [shdr str_data] in SH2, STREAM.
    -
      destruct SH2 as [F0 Rl]. unfold SSO_CAP in Rl.
      assert (C280 : cellw SEGS M2 (w_sp w + 280) 1 (2 * len)) by (split; [cbn; lia | exact F0]).
      pm_seed R2c w (set_tr c (B2 ++ [])) [Z_to_bv 64 (2 * len)].
      seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R2c. seedHK HK w A2 M2 model2 (set_tr c (B2 ++ [])) E X2.
      apply (know_more E M2 [KWord (SA (EVar 32) 280) (N.to_nat 1) (EVar 39)]) in HK.
      2: { repeat apply Forall_cons; try apply Forall_nil.
           eapply kword_var; [exact C280 | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity]. }
      xruns HR HK 100%nat STOPS (SCR [true] [] []) 50%N.
      { split_scs; try sc_auto1. all: cbn [sc_denot]; evs; rewrite ext_val_zx1 by lia; rewrite ?w_and by lia; rewrite ?even_land_1 by lia; rewrite ?br_eq, ?br_ne by (rewrite ?even_land_1 by lia; lia); bool_lia. }
      postrun. name_run HRn R3.
      rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
      clear HRn HR HK. fixregs. rewrite Qgp2 in G3. rewrite Qtp2 in G4. rewrite w_add in G10, G11 by lia.
      rewrite ext_val_zx1 in G12 by lia. rewrite w_srl in G12 by lia. rewrite half_even in G12 by lia.
      exact (STREAM R3 (w_sp w + 281) ltac:(cregs_tac G1 G2 G3 G4) G8 G10 G11 G12 ltac:(lia)).
    -
      destruct SH2 as (F0 & F1 & F2 & Hm8 & Hd0 & Hd63 & Hasz & Hl0).
      pose proof (Z.mod_pos_bound (asz + 1) 256 ltac:(lia)) as Hb0.
      assert (C280 : cellw SEGS M2 (w_sp w + 280) 1 ((asz + 1) mod 256)).
      { split; [cbn; lia | change (N.to_nat 1) with 1%nat; rewrite (fld8_byte0 SEGS M2 _ _ F0); rewrite w1_bytes_small by lia; reflexivity]. }
      assert (C288 : cellw SEGS M2 (w_sp w + 288) 8 len) by (split; [cbn; lia | exact F1]).
      assert (C296 : cellw SEGS M2 (w_sp w + 296) 8 d) by (split; [cbn; lia | exact F2]).
      pm_seed R2c w (set_tr c (B2 ++ [(d, asz)])) [Z_to_bv 64 ((asz + 1) mod 256); Z_to_bv 64 len; Z_to_bv 64 d].
      seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R2c. seedHK HK w A2 M2 model2 (set_tr c (B2 ++ [(d, asz)])) E X2.
      apply (know_more E M2 [KWord (SA (EVar 32) 280) (N.to_nat 1) (EVar 39); KWord (SA (EVar 32) 288) (N.to_nat 8) (EVar 40); KWord (SA (EVar 32) 296) (N.to_nat 8) (EVar 41)]) in HK.
      2: { repeat apply Forall_cons; try apply Forall_nil.
           - eapply kword_var; [exact C280 | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
           - eapply kword_var; [exact C288 | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity].
           - eapply kword_var; [exact C296 | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity]. }
      xruns HR HK 100%nat STOPS (SCR [false] [] []) 50%N.
      { split_scs; try sc_auto1. all: cbn [sc_denot]; evs; rewrite ext_val_zx1 by lia; rewrite ?w_and by lia; rewrite ?odd_byte0 by lia; rewrite ?br_eq, ?br_ne by lia; bool_lia. }
      postrun. name_run HRn R3.
      rreg HRn (1%bv) G1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (10%bv) G10. rreg HRn (11%bv) G11. rreg HRn (12%bv) G12.
      clear HRn HR HK. fixregs. rewrite Qgp2 in G3. rewrite Qtp2 in G4. rewrite w_add in G10 by lia.
      exact (STREAM R3 d ltac:(cregs_tac G1 G2 G3 G4) G8 G10 G11 G12 ltac:(reflexivity)).
  Qed.
End PM.
