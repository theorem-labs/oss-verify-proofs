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
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep2U1.PmUpdU1. From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PmStep2U1.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PeLia.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
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

  #[local] Notation pmx_updJS := (pmx_updJ SEGS Ly.L MI ST ly_img_low ly_rw_img ly_relro_img ly_errno_img ly_rw_not_relro ly_errno_rw).
  #[local] Notation pmx_upd_ownS := (PmStep2U1.pmx_upd_own).
  #[local] Notation live_splitS := (live_split SEGS Ly.L MI ST).
  #[local] Notation live_joinS := (live_join SEGS Ly.L MI ST).
  #[local] Notation pushes_post := (TablStmts.pushes_post SEGS Ly.L MI).
  #[local] Notation pushes_fp := (TablStmts.pushes_fp SEGS Ly.L MI).
  #[local] Notation room_pushes := (TablStmts.room_pushes SEGS Ly.L MI).

  Lemma pushes_perm : forall (A A' : AS MI) M M' model model' (len0 k0 b cap b' cap' : Z) (R : list (Z * Z)),
    ainv MI A M model -> ainv MI A' M' model' ->
    Permutation (live MI A) ((if b =? 0 then [] else [(b, 4 * cap)]) ++ R) ->
    0 <= cap -> (b' = 0 -> cap' = 0) ->
    pushes_post A A' len0 k0 b cap b' cap' ->
    Permutation (live MI A') ((if b' =? 0 then [] else [(b', 4 * cap')]) ++ R).
  Proof using AC MI.
    intros A A' M M' model model' len0 k0 b cap b' cap' R AI AI' P Hcap Hb' (Hle & Hsame & Hgrow).
    pose proof (ai_live_nodup MI A M model AI) as ND. pose proof (ai_live_nodup MI A' M' model' AI') as ND'.
    destruct (Z.eq_dec cap' cap) as [Ec|Nc].
    { destruct (Hsame Ec) as [-> E]. rewrite E. subst cap'. exact P. }
    destruct (Hgrow Nc) as [MEM NEW]. clear Hsame Hgrow.
    destruct (Z.eqb_spec b' 0) as [E0|N0]; [pose proof (Hb' E0); lia|]. cbn.
    pose proof (perm_nodup_fst _ _ P ND) as NR.
    assert (HRin : forall q k, In (q, k) R -> In (q, k) (live MI A) /\ q <> b).
    { intros q k Hin. split.
      - apply (Permutation_in (q, k) (Permutation_sym P)). apply in_app_iff. right. exact Hin.
      - destruct (Z.eqb_spec b 0) as [Eb|Nb].
        + assert (Hl : In (q, k) (live MI A)) by (apply (Permutation_in (q, k) (Permutation_sym P)); exact Hin).
          destruct (ai_live_block MI A M model q k AI Hl) as (_ & _ & Hq & _). lia.
        + cbn in NR. intros ->. apply (nodup_fst_notin (b, 4 * cap) R NR). cbn. apply in_map_iff. exists (b, k). split; [reflexivity | exact Hin]. }
    assert (NRR : NoDup (map fst R)) by (destruct (Z.eqb_spec b 0); [exact NR | exact (nodup_fst_tail _ _ NR)]).
    apply live_equiv_perm; [exact ND' | |].
    - cbn. apply NoDup_cons_2; [| exact NRR]. intros Hin. apply list_elem_of_In in Hin. apply in_map_iff in Hin.
      destruct Hin as ([q k] & Hq & Hin). cbn in Hq. subst q. destruct (HRin _ _ Hin) as [Hl Hnb]. exact (NEW _ _ Hl Hnb eq_refl).
    - intros q k. rewrite (MEM q k). cbn. split.
      + intros [[Hl Hnb]|[-> ->]]; [| left; reflexivity]. right.
        apply (Permutation_in (q, k) P) in Hl. apply in_app_iff in Hl. destruct Hl as [Hl|Hl]; [| exact Hl].
        destruct (Z.eqb_spec b 0); [destruct Hl|]. destruct Hl as [E|[]]. injection E. lia.
      + intros [E|Hin]; [injection E; intros; subst; right; split; reflexivity | left; exact (HRin _ _ Hin)].
  Qed.

  Lemma pm_v3_clear : forall (w : pmw MI ST) A M model c (b : Z),
    PMX w A M model c -> t3a (c_v3 c) = b ->
    PMX w A (wbytes M (Z_to_bv 64 (w_p w + 272)) (word_to_le_bytes 8 (Z_to_bv 64 b))) model (set_v3 c (b, [], t3c (c_v3 c))).
  Proof using AC MI ST.
    intros w A M model c b X Eb. pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & [Gc2 Gcal] & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof (x_v3 X) as V. destruct (c_v3 c) as [[b0 xs] cap] eqn:Ev3. cbn [t3a t3b t3c fst snd] in *. subst b0.
    assert (SI : stores_in (zwin (w_p w + 272) (w_p w + 280)) M (wbytes M (Z_to_bv 64 (w_p w + 272)) (word_to_le_bytes 8 (Z_to_bv 64 b)))) by stin.
    eapply (pmx_upd_ownS CV3 w A M _ model c _ _ X SI);
      [intros a Ha; cbn; unfold O_V3, zwin in *; lia | intros j Hj; destruct j; cbn; first [reflexivity | exfalso; exact (Hj eq_refl)]
      | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | cbn; rewrite Ev3; reflexivity |].
    cbn [crep set_v3 c_v3 t3a t3b t3c fst snd]. destruct V as (V1 & V2 & V3 & V4 & V5 & F0 & F1 & F2 & FE). unfold O_V3 in *.
    split; [exact V1|]. split; [exact V2|]. split; [eapply stores_in_mdef; [exact SI | exact V3]|]. split; [unfold Zlen; cbn; lia|]. split; [exact V5|].
    split; [eapply fld_keep; [exact SI | exact F0 | lia | cbn; lia | unfold zwin; cbn; intros; lia]|].
    split; [unfold Zlen; cbn [length Z.of_nat]; rewrite Z.mul_0_r, Z.add_0_r; replace (w_p w + 264 + 8) with (w_p w + 272) by lia; rdback|].
    split; [eapply fld_keep; [exact SI | exact F2 | lia | cbn; lia | unfold zwin; cbn; intros; lia]|].
    intros k Hk. unfold Zlen in Hk. cbn in Hk. lia.
  Qed.

  Lemma pmx_v3_pushes : forall (w : pmw MI ST) A M model c A' M' model' (S : Z) (len k b cap b' cap' : Z) (xs xs' : list Z),
    PMX w A M model c -> c_v3 c = (b, xs, cap) ->
    ainv MI A' M' model' -> mstd model' -> m_fs model' = m_fs model -> m_fds model' = m_fds model ->
    eff MI A A' M M' (w_sp w - S, w_sp w) (pushes_fp A (w_p w + O_V3) b cap b' cap') -> 0 <= S <= w_STK w - PM_FRAME ->
    vec32 MI A' M' (w_p w + O_V3) b' xs' cap' -> pushes_post A A' len k b cap b' cap' ->
    PMX w A' M' model' (set_v3 c (b', xs', cap')).
  Proof using AC MI ST.
    intros w A M model c A' M' model' S len k b cap b' cap' xs xs' X Ev3 AI' MS' FS' FDS' EF HS V' PP.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ai X) as AI.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & [Gc2 Gcal] & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof (x_v3 X) as V. rewrite Ev3 in V. cbn [t3a t3b t3c fst snd] in V.
    pose proof V as V0. destruct V0 as (_ & _ & _ & Hlen & Hblk & _).
    pose proof V' as V1. destruct V1 as (_ & _ & _ & Hlen' & Hblk' & _).
    set (c' := set_v3 c (b', xs', cap')).
    eapply (pmx_updJS w CV3 A M model c A' M' model' c' S _ X AI' MS' FS' FDS' EF);
      [exact HS | | | intros j Hj; destruct j; cbn; first [reflexivity | exfalso; exact (Hj eq_refl)]
      | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | cbn; exact V' |].
    - intros a [Ha|[[Hb Ha]|[Ha|Hj]]].
      + left. left. unfold O_V3 in *. cbn. exact Ha.
      + left. right. exists (b, 4 * cap). cbn. rewrite Ev3. cbn. destruct (Z.eqb_spec b 0); [lia|]. split; [left; reflexivity | unfold zwin in Ha; lia].
      + right. left. right. exists (b', 4 * cap'). cbn. destruct (Z.eqb_spec b' 0); [unfold zwin in Ha; lia|]. split; [left; reflexivity | unfold zwin in Ha; lia].
      + right. right. right. exact Hj.
    - intros a [Ha|[[Hb Ha]|[Ha|Hj]]] Hz; exfalso; unfold zwin, O_V3, w_sp0, PM_FRAME in *; [lia | | |].
      + destruct Hblk as [[-> _]|(_ & _ & _ & _ & Hl & _)]; [lia|]. destruct (ai_live_block MI A M model _ _ AI Hl) as (_ & _ & _ & Hc' & _). lia.
      + destruct Hblk' as [[-> ->]|(_ & _ & _ & _ & Hl & _)]; [lia|]. destruct (ai_live_block MI A' M' model' _ _ AI' Hl) as (_ & _ & _ & Hc' & _). lia.
      + destruct Hj as (Hj & _). lia.
    - eapply (live_joinS w A' c c' CV3); [intros j Hj; destruct j; cbn; first [reflexivity | exfalso; exact (Hj eq_refl)] | reflexivity |].
      cbn [cblocks c' set_v3 c_v3 t3a t3c fst snd].
      eapply (pushes_perm A A' M M' model model' len k b cap b' cap'); [exact AI | exact AI' | | lia | | exact PP].
      + pose proof (live_splitS w A M model c CV3 X) as P. cbn [cblocks] in P. rewrite Ev3 in P. cbn [t3a t3c fst snd] in P. exact P.
      + intros ->. destruct Hblk' as [[_ ->]|(Hb0 & _)]; [reflexivity | lia].
  Qed.

  Definition pm_idesc_operands := pm_leafA (MI:=MI) (ST:=ST) _ _ _ (cu_idesc_operands _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
  Definition pm_odesc_operands := pm_leafA (MI:=MI) (ST:=ST) _ _ _ (cu_odesc_operands _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
  Definition pm_edesc_operands := pm_leafA (MI:=MI) (ST:=ST) _ _ _ (cu_edesc_operands _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).

  #[local] Notation HCL := (cu_classes _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
  #[local] Notation pmx_room2S := (pmx_room2 SEGS Ly.L MI ST (proj1 HCL) (proj1 (proj2 HCL)) (proj2 (proj2 HCL)) (cu_RB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL)).

  Definition V3MAX : Z := 2 ^ 23.

  Lemma pm_push_types : forall (w : pmw MI ST) c0 K (fx : FPState) A M model c R (pspan p ret : Z) (l : list Z),
    PMS w c0 K -> PMX w A M model c -> c_tr c = [] -> pm_bud (w_n w) c ->
    cregs w R ret -> getr R 10%bv = Z_to_bv 64 pspan -> getr R 11%bv = Z_to_bv 64 (w_p w + O_V3) ->
    fld SEGS M pspan 8 p -> fld SEGS M (pspan + 8) 8 (Zlen l) -> ro_span SEGS Ly.L p l -> p mod 4 = 0 -> Zlen l <= g_maxlen G ->
    Forall (fun t => 0 <= t < 2 ^ 31) l ->
    w_sp w <= pspan -> pspan + 16 <= w_sp0 w - 104 ->
    Zlen (t3b (c_v3 c)) + Zlen l <= V3MAX ->
    (forall A' R' M' model' (b' cap' : Z),
        PMX w A' M' model' (set_v3 c (b', push_types l (t3b (c_v3 c)), cap')) -> pm_bud (w_n w) (set_v3 c (b', push_types l (t3b (c_v3 c)), cap')) ->
        kept R R' -> CRep.agree_on (fun a => w_sp w <= a < w_sp0 w) M M' ->
        srealizes SEGS (cfg fx R' ret M' model') K) ->
    srealizes SEGS (cfg fx R (tc_push_types tcU1) M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx A M model c R pspan p ret l PS X Htr BUD CR Ha0 Ha1 Fp Fl RS Hp4 Hll Hrange Hs1 Hs2 Hmax CONT.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ai X) as AI.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & [Gc2 Gcal] & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof (cu_mstack _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL) as HMS.
    pose proof (cu_tc_stacks _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL) as (_ & _ & HPS).
    pose proof (x_caps X) as (_ & _ & HNMAX). unfold LIB_NMAX in HNMAX.
    pose proof BUD as BUD'. destruct BUD' as (_ & _ & _ & _ & _ & _ & Bv3 & _).
    destruct (c_v3 c) as [[b xs] cap] eqn:Ev3. cbn [t3a t3b t3c fst snd] in *.
    pose proof (x_v3 X) as V. rewrite Ev3 in V. cbn [t3a t3b t3c fst snd] in V.
    pose proof V as V0. destruct V0 as (_ & _ & _ & Hlen & Hblk & _).
    assert (Hl0 : 0 <= Zlen l) by (unfold Zlen; lia).
    eapply ((cu_push_types _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL) fx A (w_s w) R M model (w_sp w) ret pspan (w_p w + O_V3) b cap p xs l K).
    - eapply pmx_cregs_callB; [exact X | exact CR | cbn [vc_stack ku_oty_pbs ccU1]; unfold NEW_STACK, PM_FRAME; lia].
    - exact (x_roc X).
    - exact Ha0. - exact Ha1. - exact Fp. - exact Fl. - exact RS. - exact Hp4. - exact Hll. - exact Hrange.
    - lia. - lia.
    - intros a Ha. cbn [vc_stack ku_oty_pbs ccU1]. unfold zwin, NEW_STACK in *. lia.
    - exact V.
    - split; [left; unfold O_V3; lia | intros a Ha; cbn [vc_stack ku_oty_pbs ccU1]; unfold zwin, O_V3, NEW_STACK in *; lia].
    - apply mod16_8; [exact Gp16 | reflexivity].
    - intros a Ha. unfold zwin, O_V3 in *. lia.
    - unfold TablStmts.caps_bound, vgrow, V3MAX in *. lia.
    - intros cc Hc1 Hc2 Hc3. rewrite <- (Nat2Z.id (length l)) in Hc3. change (Z.of_nat (length l)) with (Zlen l) in Hc3.
      eapply pmx_room2S; [exact X | exact BUD | exact (ps_budS _ _ _ PS) | exact (ps_budN _ _ _ PS) | exact (ps_budB _ _ _ PS) | | |];
        unfold vgrow, V3MAX in *; lia.
    - intros A' R' M' model' b' cap' RB V' PP EF. destruct RB as [AI' MS' FS' FDS' SX' KEPT].
      pose proof V' as V1. destruct V1 as (_ & _ & _ & Hlen' & Hblk' & _).
      assert (X' : PMX w A' M' model' (set_v3 c (b', push_types l xs, cap'))).
      { eapply (pmx_v3_pushes w A M model c A' M' model' _ _ _ b cap b' cap' xs); [exact X | exact Ev3 | exact AI' | exact MS' | exact FS' | exact FDS' | exact EF
          | cbn [vc_stack ku_oty_pbs ccU1]; unfold NEW_STACK, PM_FRAME; lia | exact V' | exact PP]. }
      assert (HC' : 4 * cap' <= 2 ^ 26) by (destruct PP as (Hcc & _); unfold V3MAX in *; lia).
      eapply CONT; [exact X' | | exact KEPT |].
      + destruct BUD as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9). unfold pm_bud. cbn [set_v3 c_m1 c_m2 c_m3 c_v1 c_v2 c_v3 c_tr t3a t3b t3c fst snd].
        repeat (split; [assumption|]). split; [| split; assumption]. destruct PP as (Hle & _). lia.
      + eapply (pmx_frame_keep SEGS Ly.L MI ST ly_img_low ly_rw_img ly_errno_img); [exact X | exact EF | cbn [vc_stack ku_oty_pbs ccU1]; unfold NEW_STACK; lia |].
        intros a Ha. split; [exact Ha|]. unfold TablStmts.pushes_fp, TablStmts.junk. unfold zwin, O_V3, w_sp0, PM_FRAME in *. intros [Hh|[[Hb Hh]|[Hh|Hj]]]; [lia | | |].
        * destruct Hblk as [[-> _]|(_ & _ & _ & _ & Hl & _)]; [lia|]. destruct (ai_live_block MI A M model _ _ AI Hl) as (_ & _ & _ & Hc' & _). lia.
        * destruct Hblk' as [[-> ->]|(_ & _ & _ & _ & Hl & _)]; [lia|]. destruct (ai_live_block MI A' M' model' _ _ AI' Hl) as (_ & _ & _ & Hc' & _). lia.
        * destruct Hj as (Hj & _). lia.
  Qed.

  Lemma pm_take_first : forall (w : pmw MI ST) c0 K (fx : FPState) A M model c R (ret : Z),
    PMS w c0 K -> PMX w A M model c -> c_tr c = [] -> pm_bud (w_n w) c ->
    cregs w R ret -> getr R 10%bv = Z_to_bv 64 (w_p w + O_V3) ->
    t3b (c_v3 c) <> [] -> Forall (fun t => 0 <= t < 2 ^ 31) (t3b (c_v3 c)) ->
    Zlen (t3b (c_v3 c)) + 2 <= V3MAX ->
    (forall A' R' M' model' (b' cap' : Z),
        PMX w A' M' model' (set_v3 c (b', snd (take_first (t3b (c_v3 c))), cap')) -> pm_bud (w_n w) (set_v3 c (b', snd (take_first (t3b (c_v3 c))), cap')) ->
        kept R R' -> getr R' 10%bv = Z_to_bv 64 (fst (take_first (t3b (c_v3 c)))) ->
        CRep.agree_on (fun a => w_sp w <= a < w_sp0 w) M M' ->
        srealizes SEGS (cfg fx R' ret M' model') K) ->
    srealizes SEGS (cfg fx R (tc_take_first tcU1) M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx A M model c R ret PS X Htr BUD CR Ha0 Hne Hrange Hmax CONT.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ai X) as AI.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & [Gc2 Gcal] & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof (cu_mstack _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL) as HMS.
    pose proof (cu_tc_stacks _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL) as (_ & _ & HPS).
    pose proof (x_caps X) as (_ & _ & HNMAX). unfold LIB_NMAX in HNMAX.
    pose proof BUD as BUD'. destruct BUD' as (_ & _ & _ & _ & _ & _ & Bv3 & _).
    destruct (c_v3 c) as [[b xs] cap] eqn:Ev3. cbn [t3a t3b t3c fst snd] in *.
    pose proof (x_v3 X) as V. rewrite Ev3 in V. cbn [t3a t3b t3c fst snd] in V.
    pose proof V as V0. destruct V0 as (_ & _ & _ & Hlen & Hblk & _).
    assert (Hl1 : 1 <= Zlen xs) by (destruct xs; [exfalso; exact (Hne eq_refl) | unfold Zlen; cbn [length]; lia]).
    eapply ((cu_take_first _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL) fx A (w_s w) R M model (w_sp w) ret (w_p w + O_V3) b cap xs K).
    - eapply pmx_cregs_callB; [exact X | exact CR | cbn [vc_stack ku_oty_pbs ccU1]; unfold NEW_STACK, PM_FRAME; lia].
    - exact Ha0. - exact V. - exact Hne.
    - split; [left; unfold O_V3; lia | intros a Ha; cbn [vc_stack ku_oty_pbs ccU1]; unfold zwin, O_V3, NEW_STACK in *; lia].
    - apply mod16_8; [exact Gp16 | reflexivity].
    - exact Hrange.
    - unfold TablStmts.caps_bound, vgrow, V3MAX in *. lia.
    - intros cc Hc1 Hc2 Hc3. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hc3.
      eapply pmx_room2S; [exact X | exact BUD | exact (ps_budS _ _ _ PS) | exact (ps_budN _ _ _ PS) | exact (ps_budB _ _ _ PS) | | |];
        unfold vgrow, V3MAX in *; lia.
    - intros A' R' M' model' b' cap' RB Hres V' PP EF. destruct RB as [AI' MS' FS' FDS' SX' KEPT].
      pose proof V' as V1. destruct V1 as (_ & _ & _ & Hlen' & Hblk' & _).
      assert (X' : PMX w A' M' model' (set_v3 c (b', snd (take_first xs), cap'))).
      { eapply (pmx_v3_pushes w A M model c A' M' model' _ _ _ b cap b' cap' xs); [exact X | exact Ev3 | exact AI' | exact MS' | exact FS' | exact FDS' | exact EF
          | cbn [vc_stack ku_oty_pbs ccU1]; unfold NEW_STACK, PM_FRAME; lia | exact V' | exact PP]. }
      assert (HC' : 4 * cap' <= 2 ^ 26) by (destruct PP as (Hcc & _); unfold V3MAX in *; lia).
      eapply CONT; [exact X' | | exact KEPT | exact Hres |].
      + destruct BUD as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9). unfold pm_bud. cbn [set_v3 c_m1 c_m2 c_m3 c_v1 c_v2 c_v3 c_tr t3a t3b t3c fst snd].
        repeat (split; [assumption|]). split; [| split; assumption]. destruct PP as (Hle & _). lia.
      + eapply (pmx_frame_keep SEGS Ly.L MI ST ly_img_low ly_rw_img ly_errno_img); [exact X | exact EF | cbn [vc_stack ku_oty_pbs ccU1]; unfold NEW_STACK; lia |].
        intros a Ha. split; [exact Ha|]. unfold TablStmts.pushes_fp, TablStmts.junk. unfold zwin, O_V3, w_sp0, PM_FRAME in *. intros [Hh|[[Hb Hh]|[Hh|Hj]]]; [lia | | |].
        * destruct Hblk as [[-> _]|(_ & _ & _ & _ & Hl & _)]; [lia|]. destruct (ai_live_block MI A M model _ _ AI Hl) as (_ & _ & _ & Hc' & _). lia.
        * destruct Hblk' as [[-> ->]|(_ & _ & _ & _ & Hl & _)]; [lia|]. destruct (ai_live_block MI A' M' model' _ _ AI' Hl) as (_ & _ & _ & Hc' & _). lia.
        * destruct Hj as (Hj & _). lia.
  Qed.
End PM.
