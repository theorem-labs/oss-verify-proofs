(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.yajl_ruby.json_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import PropExec CatExec ShapeAlg ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.XQ Require Import
  StoreOk AgentLib AsanAcct BackingAlgebra AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanInit AsanNodesMmLib.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.AS5 Require Import AsanPlanImages5 HS2Asan A_MainFacts A_ImgZero5 A_MainCells5 A_MainInit5 A_MainBridge5.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require RunCeiling MState Mem Cells Step InitMem Arr.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require AImages AImageFacts.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Malloc_ifaceP.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require AsanConsts AsanSizeClass AsanState AsanLayout AsanRep AsanRepInit AsanDepot AsanBudget.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.
(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Notation SOFF := 0x7fff8000.

Lemma u8_u64 : forall m A ws, Arr.u8arr AImages.asegs m A (Arr.u64s ws) -> Arr.u64arr AImages.asegs m A ws.
Proof. intros m A ws [B W]. split; [exact B|]. rewrite Arr.u64s_length in W. replace (8 * Z.of_nat (length ws)) with (Z.of_nat (8 * length ws)) by lia. exact W. Qed.
Lemma u8_u32 : forall m A ws, Arr.u8arr AImages.asegs m A (Arr.u32s ws) -> Arr.u32arr AImages.asegs m A ws.
Proof. intros m A ws [B W]. split; [exact B|]. rewrite Arr.u32s_length in W. replace (4 * Z.of_nat (length ws)) with (Z.of_nat (4 * length ws)) by lia. exact W. Qed.

(* [comment removed for export] *)
Lemma u64s_zeros : forall n, Arr.u64s (map AsanRep.zw (repeat 0 n)) = repeat (Z_to_bv 8 0) (8 * n)%nat.
Proof. induction n as [|n IH]; [reflexivity|]. cbn [repeat map Arr.u64s]. rewrite IH. replace (8 * Datatypes.S n)%nat with (8 + 8 * n)%nat by lia. rewrite repeat_app. reflexivity. Qed.
Lemma u32s_zeros : forall n, Arr.u32s (repeat (AsanRep.zw 0) n) = repeat (Z_to_bv 8 0) (4 * n)%nat.
Proof. induction n as [|n IH]; [reflexivity|]. cbn [repeat Arr.u32s]. rewrite IH. replace (4 * Datatypes.S n)%nat with (4 + 4 * n)%nat by lia. rewrite repeat_app. reflexivity. Qed.

(* [comment removed for export] *)
Lemma zero_sub : forall m A N i n, Mem.bytes_at AImages.asegs m A (repeat (Z_to_bv 8 0) N) -> Mem.wr_at AImages.asegs m A (Z.of_nat N) ->
  (i + n <= N)%nat ->
  Mem.bytes_at AImages.asegs m (A + Z.of_nat i) (repeat (Z_to_bv 8 0) n) /\ Mem.wr_at AImages.asegs m (A + Z.of_nat i) (Z.of_nat n).
Proof.
  intros m A N i n (B1 & B2 & B3) (W1 & W2 & W3) Hle. rewrite repeat_length in B2, B3. split.
  - split; [lia|]. split; [rewrite repeat_length; lia|]. intros j Hj. rewrite repeat_length in Hj.
    replace (A + Z.of_nat i + Z.of_nat j) with (A + Z.of_nat (i + j)) by lia. rewrite (B3 (i + j)%nat) by lia.
    rewrite !nth_error_repeat by lia. reflexivity.
  - split; [lia|]. split; [lia|]. intros j Hj. replace (A + Z.of_nat i + j) with (A + (Z.of_nat i + j)) by lia. apply W3. lia.
Qed.

(* [comment removed for export] *)
Lemma rw_cells_zero : forall m A cs, Cells.cells_wf cs -> Cells.cells_bytes cs = repeat (Z_to_bv 8 0) (Cells.cells_size cs) ->
  Mem.bytes_at AImages.asegs m A (repeat (Z_to_bv 8 0) (Cells.cells_size cs)) -> Mem.wr_at AImages.asegs m A (Z.of_nat (Cells.cells_size cs)) ->
  Step.rw_cells AImages.asegs m A cs.
Proof. intros m A cs WF E B W. split; [split; [exact WF | rewrite E; exact B] | exact W]. Qed.

Section MainRep.
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variable brk0 : word.
  Variable hw : word.
  Variable argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variable uid : word.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Variable E : env.
  Variable R : bvmap 5 word.
  Variable FULL : word -> option byte.
  Variable model : Model.
  Variable hs : acs.
  Hypothesis Hhs : HS_MAIN hs.
  Hypothesis HC : cs_ok ASEGS ASAN5 AsanInit.LIMIT (SINV0 APH sp rdraw brk0 argv envp uid hw) (argH0 APH sp rdraw argv envp uid hw) fs E hs R FULL model.

  #[local] Notation E0m := (aenv_of hs E).
  #[local] Notation CXRW := (cxs_rw sp rdraw brk0 hw argv envp fs uid Hsp Hva E R FULL model hs Hhs HC).
  #[local] Notation CXU8 := (cxs_u8_1 sp rdraw brk0 hw argv envp fs uid Hsp Hva E R FULL model hs Hhs HC).
  #[local] Notation CXZERO := (cxs_zero sp rdraw brk0 hw argv envp fs uid Hsp Hva E R FULL model hs Hhs HC).
  #[local] Notation CXS := (cxs_sound sp rdraw brk0 hw argv envp fs uid Hsp Hva E R FULL model hs Hhs HC).
  #[local] Notation PG := (pgv_range sp rdraw brk0 hw argv envp fs uid E R FULL model hs Hhs HC).
  #[local] Notation FACT := (A_MainFacts.fact_sound sp rdraw brk0 hw argv envp fs uid E R FULL model hs Hhs HC).
  #[local] Notation MR := (Mr ASAN5 (argH0 APH sp rdraw argv envp uid hw) E hs model FULL).
  Let usp := bv_unsigned sp.

  Lemma R226' : 4096 * 4295491576 <= pgv E 226 <= 4096 * 34326181871. Proof. exact (R226 sp rdraw brk0 hw argv envp fs uid E R FULL model hs Hhs HC). Qed.
  Lemma R227' : 4096 * 0 <= pgv E 227 <= 4096 * 15.                   Proof. exact (R227 sp rdraw brk0 hw argv envp fs uid E R FULL model hs Hhs HC). Qed.
  Lemma R245' : 4096 * 1 <= pgv E 245 <= 4096 * 34359736319.          Proof. exact (R245 sp rdraw brk0 hw argv envp fs uid E R FULL model hs Hhs HC). Qed.
  Lemma R244' : 4096 * 1539 <= pgv E 244 <= 4096 * 34359734272.       Proof. exact (R244 sp rdraw brk0 hw argv envp fs uid E R FULL model hs Hhs HC). Qed.
  Lemma R514' : 4096 * 1539 <= pgv E 514 <= 4096 * 34359736064.       Proof. exact (R514 sp rdraw brk0 hw argv envp fs uid E R FULL model hs Hhs HC). Qed.
  Lemma R515' : 4096 * 1539 <= pgv E 515 <= 4096 * 34359734272.       Proof. exact (R515 sp rdraw brk0 hw argv envp fs uid E R FULL model hs Hhs HC). Qed.

  (* [comment removed for export] *)
  Lemma u_sb : uE E e_sb = pgv E 226 - pgv E 227 + 65536.
  Proof.
    pose proof R226' as R226. pose proof R227' as R227.
    unfold uE, e_sb. cbn [edenot]. rewrite !u_add64, !u_mul64, !u64_lit by lia.
    replace (bv_unsigned (Z_to_bv 64 (-4096))) with (2 ^ 64 - 4096) by (vm_compute; reflexivity).
    unfold pgv in *. pose proof (u64_range (ev E 226%nat)) as Ra. pose proof (u64_range (ev E 227%nat)) as Rb.
    set (u1 := bv_unsigned (ev E 226%nat)) in *. set (u2 := bv_unsigned (ev E 227%nat)) in *.
    rewrite <- (Z.add_mod (4096 * u1) ((2 ^ 64 - 4096) * u2) (2 ^ 64)) by lia.
    replace (4096 * u1 + (2 ^ 64 - 4096) * u2) with ((4096 * u1 - 4096 * u2) + u2 * 2 ^ 64) by lia.
    assert (M0 : 2 ^ 64 <> 0) by (cbv; discriminate).
    rewrite (Z.mod_add _ _ _ M0). rewrite (Z.mod_small (4096 * u1 - 4096 * u2) (2 ^ 64) ltac:(lia)).
    rewrite u64_lit by lia. apply Z.mod_small. lia.
  Qed.

  Lemma u_rib' : uE E e_rib = pgv E 226 - pgv E 227.
  Proof. exact (u_rib sp rdraw brk0 hw argv envp fs uid E R FULL model hs Hhs HC). Qed.

  Lemma u_ri : uE E e_ri = pgv E 226 - pgv E 227 + 137439019008.
  Proof.
    pose proof R226' as R226. pose proof R227' as R227. pose proof u_rib' as U.
    unfold uE, e_ri in *. cbn [edenot]. rewrite u_add64, U, u64_lit by lia. apply Z.mod_small. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma u_sp0_sum : bv_unsigned (edenot E e_sp0) = 32768 * bv_unsigned (ev E 0%nat) + 16 * bv_unsigned (ev E 6%nat) + 4096 * bv_unsigned (ev E 10%nat)
    /\ 4294901760 <= bv_unsigned (ev E 0%nat) <= 4294967295 /\ 0 <= bv_unsigned (ev E 6%nat) <= 255 /\ 0 <= bv_unsigned (ev E 10%nat) <= 7.
  Proof.
    pose proof (FACT (KRange (EVar 0) 4294901760 4294967295) ltac:(vm_compute; reflexivity)) as R0.
    pose proof (FACT (KRange (EVar 6) 0 255) ltac:(vm_compute; reflexivity)) as R6.
    pose proof (FACT (KRange (EVar 10) 0 7) ltac:(vm_compute; reflexivity)) as R10.
    cbn [kentry_ok edenot] in R0, R6, R10.
    split; [| lia].
    unfold e_sp0, eadd, escale. rewrite !mkAlu_denot, !mkMd_denot. cbn [edenot].
    change (ev E V_S1) with (ev E 0%nat). change (ev E V_S2) with (ev E 6%nat). change (ev E V_PG) with (ev E 10%nat).
    rewrite !u_add64, !u_mul64, (u64_lit 32768), (u64_lit 16), (u64_lit 4096) by lia.
    rewrite (Z.mod_small (32768 * _)), (Z.mod_small (16 * _)), (Z.mod_small (4096 * _)) by lia.
    rewrite (Z.mod_small (32768 * _ + _)) by lia. rewrite Z.mod_small by lia. lia.
  Qed.

  Lemma u_stop : uE E e_stop = AsanSizeClass.round_up (AsanState.ae_sp0 E0m - AsanConsts.kStackAnchorDelta) AsanSizeClass.kPageSize
    /\ 0x7fff80000000 <= uE E e_stop <= 2 ^ 47.
  Proof.
    pose proof u_sp0_sum as (USP & R0 & R6 & R10).
    pose proof (FACT (KRange (EVar 374) 0 1) ltac:(vm_compute; reflexivity)) as R374.
    pose proof (FACT (KRange (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 16) (EVar 6)) (EMd Instr.M_MUL (ELit (-4096)) (EVar 374))) (ELit 3935)) 0 4095)
                  ltac:(vm_compute; reflexivity)) as RD.
    cbn [kentry_ok edenot] in R374, RD.
    set (v0 := bv_unsigned (ev E 0%nat)) in *. set (v6 := bv_unsigned (ev E 6%nat)) in *. set (v10 := bv_unsigned (ev E 10%nat)) in *. set (v374 := bv_unsigned (ev E 374%nat)) in *.
    rewrite !u_add64, !u_mul64 in RD. rewrite (u64_lit 16), (u64_lit 3935) in RD by lia.
    replace (bv_unsigned (Z_to_bv 64 (-4096))) with (2 ^ 64 - 4096) in RD by (vm_compute; reflexivity). fold v6 v374 in RD.
    assert (M0 : 2 ^ 64 <> 0) by (cbv; discriminate).
    assert (ED : (((16 * v6) mod 2 ^ 64 + ((2 ^ 64 - 4096) * v374) mod 2 ^ 64) mod 2 ^ 64 + 3935) mod 2 ^ 64 = (16 * v6 - 4096 * v374 + 3935) mod 2 ^ 64).
    { rewrite <- Z.add_mod by lia. rewrite Z.add_mod_idemp_l by lia.
      replace (16 * v6 + (2 ^ 64 - 4096) * v374 + 3935) with ((16 * v6 - 4096 * v374 + 3935) + v374 * 2 ^ 64) by lia. apply Z.mod_add. exact M0. }
    rewrite ED in RD. clear ED.
    assert (HD : 0 <= 16 * v6 - 4096 * v374 + 3935 <= 4095).
    { destruct (Z_lt_le_dec (16 * v6 - 4096 * v374 + 3935) 0) as [L|L].
      - exfalso. replace ((16 * v6 - 4096 * v374 + 3935) mod 2 ^ 64) with ((16 * v6 - 4096 * v374 + 3935 + 1 * 2 ^ 64) mod 2 ^ 64) in RD
          by (rewrite Z.mod_add by lia; reflexivity). rewrite Z.mod_small in RD by lia. lia.
      - rewrite Z.mod_small in RD by lia. lia. }
    assert (UST : uE E e_stop = 32768 * v0 + 4096 * v10 + 4096 * v374).
    { unfold uE, e_stop. cbn [edenot]. fold v0 v10 v374. rewrite !u_add64, !u_mul64, (u64_lit 32768), !(u64_lit 4096) by lia. fold v0 v10 v374.
      rewrite (Z.mod_small (32768 * v0)), (Z.mod_small (4096 * v10)), (Z.mod_small (4096 * v374)) by lia.
      rewrite (Z.mod_small (4096 * v10 + _)) by lia. rewrite Z.mod_small by lia. lia. }
    split; [| rewrite UST; lia].
    rewrite UST. cbn [AsanState.ae_sp0 aenv_of]. unfold AsanSizeClass.round_up, AsanConsts.kStackAnchorDelta, AsanSizeClass.kPageSize.
    rewrite USP. replace (32768 * v0 + 16 * v6 + 4096 * v10 - 160 + 4096 - 1) with ((8 * v0 + v10 + v374) * 4096 + (16 * v6 - 4096 * v374 + 3935)) by lia.
    rewrite Z.div_add_l by lia. rewrite Z.div_small by lia. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma den_sb : edenot E e_sb = AsanRep.zw (AsanState.ae_space_beg E0m).
  Proof. unfold AsanRep.zw. cbn [AsanState.ae_space_beg aenv_of]. rewrite <- (Z_to_bv_bv_unsigned 64 (edenot E e_sb)). f_equal. change (bv_unsigned (edenot E e_sb)) with (uE E e_sb). rewrite u_sb. lia. Qed.
  Lemma den_ri : edenot E e_ri = AsanRep.zw (AsanState.ae_region_info E0m).
  Proof.
    unfold AsanRep.zw, AsanState.ae_region_info. cbn [AsanState.ae_space_beg aenv_of]. rewrite <- (Z_to_bv_bv_unsigned 64 (edenot E e_ri)). f_equal.
    change (bv_unsigned (edenot E e_ri)) with (uE E e_ri). rewrite u_ri. unfold AsanSizeClass.kSpaceSize. lia.
  Qed.
  Lemma den_pg : forall v, pgv E v < 2 ^ 64 -> edenot E (pgE v) = AsanRep.zw (pgv E v).
  Proof. intros v Hv. exact (edenot_pg sp E v Hv). Qed.
  Lemma den_stop : edenot E e_stop = AsanRep.zw (AsanState.ae_stack_top E0m).
  Proof. pose proof (proj1 u_stop) as U. unfold AsanRep.zw, AsanState.ae_stack_top. unfold AsanState.ae_stack_top in U. rewrite <- U. unfold uE. symmetry. apply Z_to_bv_bv_unsigned. Qed.
  Lemma den_sbot : edenot E e_sbot = AsanRep.zw (AsanState.ae_stack_bottom E0m).
  Proof.
    pose proof (proj1 u_stop) as U. pose proof (proj2 u_stop) as RS. unfold AsanRep.zw, AsanState.ae_stack_bottom, AsanState.ae_stack_top. unfold AsanState.ae_stack_top in U. rewrite <- U. unfold AsanConsts.kStackSizeForThread.
    unfold e_sbot. cbn [edenot]. apply bv_eq. rewrite u_add64. change (bv_unsigned (edenot E e_stop)) with (uE E e_stop).
    replace (bv_unsigned (Z_to_bv 64 (-8388608))) with (2 ^ 64 - 8388608) by (vm_compute; reflexivity).
    rewrite u64_lit by lia. replace (uE E e_stop + (2 ^ 64 - 8388608)) with (uE E e_stop - 2 ^ 23 + 1 * 2 ^ 64) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia.
  Qed.
  Lemma den_anchor : edenot E e_anchor = AsanRep.zw (AsanState.ae_sp0 E0m - AsanConsts.kStackAnchorDelta).
  Proof.
    pose proof u_sp0_sum as (USP & R0 & R6 & R10).
    unfold AsanRep.zw, AsanConsts.kStackAnchorDelta. cbn [AsanState.ae_sp0 aenv_of].
    rewrite USP. unfold e_anchor. cbn [edenot]. apply bv_eq. rewrite !u_add64, !u_mul64, (u64_lit 32768), (u64_lit 16), (u64_lit 4096) by lia.
    replace (bv_unsigned (Z_to_bv 64 (-160))) with (2 ^ 64 - 160) by (vm_compute; reflexivity).
    set (a0 := bv_unsigned (ev E 0%nat)) in *. set (a6 := bv_unsigned (ev E 6%nat)) in *. set (a10 := bv_unsigned (ev E 10%nat)) in *.
    rewrite (Z.mod_small (32768 * a0)), (Z.mod_small (16 * a6)), (Z.mod_small (4096 * a10)) by lia.
    rewrite (Z.mod_small (16 * a6 + _)), (Z.mod_small (32768 * a0 + _)) by lia.
    rewrite u64_lit by lia.
    replace (32768 * a0 + (16 * a6 + 4096 * a10) + (2 ^ 64 - 160)) with (32768 * a0 + 16 * a6 + 4096 * a10 - 160 + 1 * 2 ^ 64) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma img_wr_at : forall a n, A_RW_LO <= a -> 0 <= n -> a + n <= A_IMG_HI -> Mem.wr_at AImages.asegs FULL a n.
  Proof.
    intros a n Ha Hn Hb. unfold A_RW_LO, A_IMG_HI in *. split; [lia|]. split; [lia|]. intros i Hi. apply AsanPlanImages5.asan_rw_window. unfold Mem.wa. rewrite u64_lit by lia. lia.
  Qed.

  #[local] Ltac fin X := first [ exact X
    | lazymatch goal with |- Step.rw_cells _ _ ?A _ => lazymatch type of X with Step.rw_cells _ _ ?B _ =>
        replace A with B by (lazy -[pgv Z.add Z.mul Z.sub Z.opp Z.pow]; lia); exact X end end ].
  #[local] Ltac cx be a l := let X := fresh in
    pose proof (CXRW be a l ltac:(vm_compute; reflexivity) eq_refl) as X; cbn [map cx_cell xv_den length] in X;
    rewrite ?u_abs in X; rewrite ?den_sb, ?den_ri, ?den_stop, ?den_sbot, ?den_anchor in X; rewrite ?den_pg in X by lia;
    try match goal with U : uE E (pgE 245) = _ |- _ => rewrite U in X end; fin X.


  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma fact_sound1 : forall K, existsb (kentry_eqb K) (kn hs) = true -> kentry_ok ASEGS E MR K.
  Proof.
    intros K HK. apply existsb_exists' in HK as (K' & Hin & Heq). apply kentry_eqb_eq in Heq. subst K'.
    exact (proj1 (Forall_forall _ _) (co_know _ _ _ _ _ _ _ _ _ _ _ HC) K Hin).
  Qed.

  Lemma vis_val : a_vis hs = VIS.
  Proof. rewrite (hs_vis sp rdraw brk0 hw argv envp fs uid E R FULL model hs Hhs HC). vm_compute. reflexivity. Qed.
  Lemma ghost_val : (a_ghost hs = G0 /\ existsb (kentry_eqb (KRange (EVar 5) 1539 524277)) (kn hs) = true) \/ a_ghost hs = G1.
  Proof. pose proof Hhs as [-> | [-> | [-> | ->]]]; [left|left|right|right]; vm_compute; repeat split; reflexivity. Qed.

  Lemma R532' : 4096 * 1 <= pgv E 532 <= 4096 * 34359736319.   Proof. exact (R532 sp rdraw brk0 hw argv envp fs uid E R FULL model hs Hhs HC). Qed.
  Lemma R438' : 4096 * 1539 <= pgv E 438 <= 4096 * 34359733495. Proof. exact (R438 sp rdraw brk0 hw argv envp fs uid E R FULL model hs Hhs HC). Qed.
  Lemma R340' : 4096 * 1 <= pgv E 340 <= 4096 * 34359736319.   Proof. exact (R340 sp rdraw brk0 hw argv envp fs uid E R FULL model hs Hhs HC). Qed.
  Lemma R275' : 4096 * 1 <= pgv E 275 <= 4096 * 34359736319.   Proof. exact (R275 sp rdraw brk0 hw argv envp fs uid E R FULL model hs Hhs HC). Qed.
  Lemma R246' : 4096 * 1539 <= pgv E 246 <= 4096 * 34359736304. Proof. exact (R246 sp rdraw brk0 hw argv envp fs uid E R FULL model hs Hhs HC). Qed.
  Lemma R225' : 4096 * 1539 <= pgv E 225 <= 4096 * 34359735410. Proof. exact (R225 sp rdraw brk0 hw argv envp fs uid E R FULL model hs Hhs HC). Qed.
  Lemma R95' : 4096 * 1539 <= pgv E 95 <= 4096 * 34359736304.   Proof. exact (R95 sp rdraw brk0 hw argv envp fs uid E R FULL model hs Hhs HC). Qed.
  Lemma R341 : 4096 * 1 <= pgv E 341 <= 4096 * 34359736319.    Proof. apply PG. vm_compute. reflexivity. Qed.
  Lemma R455 : 4096 * 1 <= pgv E 455 <= 4096 * 34359736319.    Proof. apply PG. vm_compute. reflexivity. Qed.
  Lemma R456 : 4096 * 1 <= pgv E 456 <= 4096 * 34359736319.    Proof. apply PG. vm_compute. reflexivity. Qed.
  Lemma R457 : 4096 * 1 <= pgv E 457 <= 4096 * 34359736319.    Proof. apply PG. vm_compute. reflexivity. Qed.

  #[local] Notation ZONE v l := (pg_apart_zone sp rdraw brk0 hw argv envp fs uid E R FULL model hs Hhs HC v l ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)).
  Lemma Z532 : pgv E 532 + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= pgv E 532.       Proof. pose proof R532'. exact (ZONE 532%nat 4096). Qed.
  Lemma Z275 : pgv E 275 + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= pgv E 275.       Proof. pose proof R275'. exact (ZONE 275%nat 4096). Qed.
  Lemma Z225 : pgv E 225 + 3727360 <= 0x7fff7000 \/ 0x10007fff8000 <= pgv E 225.    Proof. pose proof R225'. exact (ZONE 225%nat 3727360). Qed.
  Lemma Z95 : pgv E 95 + 65536 <= 0x7fff7000 \/ 0x10007fff8000 <= pgv E 95.         Proof. pose proof R95'. exact (ZONE 95%nat 65536). Qed.
  Lemma Z341 : pgv E 341 + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= pgv E 341.       Proof. pose proof R341. exact (ZONE 341%nat 4096). Qed.
  Lemma Z455 : pgv E 455 + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= pgv E 455.       Proof. pose proof R455. exact (ZONE 455%nat 4096). Qed.
  Lemma Z456 : pgv E 456 + 8192 <= 0x7fff7000 \/ 0x10007fff8000 <= pgv E 456.       Proof. pose proof R456. exact (ZONE 456%nat 8192). Qed.
  Lemma Z457 : pgv E 457 + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= pgv E 457.       Proof. pose proof R457. exact (ZONE 457%nat 4096). Qed.
  #[local] Notation ZONE' X := (X sp rdraw brk0 hw argv envp fs uid E R FULL model hs Hhs HC).

  (* [comment removed for export] *)
  Let pusp := usp - usp mod 4096.
  Lemma pusp_sum : pusp = 32768 * bv_unsigned (ev E 0%nat) + 4096 * bv_unsigned (ev E 10%nat) /\ 0x7fff80000000 <= pusp /\ pusp + 4096 <= 2 ^ 47.
  Proof.
    pose proof u_sp0_sum as (USP & R0 & R6 & R10). pose proof (uE_sp0 sp rdraw brk0 hw argv envp fs uid Hsp Hva Hve Hfit E R FULL model hs HC) as U.
    unfold uE in U. rewrite U in USP. pose proof (usp_lo sp Hsp). pose proof (usp_hi APH sp rdraw argv envp uid hw Hva Hve Hfit). subst pusp usp. split; [| dlia].
    rewrite USP. replace (32768 * bv_unsigned (ev E 0%nat) + 16 * bv_unsigned (ev E 6%nat) + 4096 * bv_unsigned (ev E 10%nat))
      with (16 * bv_unsigned (ev E 6%nat) + (8 * bv_unsigned (ev E 0%nat) + bv_unsigned (ev E 10%nat)) * 4096) by lia.
    rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
  Qed.

  Lemma u_stk : uE E e_stk = pusp - 8388608.
  Proof.
    pose proof pusp_sum as (P & PL & PH). pose proof u_sp0_sum as (_ & R0 & _ & R10).
    set (z0 := bv_unsigned (ev E 0%nat)) in *. set (z10 := bv_unsigned (ev E 10%nat)) in *.
    unfold uE, e_stk. cbn [edenot]. rewrite !u_add64, !u_mul64, (u64_lit 32768), (u64_lit 4096) by lia. fold z0 z10.
    replace (bv_unsigned (Z_to_bv 64 (-8388608))) with (2 ^ 64 - 8388608) by (vm_compute; reflexivity).
    rewrite (Z.mod_small (32768 * z0)), (Z.mod_small (4096 * z10)), (Z.mod_small (32768 * z0 + _)) by lia.
    replace (32768 * z0 + 4096 * z10 + (2 ^ 64 - 8388608)) with ((32768 * z0 + 4096 * z10 - 8388608) + 1 * 2 ^ 64) by lia.
    rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
  Qed.
  Lemma u_stklen : uE E e_stklen = 2 ^ 47 + 8388608 - pusp.
  Proof.
    pose proof pusp_sum as (P & PL & PH). pose proof u_sp0_sum as (_ & R0 & _ & R10).
    set (z0 := bv_unsigned (ev E 0%nat)) in *. set (z10 := bv_unsigned (ev E 10%nat)) in *.
    unfold uE, e_stklen. cbn [edenot]. rewrite !u_add64, !u_mul64 by lia. fold z0 z10.
    replace (bv_unsigned (Z_to_bv 64 (-32768))) with (2 ^ 64 - 32768) by (vm_compute; reflexivity).
    replace (bv_unsigned (Z_to_bv 64 (-4096))) with (2 ^ 64 - 4096) by (vm_compute; reflexivity).
    rewrite (u64_lit 140737496743936) by lia.
    rewrite <- (Z.add_mod ((2 ^ 64 - 32768) * z0) ((2 ^ 64 - 4096) * z10) (2 ^ 64)) by lia.
    rewrite (Z.add_mod_idemp_l) by lia.
    replace ((2 ^ 64 - 32768) * z0 + (2 ^ 64 - 4096) * z10 + 140737496743936) with ((140737496743936 - 32768 * z0 - 4096 * z10) + (z0 + z10) * 2 ^ 64) by lia.
    rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
  Qed.
  Lemma u_stksh : estart E (SA e_stksh 2146402304) = SOFF + (pusp - 8388608) / 8.
  Proof.
    pose proof pusp_sum as (P & PL & PH). pose proof u_sp0_sum as (_ & R0 & _ & R10).
    set (z0 := bv_unsigned (ev E 0%nat)) in *. set (z10 := bv_unsigned (ev E 10%nat)) in *.
    unfold estart. cbn [a_base a_off edenot e_stksh]. rewrite !u_add64, !u_mul64, (u64_lit 4096), (u64_lit 512) by lia. fold z0 z10.
    rewrite (Z.mod_small (4096 * z0)), (Z.mod_small (512 * z10)), Z.mod_small by lia. rewrite P. dlia.
  Qed.
  Lemma u_stkshlen : uE E e_stkshlen = 2 ^ 44 + 1048576 - pusp / 8.
  Proof.
    pose proof pusp_sum as (P & PL & PH). pose proof u_sp0_sum as (_ & R0 & _ & R10).
    set (z0 := bv_unsigned (ev E 0%nat)) in *. set (z10 := bv_unsigned (ev E 10%nat)) in *.
    unfold uE, e_stkshlen. cbn [edenot]. rewrite !u_add64, !u_mul64 by lia. fold z0 z10.
    replace (bv_unsigned (Z_to_bv 64 (-4096))) with (2 ^ 64 - 4096) by (vm_compute; reflexivity).
    replace (bv_unsigned (Z_to_bv 64 (-512))) with (2 ^ 64 - 512) by (vm_compute; reflexivity).
    rewrite (u64_lit 17592187092992) by lia.
    rewrite <- (Z.add_mod ((2 ^ 64 - 4096) * z0) ((2 ^ 64 - 512) * z10) (2 ^ 64)) by lia.
    rewrite (Z.add_mod_idemp_l) by lia.
    replace ((2 ^ 64 - 4096) * z0 + (2 ^ 64 - 512) * z10 + 17592187092992) with ((17592187092992 - 4096 * z0 - 512 * z10) + (z0 + z10) * 2 ^ 64) by lia.
    rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. rewrite P. dlia.
  Qed.

  (* [comment removed for export] *)
  Lemma shadow_zero_pg : forall v l g,
    hs_fact (KZero (SA (EMd Instr.M_MUL (ELit 512) (EVar v)) 2147450880) (ELit (l / 8))) = true ->
    pgv E v < 2 ^ 47 -> l mod 8 = 0 -> 0 < l < 2 ^ 47 -> pgv E v <= 8 * g < pgv E v + l ->
    FULL (Z_to_bv 64 (SOFF + g)) = Some (Z_to_bv 8 0).
  Proof.
    intros v l g HK Hv Hl Hl2 Hg. pose proof (FACT _ HK) as [_ HZ].
    unfold estart, elenZ in HZ. cbn [a_base a_off edenot] in HZ.
    pose proof (u64_range (ev E v)) as Rv. unfold pgv in *.
    assert (Hl8 : 0 <= g - 512 * bv_unsigned (ev E v) < l / 8) by dlia.
    apply (Mr_some0 sp rdraw hw argv envp uid E FULL model hs). specialize (HZ (g - 512 * bv_unsigned (ev E v))).
    rewrite u_mul64, !u64_lit in HZ by dlia. rewrite Z.mod_small in HZ by lia.
    replace (512 * bv_unsigned (ev E v) + 2147450880 + (g - 512 * bv_unsigned (ev E v))) with (SOFF + g) in HZ by lia.
    apply HZ. exact Hl8.
  Qed.

  (* [comment removed for export] *)
  Lemma shadow_zero_stack : forall g, pusp - 8388608 <= 8 * g < 2 ^ 47 -> FULL (Z_to_bv 64 (SOFF + g)) = Some (Z_to_bv 8 0).
  Proof.
    intros g Hg. pose proof pusp_sum as (P & PL & PH).
    pose proof (FACT (KZero (SA e_stksh 2146402304) e_stkshlen) ltac:(vm_compute; reflexivity)) as [_ HZ].
    fold (elenZ E e_stkshlen) in HZ. change (elenZ E e_stkshlen) with (uE E e_stkshlen) in HZ. rewrite u_stksh, u_stkshlen in HZ.
    apply (Mr_some0 sp rdraw hw argv envp uid E FULL model hs). specialize (HZ (SOFF + g - (SOFF + (pusp - 8388608) / 8)) ltac:(dlia)).
    replace (SOFF + (pusp - 8388608) / 8 + (SOFF + g - (SOFF + (pusp - 8388608) / 8))) with (SOFF + g) in HZ by lia. exact HZ.
  Qed.

  Lemma u_pg' : forall v, pgv E v < 2 ^ 64 -> uE E (pgE v) = pgv E v.
  Proof. intros v Hv. exact (u_pg sp E v Hv). Qed.
  Lemma u_lit' : forall z, 0 <= z < 2 ^ 64 -> uE E (ELit z) = z.
  Proof. intros z Hz. unfold uE. cbn [edenot]. apply u64_lit. lia. Qed.
  Lemma u_pg_off' : forall v z, 0 <= z -> pgv E v + z < 2 ^ 64 -> uE E (EAlu Instr.ALU_ADD (pgE v) (ELit z)) = pgv E v + z.
  Proof. intros v z Hz Hv. exact (u_pg_off sp E v z Hz Hv). Qed.

  (* [comment removed for export] *)
  Lemma ghost_apart : forall x, 0x7fff8000 <= x < 0x8fff7000 \/ 0x2008fff7000 <= x < 0x10007fff8000 -> in_ghost E hs x = false.
  Proof.
    intros x Hx. pose proof R341 as R341. pose proof R455 as R455. pose proof R456 as R456. pose proof R457 as R457.
    unfold in_ghost. destruct ghost_val as [[-> H5] | ->].
    - pose proof (fact_sound1 _ H5) as R5. cbn [kentry_ok edenot] in R5. clear H5.
      assert (U5 : uE E (pgE 5) = pgv E 5) by (apply u_pg'; unfold pgv; lia).
      apply existsb_false_forall. intros p Hp. cbn in Hp.
      repeat (destruct Hp as [<- | Hp]); try contradiction; cbn [fst snd];
        rewrite ?u_pg_off' by lia; rewrite ?u_pg' by lia; rewrite ?u_lit' by lia; unfold pgv in *; rewrite ?U5; apply range_false;
        [ pose proof Z341 | pose proof Z455 | pose proof Z456 | pose proof Z457 | | pose proof Z455 | pose proof Z456 | pose proof Z457 ]; unfold pgv in *; lia.
    - apply existsb_false_forall. intros p Hp. cbn in Hp.
      repeat (destruct Hp as [<- | Hp]); try contradiction; cbn [fst snd];
        rewrite ?u_pg_off' by lia; rewrite ?u_pg' by lia; rewrite ?u_lit' by lia; apply range_false;
        [ pose proof Z341 | pose proof Z455 | pose proof Z456 | pose proof Z457 | pose proof Z455 | pose proof Z456 | pose proof Z457 ]; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma E0m_img : AsanState.ae_img E0m = A_IMG.                                  Proof. reflexivity. Qed.
  Lemma E0m_fs_beg : AsanState.ae_fs_beg E0m = pgv E 438.                        Proof. reflexivity. Qed.
  Lemma E0m_fs_len : AsanState.ae_fs_len E0m = 11571200.                         Proof. reflexivity. Qed.
  Lemma E0m_iarena : AsanState.ae_iarena E0m = pgv E 246.                        Proof. reflexivity. Qed.
  Lemma E0m_space_beg : AsanState.ae_space_beg E0m = pgv E 226 - pgv E 227 + 0x10000. Proof. reflexivity. Qed.

  Theorem init_shadow0 : forall g, AsanRep.sh_default_dom E0m (8 * g) = true -> AsanRep.sh_excluded E0m (8 * g) = false ->
    Step.rw_cells AImages.asegs FULL (AsanSizeClass.kShadowBase + g) [Cells.C1 (AsanRep.zb 0)].
  Proof.
    intros g Hdom Hex.
    change AsanSizeClass.kShadowBase with SOFF.
    (* [comment removed for export] *)
    assert (DOM : (0 <= 8 * g < 0x7fff7000 /\ ~ (0x10000 <= 8 * g < 0x603000)) \/ 0x10007fff8000 <= 8 * g <= 2 ^ 47 - 1).
    { unfold AsanRep.sh_default_dom, AsanRep.in_img in Hdom. rewrite E0m_img in Hdom. cbn [A_IMG fst snd] in Hdom.
      rewrite AsanLayout.kLowAppEnd_val, AsanSizeClass.kHighMemBeg_val in Hdom. unfold AsanSizeClass.kHighMemEnd in Hdom.
      apply orb_prop in Hdom as [H|H].
      - left. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
        apply negb_true_iff in H3. split; [lia|]. intros [X Y]. apply andb_false_iff in H3 as [H3|H3]; [apply Z.leb_gt in H3 | apply Z.ltb_ge in H3]; lia.
      - right. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia. }
    clear Hdom.
    (* [comment removed for export] *)
    unfold AsanRep.sh_excluded, AsanRep.in_fakestack, AsanRep.in_iarena, AsanRep.in_reginfo in Hex.
    rewrite E0m_fs_beg, E0m_fs_len, E0m_iarena, E0m_space_beg in Hex.
    unfold AsanRep.kIArenaLen, AsanSizeClass.kSpaceSize, AsanSizeClass.kPageSize in Hex.
    apply orb_false_iff in Hex as [Hex NRI]. apply orb_false_iff in Hex as [NFS NIA].
    assert (NI : forall lo hi, ((lo <=? 8 * g) && (8 * g <? hi))%bool = false -> ~ (lo <= 8 * g < hi)).
    { intros lo hi Hb [X Y]. apply andb_false_iff in Hb as [Hb|Hb]; [apply Z.leb_gt in Hb | apply Z.ltb_ge in Hb]; lia. }
    apply NI in NFS. apply NI in NIA. apply NI in NRI. clear NI.
    set (x := SOFF + g).
    assert (Hx : 0x7fff8000 <= x < 0x8fff7000 \/ 0x2008fff7000 <= x < 0x10007fff8000) by (subst x; lia).
    assert (Ux : bv_unsigned (Z_to_bv 64 x) = x) by (apply u64_lit; lia).
    (* [comment removed for export] *)
    enough (Z0 : FULL (Z_to_bv 64 x) = Some (Z_to_bv 8 0)).
    { split; [split; [cbn; exact (conj I I)|]|].
      - cbn [Cells.cells_bytes Cells.cbytes app]. split; [lia|]. split; [cbn; lia|].
        intros i Hi. cbn in Hi. replace i with 0%nat by lia. cbn [nth_error]. rewrite Z.add_0_r. unfold Mem.mrd, Mem.wa. fold x. rewrite Z0.
        unfold AsanRep.zb. reflexivity.
      - cbn [Cells.cells_size Cells.csize Nat.add]. split; [lia|]. split; [lia|].
        intros i Hi. replace i with 0 by lia. rewrite Z.add_0_r. unfold wview, Mem.wa. fold x. rewrite Z0. discriminate. }
    (* [comment removed for export] *)
    assert (MX : exists m, existsb (amap_eqb m) (a_maps HS_s2_00) = true /\ am_kind m = KRWLAZY /\ is_tok_kind (am_kind m) = false /\
                           bv_unsigned (edenot E (am_base m)) <= x < bv_unsigned (edenot E (am_base m)) + bv_unsigned (edenot E (am_len m))).
    { destruct Hx as [Hx1|Hx1].
      - exists (AM (ELit 2147446784) (ELit 268435456) KRWLAZY). split; [vm_compute; reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
        cbn [am_base am_len edenot]. rewrite !u64_lit by lia. lia.
      - exists (AM (ELit 2201439137792) (ELit 15392894357504) KRWLAZY). split; [vm_compute; reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
        cbn [am_base am_len edenot]. rewrite !u64_lit by lia. lia. }
    destruct MX as (m & Hm & Hkind & Htok & Hin).
    pose proof (amap_in_b sp rdraw brk0 hw argv envp fs uid E R FULL model hs Hhs HC m Hm) as Hm'.
    destruct (proj1 (Forall_forall _ _) (co_kinds _ _ _ _ _ _ _ _ _ _ _ HC) _ Hm' Hkind (Z_to_bv 64 x) ltac:(rewrite Ux; exact Hin)) as [NA LZ].
    rewrite Ux in NA.
    assert (INM : in_ivs x (vm_maps (m_vmmaps model)) = true).
    { apply AsanNodesMmLib.in_ivs_true'. exists (amap_den E m). split;
        [ exact (maps_match_In E (a_maps hs) _ m (co_maps _ _ _ _ _ _ _ _ _ _ _ HC) Hm' Htok)
        | unfold amap_den; cbn [fst snd]; exact Hin ]. }
    clear Hm Hm' Hkind Htok Hin m.
    destruct (hid ASAN5 (argH0 APH sp rdraw argv envp uid hw) E hs model (Z_to_bv 64 x)) eqn:Hh.
    - (* [comment removed for export] *)
      apply (co_zero _ _ _ _ _ _ _ _ _ _ _ HC (Z_to_bv 64 x) Hh); rewrite ?Ux; [exact INM | exact NA | exact LZ | exact (ghost_apart x Hx)].
    - (* [comment removed for export] *)
      unfold hid in Hh. apply Bool.orb_false_iff in Hh as [_ Hv]. apply Bool.negb_false_iff in Hv.
      unfold vis in Hv. rewrite Ux, LZ in Hv. cbn [negb] in Hv.
      replace (in_hull ASAN5 x) with false in Hv by (symmetry; unfold in_hull; cbn [img_lo img_hi ASAN5]; apply Bool.andb_false_iff; right; apply Z.ltb_ge; lia).
      pose proof pusp_sum as (PP & PL & PH).
      rewrite (ptop_eq sp rdraw brk0 hw argv envp fs uid Hsp Hva Hve Hfit E R FULL model hs HC) in Hv.
      replace (usp - usp mod 4096 - 8388608 <=? x) with false in Hv by (symmetry; apply Z.leb_gt; subst pusp; lia).
      cbn [orb] in Hv. rewrite INM, NA in Hv. cbn [negb andb orb] in Hv.
      pose proof R532' as R532. pose proof R515' as R515. pose proof R514' as R514. pose proof R438' as R438. pose proof R340' as R340.
      pose proof R275' as R275. pose proof R246' as R246. pose proof R245' as R245. pose proof R226' as R226. pose proof R227' as R227.
      pose proof R225' as R225. pose proof R95' as R95.
      pose proof u_ri as URI. pose proof u_stk as USTK. pose proof u_stklen as USTKL.
      unfold in_allow in Hv. apply Bool.orb_true_iff in Hv as [Hv|Hv].
      + (* [comment removed for export] *)
        exfalso. unfold in_vis in Hv. rewrite vis_val in Hv. apply existsb_exists in Hv as (p & Hp & Hb). cbn in Hp.
        repeat (destruct Hp as [<- | Hp]); try contradiction; cbn [fst snd] in Hb;
          rewrite ?URI, ?USTK, ?USTKL in Hb; rewrite ?u_pg' in Hb by lia; rewrite ?u_lit' in Hb by lia;
          apply andb_prop in Hb as [Hb1 Hb2]; apply Z.leb_le in Hb1; apply Z.ltb_lt in Hb2;
          [ pose proof Z532 | pose proof (ZONE' Z515) | pose proof (ZONE' Z514) | pose proof (ZONE' Z438) | pose proof (ZONE' Z340)
          | pose proof Z275 | pose proof (ZONE' Z246) | pose proof (ZONE' Z245) | | pose proof Z225 | pose proof Z95 | | ]; lia.
      + (* [comment removed for export] *)
        unfold in_sh in Hv. rewrite vis_val in Hv. apply existsb_exists in Hv as (p & Hp & Hb). cbn in Hp.
        unfold sh_lo, sh_hi in Hb. cbn [shadow_off ASAN5] in Hb.
        repeat (destruct Hp as [<- | Hp]); try contradiction; cbn [fst snd] in Hb;
          rewrite ?URI, ?USTK, ?USTKL in Hb; rewrite ?u_pg' in Hb by lia; rewrite ?u_lit' in Hb by lia;
          apply andb_prop in Hb as [Hb1 Hb2]; apply Z.leb_le in Hb1; apply Z.ltb_lt in Hb2; subst x.
        * apply (shadow_zero_pg 532 4096); [vm_compute; reflexivity | lia | reflexivity | lia | unfold pgv in *; dlia].
        * apply (shadow_zero_pg 515 8388608); [vm_compute; reflexivity | lia | reflexivity | lia | unfold pgv in *; dlia].
        * apply (shadow_zero_pg 514 1048576); [vm_compute; reflexivity | lia | reflexivity | lia | unfold pgv in *; dlia].
        * exfalso. apply NFS. unfold pgv in *; dlia.
        * apply (shadow_zero_pg 340 4096); [vm_compute; reflexivity | lia | reflexivity | lia | unfold pgv in *; dlia].
        * apply (shadow_zero_pg 275 4096); [vm_compute; reflexivity | lia | reflexivity | lia | unfold pgv in *; dlia].
        * exfalso. apply NIA. unfold pgv in *; dlia.
        * apply (shadow_zero_pg 245 4096); [vm_compute; reflexivity | lia | reflexivity | lia | unfold pgv in *; dlia].
        * exfalso. apply NRI. unfold pgv in *; dlia.
        * apply (shadow_zero_pg 225 3727360); [vm_compute; reflexivity | lia | reflexivity | lia | unfold pgv in *; dlia].
        * apply (shadow_zero_pg 95 65536); [vm_compute; reflexivity | lia | reflexivity | lia | unfold pgv in *; dlia].
        * exfalso. dlia.
        * apply shadow_zero_stack. rewrite PP in *. dlia.
  Qed.

  #[local] Notation INST := 0xaa518.

  Theorem init_arep0 : AsanRepInit.arep0_facts AImages.asegs E0m FULL.
  Proof.
    pose proof R244' as R244. pose proof R245' as R245. pose proof R226' as R226. pose proof R227' as R227.
    assert (UPG245 : uE E (pgE 245) = pgv E 245) by (apply (u_pg sp E); lia).
    unfold AsanRepInit.arep0_facts.
    (* [comment removed for export] *)
    split. { cx (ELit 0) (INST + 32) [CX8 (XS e_sb); CX4 0xffffffff; CX4 0; CX8 (XS e_ri); CX1 0]. }
    split. { cx (ELit 0) (INST + 64) [CX8 (XL 4096); CX8 (XS (pgE 244)); CX8 (XS (pgE 244)); CX8 (XL (2^23))]. }
    split. { cx (ELit 0) (INST + 112) [CX8 (XL 0); CX8 (XL 0); CX1 0]. }
    split. { cx (ELit 0) (INST + 136) [CX8 (XL 0); CX8 (XL 0); CX8 (XL 0); CX8 (XL 0)]. }
    split. { pose proof (CXZERO (ELit 0) (INST + 136 + 32) 512 ltac:(vm_compute; reflexivity)) as X. rewrite u_abs in X.
             apply u8_u64. rewrite u64s_zeros. exact X. }
    split. { cx (ELit 0) (INST + 680) [CX4 0]. }
    split. { cx (ELit 0) (INST + 688 + 16) [CX8 (XL 0); CX8 (XL 0)]. }
    split. { cx (ELit 0) (INST + 728 + 64) [CX8 (XL (2^28)); CX8 (XL 0xE666661); CX8 (XL (2^20))]. }
    split. { cx (ELit 0) (INST + 880) [CX4 0]. }   (* [comment removed for export] *)
    split. { cx (ELit 0) (INST + 888) [CX8 (XL 0); CX8 (XL 0); CX8 (XL 0); CX8 (XL 0)]. }
    split. { cx (ELit 0) (INST + 984) [CX1 0]. }
    split. { cx (ELit 0) (INST + 3616) [CX8 (XL (2^40)); CX2 16; CX2 2048; CX1 1]. }
    (* [comment removed for export] *)
    split. { pose proof (CXS e_rib 137439019008 [CXZ 4096] ltac:(vm_compute; reflexivity)) as [Z0 W0]. cbn [cxs_prop cx_prop cxs_len cx_len] in Z0, W0. destruct Z0 as [Z0 _].
             rewrite u_rib' in Z0, W0. rewrite Z.add_0_r in W0.
             intros c Hc. unfold AsanState.ae_region_info. cbn [AsanState.ae_space_beg aenv_of]. unfold AsanSizeClass.kSpaceSize, AsanConsts.kRegSize. unfold AsanSizeClass.kNumClasses in Hc.
             replace (pgv E 226 - pgv E 227 + 65536 + 2 ^ 37 + 128 * c) with (pgv E 226 - pgv E 227 + 137439019008 + Z.of_nat (Z.to_nat (128 * c))) by lia.
             destruct (zero_sub FULL _ 4096 (Z.to_nat (128 * c)) 128 Z0 W0 ltac:(lia)) as [B W].
             apply rw_cells_zero; [cbn; repeat split; reflexivity | vm_compute; reflexivity | exact B | exact W]. }
    (* [comment removed for export] *)
    split. { cx (pgE 245) 8 [CX8 (XS e_stop); CX8 (XS e_sbot)]. }
    split. { cx (pgE 245) 40 [CX1 0]. }
    split. { cx (pgE 245) 80 [CX8 (XL 0); CX8 (XL 0); CX8 (XL 0); CX8 (XL 0)]. }
    split. { pose proof (CXS (pgE 245) 208 [CXZ 2560] ltac:(vm_compute; reflexivity)) as [Z0 W0]. cbn [cxs_prop cx_prop cxs_len cx_len] in Z0, W0. destruct Z0 as [Z0 _].
             rewrite UPG245 in Z0, W0. rewrite Z.add_0_r in W0.
             intros c Hc. cbn [AsanState.ae_thread aenv_of]. unfold AsanConsts.kThrCache, AsanConsts.kPerClassSize. unfold AsanSizeClass.kNumClasses in Hc. split.
             - replace (pgv E 245 + 208 + 80 * c) with (pgv E 245 + 208 + Z.of_nat (Z.to_nat (80 * c))) by lia.
               destruct (zero_sub FULL _ 2560 (Z.to_nat (80 * c)) 16 Z0 W0 ltac:(lia)) as [B W].
               apply rw_cells_zero; [cbn; repeat split; reflexivity | vm_compute; reflexivity | exact B | exact W].
             - exists (repeat (AsanRep.zw 0) 16). split; [| reflexivity].
               replace (pgv E 245 + 208 + 80 * c + 16) with (pgv E 245 + 208 + Z.of_nat (Z.to_nat (80 * c + 16))) by lia.
               destruct (zero_sub FULL _ 2560 (Z.to_nat (80 * c + 16)) 64 Z0 W0 ltac:(lia)) as [B W].
               apply u8_u32. rewrite u32s_zeros. split; [exact B | rewrite repeat_length; exact W]. }
    split. { cx (pgE 245) (2768 + 16) [CX8 (XL 0); CX8 (XL 0)]. }
    split. { pose proof (CXZERO (pgE 245) 2800 112 ltac:(vm_compute; reflexivity)) as X. rewrite UPG245 in X.
             apply u8_u64. rewrite u64s_zeros. exact X. }
    split. { pose proof (CXZERO (pgE 245) (2800 + 112) 256 ltac:(vm_compute; reflexivity)) as X. rewrite UPG245 in X.
             apply u8_u64. rewrite u64s_zeros.
             replace (AsanState.ae_thread E0m + AsanConsts.kThrStats + 112) with (pgv E 245 + (2800 + 112)) by (lazy -[pgv Z.add Z.mul Z.sub Z.opp Z.pow]; lia). exact X. }
    split. { cx (pgE 245) 3168 [CX1 0]. }
    (* [comment removed for export] *)
    split. { pose proof (CXU8 (ELit 0) 0xab378 (CXB (AsanRep.asan_flags_bytes AsanConsts.asan_ic)) ltac:(vm_compute; reflexivity) eq_refl) as X. rewrite u_abs in X.
             exact X. }
    split. { cx (ELit 0) (0x13f6a8 + 34) [CX1 1]. }
    split. { cx (ELit 0) (0x13f6a8 + 120) [CX8 (XL (2^64 - 1))]. }
    split. { cx (ELit 0) (0x13f6a8 + 219) [CX1 1]. }
    split. { cx (ELit 0) 0xadb78 [CX8 (XL 0x7fff8000)]. }
    split. { cx (ELit 0) 0xae860 [CX8 (XL (2^47 - 1)); CX8 (XL 0); CX8 (XL 0)]. }
    split. { cx (ELit 0) 0xad3dc [CX1 1]. }
    split. { cx (ELit 0) 0xae858 [CX1 1]. }
    split. { cx (ELit 0) 0xae87c [CX4 30]. }
    split. { cx (ELit 0) 0x13d620 [CX8 (XL 4096)]. }
    split. { cx (ELit 0) 0x13f69c [CX4 0]. }
    split. { cx (ELit 0) 0x13d610 [CX8 (XS e_anchor)]. }
    split. { cx (ELit 0) 0xa6820 [CX8 (XL 0x9dcdc); CX8 (XL 0x9e0e0)]. }
    split. { pose proof (CXU8 (ELit 0) 0x13f640 (CXZ 80) ltac:(vm_compute; reflexivity) eq_refl) as X. rewrite u_abs in X.
             apply u8_u64. rewrite u64s_zeros. exact X. }
    split. { cx (ELit 0) 0x13d608 [CX1 0; CX1 0]. }
    split. { pose proof (CXZERO (ELit 0) (0xaed80 + 8) 0x40000 ltac:(vm_compute; reflexivity)) as X. rewrite u_abs in X.
             unfold AsanRep.zeros, AsanRep.zb.
             lazymatch goal with |- Arr.u8arr _ _ ?A _ => replace A with (0xaed80 + 8) by reflexivity end. exact X. }
    split. { change (AsanConsts.aic_internal_allocator_instance (AsanState.ae_ic E0m)) with 0xaed80. apply img_wr_at; unfold A_RW_LO, A_IMG_HI; lia. }
    (* [comment removed for export] *)
    split. { exact init_shadow0. }
    (* [comment removed for export] *)
    intros c Hc. cbn [AsanState.ae_space_beg aenv_of]. unfold AsanSizeClass.free_array, AsanSizeClass.region_beg, AsanSizeClass.kRegionSize, AsanSizeClass.kFreeArrayOffset.
    unfold AsanSizeClass.kNumClasses in Hc.
    split.
    - split; [apply Mem.bytes_at_nil; lia | split; [lia|]; split; [cbn; lia | intros i Hi; cbn in Hi; lia]].
    - split; [lia|]. split; [lia|]. intros i Hi. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[local] Notation CXRWK := (cxs_rw_k sp rdraw brk0 hw argv envp fs uid Hsp Hva E R FULL model hs HC).
  #[local] Notation CXZK := (cxs_zero_k sp rdraw brk0 hw argv envp fs uid Hsp Hva E R FULL model hs HC).
  #[local] Notation CXSK := (cxs_sound_k sp rdraw brk0 hw argv envp fs uid Hsp Hva E R FULL model hs HC).
  #[local] Notation TD := 0x18fa58.
  #[local] Notation SS := 0x17fa48.

  Lemma bucket_head_1 : forall h b, AsanDepot.bucket_head [h] b = (if AsanDepot.bucket_of h =? b then 1 else 0).
  Proof. intros h b. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma depot_case : forall (keys : list (list Z)) (fr hb : Z) (H : Z),
    keys0_of hs = keys -> frames0_of hs = fr -> map AsanSizeClass.depot_hash keys = [H] -> AsanDepot.bucket_of H = hb -> 0 <= hb < 2 ^ 20 ->
    (* [comment removed for export] *)
    (0 < hb -> cxs_okk (kn hs) (ELit 0) TD [CXZ (4 * hb)] = true) ->
    cxs_okk (kn hs) (ELit 0) (TD + 4 * hb) [CX4 1] = true ->
    (hb < 2 ^ 20 - 1 -> cxs_okk (kn hs) (ELit 0) (TD + 4 * hb + 4) [CXZ (4 * (2 ^ 20 - 1 - hb))] = true) ->
    (* [comment removed for export] *)
    cxs_okk (kn hs) (ELit 0) (TD + 0x400000) [CX4 1] = true ->
    cxs_okk (kn hs) (ELit 0) (TD + 0x400008) [CX4 0] = true ->
    cxs_okk (kn hs) (ELit 0) (TD + 0x400010) [CX8 (XS (pgE 514))] = true ->
    cxs_okk (kn hs) (ELit 0) (TD + 0x400018) [CXZ (8 * (2 ^ 15 - 1))] = true ->
    (* [comment removed for export] *)
    cxs_okk (kn hs) (pgE 514) 0 [CXZ 16; CX8 (XL H); CX4 0; CX4 1; CXZ 0xfffe0] = true ->
    (* [comment removed for export] *)
    cxs_okk (kn hs) (ELit 0) SS [CX8 (XL fr); CX8 (XL 0x800000); CX8 (XS (pgE 515)); CX4 fr; CX4 0] = true ->
    cxs_okk (kn hs) (ELit 0) (SS + 32) [CXZ (16 * 0x1000 - 16)] = true ->
    (* [comment removed for export] *)
    (exists ws, 0 < cxs_len ws /\ cxs_len ws = 2 ^ 23 /\ forallb not_any ws = true /\ cxs_okk (kn hs) (pgE 515) 0 ws = true) ->
    AsanRepInit.depot0_facts AImages.asegs E0m FULL.
  Proof.
    intros keys fr hb H EK EF EH EB Hhb T1 T2 T3 U1 UM U2 U3 N1 S1 S2 [ws (Wl & Wn & Wa & Wk)].
    pose proof R514' as R514. pose proof R515' as R515.
    assert (U514 : uE E (pgE 514) = pgv E 514) by (apply u_pg'; lia).
    assert (U515 : uE E (pgE 515) = pgv E 515) by (apply u_pg'; lia).
    unfold AsanRepInit.depot0_facts.
    change (AsanState.ae_keys0 E0m) with (keys0_of hs). change (AsanState.ae_frames0 E0m) with (frames0_of hs).
    change (AsanState.ae_depot_nodes E0m) with (pgv E 514). change (AsanState.ae_store_blk E0m) with (pgv E 515).
    change (AsanConsts.aic_theDepot (AsanState.ae_ic E0m)) with TD. change (AsanConsts.aic_stackStore (AsanState.ae_ic E0m)) with SS.
    rewrite EK, EF, EH. cbv zeta.
    (* [comment removed for export] *)
    split. { intros b Hb. unfold AsanDepot.kTabSize in Hb. rewrite bucket_head_1, EB.
             destruct (Z.eqb_spec hb b) as [<-|NE].
             - pose proof (CXRWK (ELit 0) (TD + 4 * hb) [CX4 1] ltac:(cbn; lia) T2 eq_refl) as X. cbn [map cx_cell xv_den] in X. rewrite u_abs in X. exact X.
             - destruct (Z_lt_le_dec b hb) as [L|L].
               + pose proof (CXZK (ELit 0) TD (4 * hb) ltac:(lia) (T1 ltac:(lia))) as [B W]. rewrite u_abs in B, W.
                 rewrite repeat_length in W.
                 destruct (zero_sub FULL TD (Z.to_nat (4 * hb)) (Z.to_nat (4 * b)) 4 B W ltac:(lia)) as [B4 W4].
                 rewrite Z2Nat.id in B4, W4 by lia. apply rw_cells_zero; [cbn; exact (conj I I) | reflexivity | exact B4 | exact W4].
               + pose proof (CXZK (ELit 0) (TD + 4 * hb + 4) (4 * (2 ^ 20 - 1 - hb)) ltac:(lia) (T3 ltac:(lia))) as [B W]. rewrite u_abs in B, W.
                 rewrite repeat_length in W.
                 destruct (zero_sub FULL (TD + 4 * hb + 4) (Z.to_nat (4 * (2 ^ 20 - 1 - hb))) (Z.to_nat (4 * (b - hb - 1))) 4 B W ltac:(lia)) as [B4 W4].
                 rewrite Z2Nat.id in B4, W4 by lia. replace (TD + 4 * hb + 4 + 4 * (b - hb - 1)) with (TD + 4 * b) in B4, W4 by lia.
                 apply rw_cells_zero; [cbn; exact (conj I I) | reflexivity | exact B4 | exact W4]. }
    split. { pose proof (CXRWK (ELit 0) (TD + 0x400000) [CX4 1] ltac:(cbn; lia) U1 eq_refl) as X. cbn [map cx_cell xv_den] in X. rewrite u_abs in X.
             unfold AsanOps.zlen. replace (Z.of_nat (length keys)) with 1 by (apply (f_equal (fun l => Z.of_nat (length l))) in EH; rewrite length_map in EH; cbn in EH; lia). exact X. }
    split. { pose proof (CXRWK (ELit 0) (TD + 0x400010) [CX8 (XS (pgE 514))] ltac:(cbn; lia) U2 eq_refl) as X. cbn [map cx_cell xv_den] in X. rewrite u_abs in X. rewrite den_pg in X by lia. exact X. }
    split. { pose proof (CXZK (ELit 0) (TD + 0x400018) (8 * (2 ^ 15 - 1)) ltac:(lia) U3) as [B W]. rewrite u_abs in B, W. rewrite repeat_length in W.
             intros k Hk. unfold AsanDepot.kNodesMap1 in Hk.
             destruct (zero_sub FULL (TD + 0x400018) (Z.to_nat (8 * (2 ^ 15 - 1))) (Z.to_nat (8 * (k - 1))) 8 B W ltac:(lia)) as [B8 W8].
             rewrite Z2Nat.id in B8, W8 by lia. replace (TD + 0x400018 + 8 * (k - 1)) with (TD + 0x400010 + 8 * k) in B8, W8 by lia.
             apply rw_cells_zero; [cbn; exact (conj I I) | reflexivity | exact B8 | exact W8]. }
    (* [comment removed for export] *)
    pose proof (CXSK (pgE 514) 0 [CXZ 16; CX8 (XL H); CX4 0; CX4 1; CXZ 0xfffe0] ltac:(cbn; lia) N1) as [NP NW]. rewrite U514, Z.add_0_r in NP, NW.
    cbn [cxs_prop cx_prop cxs_len cx_len xv_den] in NP, NW. destruct NP as (_ & NH & NL & NS & _).
    split. { intros i Hi. unfold AsanOps.zlen in Hi. replace (Z.of_nat (length keys)) with 1 in Hi by (apply (f_equal (fun l => Z.of_nat (length l))) in EH; rewrite length_map in EH; cbn in EH; lia).
             assert (i = 1) as -> by lia. exists (Z_to_bv 64 1).
             unfold AsanDepot.nth_hash, AsanDepot.node_link. cbn [Z.sub Z.to_nat nth firstn Pos.to_nat]. change (AsanDepot.bucket_head [] _) with 0.
             split; [split; [cbn; repeat split; exact I|]|].
             - cbn [Cells.cells_bytes Cells.cbytes]. rewrite app_nil_r.
               apply (proj2 (Mem.bytes_at_app _ _ _ _ _)). split; [exact NH|]. rewrite Mem.length_le8.
               apply (proj2 (Mem.bytes_at_app _ _ _ _ _)). split; [replace (pgv E 514 + 16 * 1 + Z.of_nat 8) with (pgv E 514 + 16 + 8) by lia; exact NL|]. rewrite Mem.length_le4.
               replace (pgv E 514 + 16 * 1 + Z.of_nat 8 + Z.of_nat 4) with (pgv E 514 + 16 + 8 + 4) by lia. exact NS.
             - cbn [Cells.cells_size Cells.csize Nat.add]. destruct NW as (W1 & W2 & W3). split; [lia|]. split; [lia|]. intros j Hj.
               replace (pgv E 514 + 16 * 1 + j) with (pgv E 514 + (16 + j)) by lia. apply W3. lia. }
    split. { unfold AsanConsts.kDepotNodeBlockBytes. replace (2 ^ 20) with (16 + (8 + (4 + (4 + (1048544 + 0))))) by reflexivity. exact NW. }
    (* [comment removed for export] *)
    pose proof (CXRWK (ELit 0) SS [CX8 (XL fr); CX8 (XL 0x800000); CX8 (XS (pgE 515)); CX4 fr; CX4 0] ltac:(cbn; lia) S1 eq_refl) as SX. cbn [map cx_cell xv_den] in SX. rewrite u_abs in SX. rewrite den_pg in SX by lia.
    assert (SX1 := proj1 (proj1 (Malloc_ifaceP.rw_cells_app _ _ _ [Cells.C8 (Z_to_bv 64 fr)] _) SX)).
    assert (SXr := proj2 (proj1 (Malloc_ifaceP.rw_cells_app _ _ _ [Cells.C8 (Z_to_bv 64 fr)] _) SX)). cbn [Cells.cells_size Cells.csize Nat.add] in SXr.
    assert (SX2 := proj1 (proj1 (Malloc_ifaceP.rw_cells_app _ _ _ [Cells.C8 (Z_to_bv 64 0x800000)] _) SXr)).
    assert (SXr2 := proj2 (proj1 (Malloc_ifaceP.rw_cells_app _ _ _ [Cells.C8 (Z_to_bv 64 0x800000)] _) SXr)). cbn [Cells.cells_size Cells.csize Nat.add] in SXr2.
    assert (SX3 := proj1 (proj1 (Malloc_ifaceP.rw_cells_app _ _ _ [Cells.C8 (AsanRep.zw (pgv E 515)); Cells.C4 (Z_to_bv 64 fr)] _) SXr2)).
    assert (SX4 := proj2 (proj1 (Malloc_ifaceP.rw_cells_app _ _ _ [Cells.C8 (AsanRep.zw (pgv E 515)); Cells.C4 (Z_to_bv 64 fr)] _) SXr2)). cbn [Cells.cells_size Cells.csize Nat.add] in SX4.
    split; [exact SX1|].
    split; [exists (Z_to_bv 64 0x800000); replace (SS + 8) with (SS + Z.of_nat 8) by lia; exact SX2|].
    split; [replace (SS + 16) with (SS + Z.of_nat 8 + Z.of_nat 8) by lia; exact SX3|].
    split; [exists (Z_to_bv 64 0); replace (SS + 28) with (SS + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 12) by lia; exact SX4|].
    pose proof (CXZK (ELit 0) (SS + 32) (16 * 0x1000 - 16) ltac:(lia) S2) as [B W]. rewrite u_abs in B, W. rewrite repeat_length in W.
    split. { intros k Hk. unfold AsanDepot.kStoreBlockCount in Hk. split.
             - destruct (zero_sub FULL (SS + 32) (Z.to_nat (16 * 0x1000 - 16)) (Z.to_nat (16 * (k - 1))) 12 B W ltac:(lia)) as [B1 W1].
               rewrite Z2Nat.id in B1, W1 by lia. replace (SS + 32 + 16 * (k - 1)) with (SS + 16 + 16 * k) in B1, W1 by lia.
               apply rw_cells_zero; [cbn; exact (conj I (conj I I)) | reflexivity | exact B1 | exact W1].
             - exists (Z_to_bv 64 0).
               destruct (zero_sub FULL (SS + 32) (Z.to_nat (16 * 0x1000 - 16)) (Z.to_nat (16 * (k - 1) + 12)) 4 B W ltac:(lia)) as [B2 W2].
               rewrite Z2Nat.id in B2, W2 by lia. replace (SS + 32 + (16 * (k - 1) + 12)) with (SS + 28 + 16 * k) in B2, W2 by lia.
               apply rw_cells_zero; [cbn; exact (conj I I) | reflexivity | exact B2 | exact W2]. }
    (* [comment removed for export] *)
    split. { pose proof (CXRWK (pgE 515) 0 ws Wl Wk Wa) as [[_ SB] SW]. rewrite U515, Z.add_0_r in SB, SW.
      exists (Cells.cells_bytes (map (cx_cell E) ws)). split; [split; [exact SB | rewrite (Cells.cells_bytes_length _ (cxs_cells_wf E ws)); exact SW]|].
      rewrite (Cells.cells_bytes_length _ (cxs_cells_wf E ws)).
      pose proof (proj1 (CXSK (pgE 515) 0 ws Wl Wk)) as SP. rewrite U515, Z.add_0_r in SP.
      rewrite (proj2 (cxs_prop_bytes E FULL hs ws (pgv E 515) (pgE 515) 0 ltac:(intros ->; cbn in Wl; lia) Wa Wk SP)). rewrite Wn. reflexivity. }
    (* [comment removed for export] *)
    split. { pose proof (CXRWK (ELit 0) (TD + 0x400008) [CX4 0] ltac:(cbn; lia) UM eq_refl) as X. cbn [map cx_cell xv_den] in X. rewrite u_abs in X. exact X. }
    intros k Hk. unfold AsanDepot.kStoreBlockCount in Hk. destruct (Z.eq_dec k 0) as [-> | NZ].
    - rewrite Z.mul_0_r, Z.add_0_r. replace (SS + 28) with (SS + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 12) by lia. exact SX4.
    - destruct (zero_sub FULL (SS + 32) (Z.to_nat (16 * 0x1000 - 16)) (Z.to_nat (16 * (k - 1) + 12)) 4 B W ltac:(lia)) as [B2 W2].
      rewrite Z2Nat.id in B2, W2 by lia. replace (SS + 32 + (16 * (k - 1) + 12)) with (SS + 28 + 16 * k) in B2, W2 by lia.
      apply rw_cells_zero; [cbn; exact (conj I I) | reflexivity | exact B2 | exact W2].
  Qed.

  Theorem init_depot0 : AsanRepInit.depot0_facts AImages.asegs E0m FULL.
  Proof.
    pose proof Hhs as [Eh|[Eh|[Eh|Eh]]].
    1,3: eapply (depot_case [[0x3fdd8; 0x41128]] 3 38466 14505413795220854338);
      [ unfold keys0_of, rcase0; rewrite Eh; vm_compute; reflexivity
      | unfold frames0_of, rcase0; rewrite Eh; vm_compute; reflexivity
      | vm_compute; reflexivity
      | vm_compute; reflexivity
      | lia
      | intros _; rewrite Eh; vm_compute; reflexivity
      | rewrite Eh; vm_compute; reflexivity
      | intros _; rewrite Eh; vm_compute; reflexivity
      | rewrite Eh; vm_compute; reflexivity
      | rewrite Eh; vm_compute; reflexivity
      | rewrite Eh; vm_compute; reflexivity
      | rewrite Eh; vm_compute; reflexivity
      | rewrite Eh; vm_compute; reflexivity
      | rewrite Eh; vm_compute; reflexivity
      | rewrite Eh; vm_compute; reflexivity
      | exists [CX8 (XL 2); CX8 (XL 0x3fdd8); CX8 (XL 0x41128); CXZ 0x7fffe8]; split; [cbn; lia|]; split; [reflexivity|]; split; [reflexivity|]; rewrite Eh; vm_compute; reflexivity ].
    1,2: eapply (depot_case [[0x3fdd8]] 2 438931 14045708067666309779);
      [ unfold keys0_of, rcase0; rewrite Eh; vm_compute; reflexivity
      | unfold frames0_of, rcase0; rewrite Eh; vm_compute; reflexivity
      | vm_compute; reflexivity
      | vm_compute; reflexivity
      | lia
      | intros _; rewrite Eh; vm_compute; reflexivity
      | rewrite Eh; vm_compute; reflexivity
      | intros _; rewrite Eh; vm_compute; reflexivity
      | rewrite Eh; vm_compute; reflexivity
      | rewrite Eh; vm_compute; reflexivity
      | rewrite Eh; vm_compute; reflexivity
      | rewrite Eh; vm_compute; reflexivity
      | rewrite Eh; vm_compute; reflexivity
      | rewrite Eh; vm_compute; reflexivity
      | rewrite Eh; vm_compute; reflexivity
      | exists [CX8 (XL 1); CX8 (XL 0x3fdd8); CXZ 0x7ffff0]; split; [cbn; lia|]; split; [reflexivity|]; split; [reflexivity|]; rewrite Eh; vm_compute; reflexivity ].
  Qed.

  (* [comment removed for export] *)
  Theorem init_arep : AsanRep.ARep AImages.asegs E0m (AsanDepot.DepotR AImages.asegs E0m) (AsanState.astate0 E0m) FULL.
  Proof.
    assert (NK : AsanOps.zlen (AsanState.ae_keys0 E0m) < AsanConsts.kDepotNodesPerBlock).
    { unfold AsanOps.zlen, AsanConsts.kDepotNodesPerBlock. change (AsanState.ae_keys0 E0m) with (keys0_of hs). unfold keys0_of. destruct (rcase0 hs); cbn; lia. }
    assert (FR : 0 <= AsanState.ae_frames0 E0m <= AsanConsts.kStoreBlockFrames).
    { unfold AsanConsts.kStoreBlockFrames. change (AsanState.ae_frames0 E0m) with (frames0_of hs). unfold frames0_of. destruct (rcase0 hs); cbn; lia. }
    apply AsanRepInit.ARep_init; [exact init_arep0|]. split.
    - apply AsanBudget.depot_inv_init; [| exact NK]. change (AsanState.ae_frames0 E0m) with (frames0_of hs). unfold frames0_of. destruct (rcase0 hs); lia.
    - apply AsanRepInit.DepotRep_init; [exact NK | exact FR | exact init_depot0].
  Qed.
End MainRep.
