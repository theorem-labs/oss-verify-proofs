(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzDefs. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzTac2 BzInv. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTables. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzContracts BzContracts0 DecCut DecTac DecTac2 DecAux S0_dec_U13.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem BzCMem.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzDU5 BzDU2 BzDU4. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require DecCutF DecTacF DecTacFR S0F_decRet S0F_decCuts S0F_decCuts4 DecTacM U0_mm.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU4 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecCutF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacFR OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decRet OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decCuts OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decCuts4.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import LinSplit. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import DecFast DecFastT.
Local Ltac DecCut.revive H MUL WML AOK ::= DecFast.revive_cached H MUL WML AOK.
Local Ltac DecCut.dpure_from DP ::= DecFast.dpure_from_fast DP.
Local Ltac DecCut.open_dmem DM ::= DecFast.open_dmem_red DM.
Local Ltac DecTac.gb_next keep Wloc IB ::= DecFastT.gb_next_red keep Wloc IB.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import NatLit.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzImg0TacFR BzImg0Tac.
Local Ltac Zify.zify_pre_hook ::= NatLit.natlen_ctx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)

(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require NormFast. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require RelLiaA. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require SasFastF. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require RelLia.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac lia ::= RelLiaA.lia_rf.
Local Ltac BzTac.bz32 ::= NormFast.bz32_m.
Local Ltac BzTac2.bz32l ::= NormFast.bz32l_m.
Local Ltac Zify.zify_pre_hook ::= NormFast.nf_pre_natlen.
Local Ltac DecCutF.unset_Z ::= NormFast.unset_Z_subst.
Local Ltac simpl_arr_sizes ::= SasFastF.sas6F_all.
Local Ltac StoreFast.tlia ::= RelLia.tlia_r.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
(* [comment removed for export] *)
Section ACeilS1. Context {ACEIL__ : ACeil}.

(* [comment removed for export] *)
Lemma mkmaps_n_bound : forall n i inUse s2u n0, (n0 <= snd (mkmaps n i inUse s2u n0) <= n0 + Z.of_nat n)%Z.
Proof.
  induction n as [|n IH]; intros i inUse s2u n0; cbn [mkmaps snd]; [lia|].
  destruct (negb (zget inUse i =? 0)%Z).
  - pose proof (IH (i + 1)%Z inUse (zset s2u n0 i) (n0 + 1)%Z). lia.
  - pose proof (IH (i + 1)%Z inUse s2u n0). lia.
Qed.
Lemma mkmaps_s2u_byte : forall n i inUse s2u n0, (0 <= i)%Z -> (i + Z.of_nat n <= 256)%Z -> (forall k, (0 <= zget s2u k < 256)%Z) ->
  forall k, (0 <= zget (fst (mkmaps n i inUse s2u n0)) k < 256)%Z.
Proof.
  induction n as [|n IH]; intros i inUse s2u n0 Hi Hn HB k; cbn [mkmaps fst]; [apply HB|].
  destruct (negb (zget inUse i =? 0)%Z).
  - apply IH; [lia | lia |]. intros j. rewrite zget_zset. destruct (Z.eqb_spec j n0); [lia| apply HB].
  - apply IH; [lia | lia | exact HB].
Qed.
(* [comment removed for export] *)
Lemma K_HMK_mm : forall F L d s,
  K_HMK F L d s = K_L4M F L (d_set_nInUse (d_set_s2u d (fst (mkmaps 256 0 (d_inUse d) (d_s2u d) 0))) (snd (mkmaps 256 0 (d_inUse d) (d_s2u d) 0))) s 256.
Proof. intros F L d s. unfold K_HMK, makeMaps_d. rewrite K_L4M_exit. destruct (mkmaps 256 0 (d_inUse d) (d_s2u d) 0). reflexivity. Qed.

Section R.
  Variable A : act14.
  Hypothesis AOK : act_ok 320 A.
  Variable F : nat.
  Hypothesis HSEL : S0F_cut_HSEL A F.
  (* [comment removed for export] *)

  Notation usp := (bv_unsigned (a_sp A)).
  Notation cx := (a_cx A).
  Notation S := (b_s (a_cx A)).

  (* [comment removed for export] *)
  Lemma S0F_dec_U4C : S0F_cut_HMK A F.
  Proof.
    unfold S0F_cut_HMK. intros until pb. intros DM FR ST MU WM MI DP DI FU.
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN. pose proof rnums_words_length as RNL. lin_natZ RNL.
    pose proof (act_ok_al _ _ AOK) as ALG; unfold ctx_al in ALG. cps_destruct ALG as (ALG1 & _).
    assert (S8 : (S mod 8 = 0)%Z).
    { apply Z.mod_divide in ALG1; [|lia]. destruct ALG1 as [q E]. rewrite E.
      replace (q * 16)%Z with (2 * q * 8)%Z by lia. apply Z_mod_mult. }
    clear ALG1.
    unfold W14, D14, DSTATE_SIZE in MU. cbn [app blk_ivls b_s b_strm] in MU.
    cps_destruct DI as (NB & HDR & IU & NS2). unfold nb_ok in NB.
    pose proof (dpureF_rep _ _ _ _ _ _ DP) as REP. unfold drep in REP. cps_destruct REP as (_ & _ & _ & RS2U & _).
    pose proof (mkmaps_n_bound 256 0 (d_inUse d) (d_s2u d) 0) as Hn. change (Z.of_nat 256) with 256%Z in Hn.
    pose proof (mkmaps_s2u_byte 256 0 (d_inUse d) (d_s2u d) 0 ltac:(lia) ltac:(lia) RS2U) as RS2U'.
    open_dmemF DM. s2img. unfold r_of in DR. dr_open. kq_intro. rewrite K_HMK_mm in KQ.
    hide_all_but_at [S + 3152; S + 3196; S + 3468]%Z.
    pose proof (munch_refl [(S + 3192, S + 3196); (S + 3468, S + 3724)]%Z m) as MUL. pose proof (wmono_refl s0segs m) as WML.
    (* [comment removed for export] *)
    wstepl. wstepl. wstepl. wstepl. wstepl. wstepl.
    eapply evt_cut.
    { eapply OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.U0_mm.makeMaps_d_spec with (DS := S) (lo := a_lo A);
        [ first [reflexivity | f_equal; lia] | eassumption | eassumption | eassumption
        | intros k Hk; pose proof (IU k Hk); lia | exact MI
        | rewrite unsigned_lit by lia; exact ST | exact S8 | lia | lia | rewrite unsigned_lit by lia; lia ]. }
    intros ms' PO. cbv beta in PO.
    destruct PO as (y5 & y6 & y7 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m' & Ems & MUc & WMc & MIc & ST' & MID' & IU8' & S2U8').
    subst ms'. rewrite (ret_pc_even 0x26264 ltac:(lia) eq_refl).
    rewrite unsigned_lit in ST' by lia.
    (* [comment removed for export] *)
    lazymatch type of MU with munch ?W14 ?m0 _ =>
      assert (SUB14 : sub_fp [(S + 3192, S + 3196); (S + 3468, S + 3724)]%Z W14) by (lin_unbox LIN; clear - LIN; OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacM.sub_fp_solve);
      apply (munch_trans W14 m0 m m') in MU; [ | exact (munch_weaken _ W14 m m' SUB14 MUc) ]; clear SUB14 end.
    apply (wmono_trans s0segs _ m m') in WM; [ | exact WMc ].
    apply (rw_cells_transport s0segs [(S + 3192, S + 3196); (S + 3468, S + 3724)]%Z m m') in FR; [ | exact MUc | exact WMc | cbn [disjoint_from cells_size csize Nat.add]; lia ].
    repeat match goal with H : rw_cells _ m _ _ |- _ => clear H | H : u8arr _ m _ _ |- _ => clear H end.
    clear MUL WML ST MI. rename MUc into MUL. rename WMc into WML.
    set (MK := mkmaps 256 0 (d_inUse d) (d_s2u d) 0) in *. clearbody MK. destruct MK as [mma mmn]. cbn [fst snd] in *.
    (* [comment removed for export] *)
    wstepl. wstepl. wstepl; if_cases KZ; zify_cond_z KZ.
    - (* [comment removed for export] *)
      rewrite K_L4M_exit_ret in KQ by (dmodel_cbn; unset_Z; lia).
      wstepl. wstepl. wstepl. wstepl. wstepl. wstepl. wstepl. wstepl. wstepl.
      revive_all MUL WML AOK. kq_fold. enter_cutF (S0F_dec_retc A AOK _ _ _ _ JK_) DP;
        [ ret_nb | apply dpost14_ne; dmodel_cbn; exact NS2 ].
    - (* [comment removed for export] *)
      rewrite K_L4M_exit_go in KQ by (dmodel_cbn; unset_Z; lia).
      wstepl. wstepl. notrap.
      wstepl. wstepl. wstepl. wstepl.
      revive_all MUL WML AOK. enter_sameF HSEL DP.
      (* [comment removed for export] *)
      unfold dinv_HSEL, alpha_ok, hdr_ok in *. dmodel_cbn. unset_Z. lia.
  Qed.
End R.
End ACeilS1.
