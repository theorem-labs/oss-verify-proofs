(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzDefs. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzTac2 BzInv. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTables. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzContracts BzContracts0 DecCut DecTac DecTac2 S0_dec_U13 S0_decCuts.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem BzCMem.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzDU2. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require DecCutF DecTacF DecTacFR.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDU5.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDOKp BzSepTac. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require S0F_decRet S0F_decCutsA S0F_decMain.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecCutF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacFR OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5.BzDRv OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOKp OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decRet OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decCutsA OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decMain.
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
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require JunkFast.
Local Ltac BzTac.bz32 ::= JunkFast.bz32_j.
Local Ltac BzTac2.bz32l ::= JunkFast.bz32l_j.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require RelLia.
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
Local Ltac Bz.BzSepTac.tlia2 ::= first [ RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; Bz.BzSepTac.unhide_disj; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac StoreFast.tlia ::= RelLia.tlia_r.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
(* [comment removed for export] *)
Section ACeilS1. Context {ACEIL__ : ACeil}.
Section R.
  Variable A : act14.
  Hypothesis AOK : act_ok 320 A.

  Notation usp := (bv_unsigned (a_sp A)).
  Notation cx := (a_cx A).
  Notation S := (b_s (a_cx A)).
  Notation W := (W14 DI_S0 (a_cx A) (bv_unsigned (a_sp A))).

  (* [comment removed for export] *)
  Lemma S0F_dec14_entry : forall (F : nat) (J : jk) (d : dst) (s : dstrm) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    dmem DI_S0 cx (a_g1 A) (a_sv A) (a_payload A) (a_m0 A) (dvF cx J d s) ->
    stk s0segs (a_m0 A) (a_lo A) usp -> mem_inv s0segs (a_m0 A) ->
    dpureF cx (a_b0 A) (a_payload A) J d s ->
    d_state d = 14%Z ->
    fuel_ok F d s ->
    evt s0segs (QF A (drun F 14 (d_sv d) d s))
      (MS (mkR (a_ra A) (a_sp A) (a_gp A) (a_tp A) t0 t1 t2 (a_s0 A) (a_s1 A) (Z_to_bv 64 S) a1 a2 a3 a4 a5 a6 a7
              (a_s2 A) (a_s3 A) (a_s4 A) (a_s5 A) (a_s6 A) (a_s7 A) (a_s8 A) (a_s9 A) (a_s10 A) (a_s11 A) t3 t4 t5 t6)
          (a_F A) (Z_to_bv 64 0x2462c) (a_fc A) None (a_m0 A) (seg_rom s0segs)).
  Proof.
    intros until t6. intros DM ST MI DP ST14 FU.
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN. pose proof rnums_words_length as RNL. lin_natZ RNL.
    pose proof (dpureF_snb _ _ _ _ _ _ DP) as SNB.
    assert (LS7 : (Z.land S 7 = 0)%Z).
    { pose proof (proj1 (act_ok_al _ _ AOK)) as SAL. change 7%Z with (Z.ones 3). rewrite Z.land_ones by lia.
      apply Z.mod_divide; [lia|]. apply Z.mod_divide in SAL; [destruct SAL as [k SAL]; exists (2 * k)%Z; lia | lia]. }
    pose proof (munch_refl W (a_m0 A)) as MU. pose proof (wmono_refl s0segs (a_m0 A)) as WM.
    unfold W14, D14, DSTATE_SIZE in MU. cbn [app blk_ivls b_s b_strm] in MU.
    pose proof (munch_refl [(usp + -336, usp)]%Z (a_m0 A)) as MUL. pose proof (wmono_refl s0segs (a_m0 A)) as WML.
    open_dmemF DM. s2img.
    (* [comment removed for export] *)
    hide_all_but (HD, SAV).
    pose proof SAV as SAV0. hide SAV0.
    rewrite ST14 in HD.
    carve_frame 336%nat ST.
    do 14 wstep.
    (* [comment removed for export] *)
    wstep. notrap. wstep. wstep. rewrite LS7. wstep. notrap. wstep.
    try change (sx32 (Z_to_bv 64 14)) with (Z_to_bv 64 14).
    wstep. wstep. wstep. wstep.
    wstep. if_true_z.
    (* [comment removed for export] *)
    do 39 wstep.
    clear SAV. (* [comment removed for export] *)
    (* [comment removed for export] *)
    wstep. wstep. wstep. if_false_z.
    do 11 wstep.
    (* [comment removed for export] *)
    wstep.
    do 6 wstep.
    (* [comment removed for export] *)
    wstep.
    (* [comment removed for export] *)
    lazymatch goal with
    | FRH : rw_cells s0segs ?mm (usp + -336)%Z (CB 88%nat ?jb :: ?rest) |- _ =>
        apply (rw_cells_split_CB s0segs mm (usp + -336)%Z [] 88%nat jb rest [8; 80]%nat) in FRH; [| reflexivity];
        cbn [mk_CB_cells app] in FRH;
        apply (rw_cells_CB_c8 s0segs mm (usp + -336)%Z [CB 8%nat (List.firstn 8 jb)] 10%nat) in FRH;
        cbn [c8cells app] in FRH
    end.
    rewrite <- ST14 in HD.
    revive_all MUL WML AOK.
    try rewrite (sx32_lit (sv_nblock (d_sv d))) by lia. try rewrite (sx32_of_Z (sv_nblock (d_sv d))) by lia.
    enter_cutF (S0F_dec_H14 A AOK F _ _ _ JK_) DP.
    all: try (unfold dinv_H14, nb_ok; exact SNB).
    all: try (lazymatch goal with H : rw_cells s0segs _ (usp + -336)%Z _ |- rw_cells _ _ _ _ => exact H end).
  Qed.
End R.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition act_okF' (A : act14) : Prop :=
  ctx_ok (a_cx A) /\ (a_lo A <= a_usp A - D14)%Z /\ (CEILING <= a_lo A)%Z /\ (a_usp A < 2^64)%Z /\
  Z.of_nat (length (a_payload A)) = b_len (a_cx A) /\ (1 <= b_n (a_cx A))%Z /\ (a_usp A <= b_strm (a_cx A))%Z /\
  (b_small (a_cx A) = 0%Z -> b_tt (a_cx A) <> 0%Z) /\
  (b_small (a_cx A) = 1%Z -> b_ll16 (a_cx A) <> 0%Z /\ b_ll4 (a_cx A) <> 0%Z) /\
  (b_small (a_cx A) = 0%Z \/ b_small (a_cx A) = 1%Z).

Definition ph_h0 (cx : bctx) : dsh :=
  DSH (b_strm cx) 14 (Z_to_bv 8 0) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0] 0 (Z_to_bv 8 0) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]
      0 0 0 0 (b_n cx) (Z_to_bv 8 (b_small cx)) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0] 0 0 0 (Z_to_bv 64 0) (Z_to_bv 64 0).
Definition ph_act (A : act14) : act14 :=
  ACT (a_ra A) (a_sp A) (a_gp A) (a_tp A) (a_s0 A) (a_s1 A) (a_s2 A) (a_s3 A) (a_s4 A) (a_s5 A) (a_s6 A) (a_s7 A)
      (a_s8 A) (a_s9 A) (a_s10 A) (a_s11 A) (a_F A) (a_fc A) (a_m0 A) (a_cx A) (ph_h0 (a_cx A)) (a_b0 A) (a_lo A)
      (a_g1 A) (a_sv A) (a_payload A).

Lemma ph_act_ok : forall A J d s, act_okF' A -> dpureF (a_cx A) (a_b0 A) (a_payload A) J d s ->
  a_b0 A = bs_of (a_cx A) J s -> (0 <= s_avail_out s <= b_dlen (a_cx A))%Z -> act_ok 320 (ph_act A).
Proof.
  (intros A J d s; cps_intros (CX & LO & CE & USP & PL & BN & UB & TT & LL & SM); intros DP EB AV).
  pose proof CX as CX'. cps_destruct CX' as (CL & _ & _). unfold ctx_lin in CL.
  pose proof (dpureF_jwf _ _ _ _ _ _ DP) as JW. unfold jk_wf in JW.
  pose proof (dpureF_in _ _ _ _ _ _ DP) as [k IR].
  assert (LENIN : (Z.of_nat (length (s_in s)) <= b_len (a_cx A))%Z).
  { rewrite IR, length_map, length_skipn. lia. }
  unfold act_ok. cbn [a_cx a_lo a_sp a_h0 a_b0 a_payload ph_act ph_h0 sh_state sh_strm sh_n sh_small].
  rewrite EB. cbn [bs_S bs_src bs_len bs_dst bs_dlen bs_of].
  repeat match goal with |- _ /\ _ => split end; try assumption; try reflexivity; try lia.
  - (* [comment removed for export] *) unfold dsh_wf; cbn. repeat split; try reflexivity; try lia.
  - (* [comment removed for export] *) unfold bzs_wf, bs_of; cbn. cps_destruct JW as (_ & _ & _ & _ & _ & Q1 & Q2). repeat split; try assumption; lia.
  - (* [comment removed for export] *) rewrite unsigned_lit8 by lia. reflexivity.
Qed.

Lemma FPOST14_ph : forall A R, FPOST14 DI_S0 (ph_act A) R = FPOST14 DI_S0 A R.
Proof. intros A R. destruct A; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem S0F_dec14F :
  forall (A : act14) (J : jk) (d : dst) (s : dstrm) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    act_okF' A ->
    dmem DI_S0 (a_cx A) (a_g1 A) (a_sv A) (a_payload A) (a_m0 A) (dvF (a_cx A) J d s) ->
    dpureF (a_cx A) (a_b0 A) (a_payload A) J d s ->
    d_state d = 14%Z -> a_b0 A = bs_of (a_cx A) J s ->
    (0 <= s_avail_out s <= b_dlen (a_cx A))%Z ->
    stk (di_segs DI_S0) (a_m0 A) (a_lo A) (a_usp A) -> mem_inv (di_segs DI_S0) (a_m0 A) ->
    evt (di_segs DI_S0) (fun ms' => FPOST14 DI_S0 A (decompress d s) ms' /\ dpost14W (decompress d s))
        (MS (mkR (a_ra A) (a_sp A) (a_gp A) (a_tp A) t0 t1 t2 (a_s0 A) (a_s1 A) (Z_to_bv 64 (a_S A)) a1 a2 a3 a4 a5 a6 a7
                 (a_s2 A) (a_s3 A) (a_s4 A) (a_s5 A) (a_s6 A) (a_s7 A) (a_s8 A) (a_s9 A) (a_s10 A) (a_s11 A) t3 t4 t5 t6)
            (a_F A) (Z_to_bv 64 (di_dec DI_S0)) (a_fc A) None (a_m0 A) (seg_rom (di_segs DI_S0))).
Proof.
  intros until t6. intros AF DM DP ST14 EB AV STK MI.
  pose proof (ph_act_ok A J d s AF DP EB AV) as AOK.
  pose proof (decompress_rv d s) as RV.
  rewrite (decompress_eq14 d s) in RV |- * by (rewrite ST14; cbv; discriminate). rewrite ST14 in RV |- *.
  set (F := (9 * length (s_in s) + 64)%nat) in *.
  assert (FU : fuel_ok F d s).
  { unfold fuel_ok. subst F. pose proof (dpureF_bl _ _ _ _ _ _ DP). rewrite Nat2Z.inj_add, Nat2Z.inj_mul. cbn [Z.of_nat Pos.of_succ_nat]. lia. }
  cbn [di_segs di_dec DI_S0].
  eapply evt_mono.
  - pose proof (S0F_dec14_entry (ph_act A) AOK F J d s t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6) as E.
    cbn [a_cx a_g1 a_sv a_payload a_m0 a_lo a_sp a_b0 a_ra a_gp a_tp a_s0 a_s1 a_s2 a_s3 a_s4 a_s5 a_s6 a_s7 a_s8 a_s9 a_s10 a_s11 a_F a_fc ph_act] in E.
    unfold QF in E. rewrite FPOST14_ph in E. exact (E DM STK MI DP ST14 FU).
  - intros ms' PO. split; [exact PO|].
    cbv beta in PO. destruct (dfin (drun F 14 (d_sv d) d s)) as [[rv d'] s'] eqn:ER.
    cps_destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & m' & J' & _ & _ & _ & _ & _ & _ & DP' & PST).
    unfold dpost14W. split; [| split; [| exact RV]].
    + intros E2. exact (PST E2).
    + intros _. pose proof (dpureF_rep _ _ _ _ _ _ DP') as RP. unfold drep in RP. change (2^32)%Z with 4294967296%Z in RP. tauto.
Qed.

End ACeilS1.
