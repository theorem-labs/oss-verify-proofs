(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsS0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzDefs BzModel BzTac BzTac2 BzInv BzTables BzContracts BzContracts0 DecCut DecTac DecTac2 DecAux S0_dec_U13.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Musl Require Import S0_memset.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem BzCMem.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzDU5 BzDU2 BzDU4 DecCutF DecTacF DecTacFR S0F_decRet S0F_decCutsA S0F_decCuts4 S0F_gb_I.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU4 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFR OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0F_decRet OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0F_decCutsA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0F_decCuts4 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0F_gb_I.
From Stdlib Require Lia. 
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require LinSplit DecFast DecFastT.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require NatLit.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzImg0TacFR BzImg0Tac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require NormFast RelLiaA SasFastF RelLia.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require RangeFast RangeFastEnv.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require CpsOpen.
Module S0F_dec_U4B.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.PropExec.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.SegsS0.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDefs OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzModel OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzInv OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTables OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzContracts OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzContracts0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCut OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTac2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecAux OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0_dec_U13.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU4 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFR OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0F_decRet OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0F_decCuts4 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0F_gb_I.
 Unset Lia Cache.
Import ListNotations. Local Open Scope bv_scope.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.ACeil.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.LinSplit OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecFast OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecFastT.
Local Ltac DecCut.revive H MUL WML AOK ::= DecFast.revive_cached H MUL WML AOK.
Local Ltac DecCut.dpure_from DP ::= DecFast.dpure_from_fast DP.
Local Ltac DecCut.open_dmem DM ::= DecFast.open_dmem_red DM.
Local Ltac DecTac.gb_next keep Wloc IB ::= DecFastT.gb_next_red keep Wloc IB.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.NatLit.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzImg0TacFR OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzImg0Tac.
Local Ltac Zify.zify_pre_hook ::= NatLit.natlen_ctx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)

Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)

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
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.
(* [comment removed for export] *)
Ltac ctx_fuel := match goal with FU : fuel_ok ?F1 _ _ |- _ => F1 end.
Tactic Notation "enter_nextK" constr(H) constr(DP) :=
  kq_fold; let F1 := ctx_fuel in enter_cutF (H F1 ltac:(lia) _ _ _ JK_) DP.

Section ACeilS1. Context {ACEIL__ : ACeil}.
Section R.
  Variable A : act14.
  Hypothesis AOK : act_ok 320 A.
  Variable F : nat.

  Notation usp := (bv_unsigned (a_sp A)).
  Notation cx := (a_cx A).
  Notation S := (b_s (a_cx A)).

  Ltac prep DM MU :=
    unfold W14, D14, DSTATE_SIZE in MU; cbn [app blk_ivls b_s b_strm] in MU; open_dmemF DM; s2img.

  (* [comment removed for export] *)
  Lemma S0F_U4_L2I :
    (forall F', (F' < F)%nat -> S0F_cut_HMAP2I A F') -> (forall F', (F' < F)%nat -> S0F_cut_HMAP2 A F') ->
    S0F_cut_HMAP2I A F.
  Proof.
    intros HI HO. unfold S0F_cut_HMAP2I. intros until pb. intros DM FR ST MU WM MI DP DI FU.
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN. pose proof rnums_words_length as RNL. lin_natZ RNL.
    cps_destruct DI as (NB & HDR & Hi & Hj & I16 & IU). unfold nb_ok in NB. prep DM MU.
    gbF_call (S0F_gb_1d86c A AOK (QF A) (S0F_dec_ret_ok A AOK) _ _ _ _ JK_) MU WM AOK DP FU.
    gbF_next [S; S + 3196]%Z [(S, S + 68); (S + 3196, S + 3452)]%Z.
    dr_open. hide_all_but_at [S; S + 3196]%Z.
    (* [comment removed for export] *)
    wstepl. wstepl. gbv 11%Z 1%Z ub. wstepl.
    rewrite edge_29 in KQ by (dmodel_cbn; lia). kq_norm.
    (* [comment removed for export] *)
    Ltac fin HO HI HDR MUL WML DP :=
      wstepl; wstepl; wstepl;
      let K := fresh "K15" in
      wstepl; if_cases K; zify_cond_z K;
      [ (* [comment removed for export] *)
        match goal with KQ : kq _ _ |- _ => rewrite (@if_falseP _ (_ <? 16)%Z) in KQ by blia end;
        wstepl;
        revive_all MUL WML AOK; enter_nextK HO DP;
        unfold dinv_L4O, nb_ok; dmodel_cbn; split; [lia|]; split; [apply (hdr_ok_frame _ _ HDR); dmodel_cbn; reflexivity|]; split; [lia|];
        split; [| split; [| cbv; discriminate]]
      | match goal with KQ : kq _ _ |- _ => rewrite (@if_trueP _ (_ <? 16)%Z) in KQ by blia end;
        revive_all MUL WML AOK; enter_nextK HI DP;
        unfold dinv_HMAP2, nb_ok; dmodel_cbn; split; [lia|]; split; [apply (hdr_ok_frame _ _ HDR); dmodel_cbn; reflexivity|]; split; [lia|]; split; [lia|]; split ].
    (* [comment removed for export] *)
    wstepl; if_cases Kbit; zify_cond_z Kbit.
    - rewrite (@if_falseP _ (ub =? 1)%Z) in KQ by blia.
      fin HO HI HDR MUL WML DP; first [exact I16 | exact IU].
    - rewrite (@if_trueP _ (ub =? 1)%Z) in KQ by blia.
      (* [comment removed for export] *)
      wstepl. wstepl. wstepl. wstepl. wstepl.
      lazymatch goal with H : u8arr _ _ (S + 3196)%Z _ |- _ => zb8_sb H (sv_i L * 16 + sv_j L)%Z end.
      fin HO HI HDR MUL WML DP; first [ apply in16_ok_frame_inUse; exact I16 | apply inUse_ok_set1'; unfold inUse_ok in IU; exact IU ].
  Qed.

  (* [comment removed for export] *)
  Lemma S0F_dec_U4B : S0F_cut_HMAP2I A F -> S0F_cut_HMK A F -> S0F_cut_HMAP2 A F.
  Proof.
    intros HI HMK.
    assert (G : forall k : nat, (k <= 16)%nat ->
      forall (L : dsv) (d : dst) (s : dstrm) (J : jk) (i : Z), i = (16 - Z.of_nat k)%Z ->
      forall (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x23 x24 x25 x27 x29 x30 x31 : word)
         (m : word -> option byte)
         (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96 f136 f144 f152 f160 f168 f176 f184 f192 f200 : word) (pb : list byte),
      dmem DI_S0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J d s) ->
      S0FR A m j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96
           (Z_to_bv 64 (S + 2124)) (Z_to_bv 64 (S + 7884)) (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 7820))
           f136 f144 f152 f160 f168 f176 f184 f192 f200 pb ->
      stk s0segs m (a_lo A) (usp + -320) ->
      munch (W14 DI_S0 cx usp) (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
      dpureF cx (a_b0 A) (a_payload A) J d s ->
      dinv_L4O L d i ->
      fuel_ok F d s ->
      evt s0segs (QF A (K_L4O F L d s i))
        (MS (mkR x1 (Z_to_bv 64 (usp + -320)) (a_gp A) (a_tp A) x5 x6 x7 (Z_to_bv 64 (S + 64036)) x9
                x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 S) x20 x21
                (Z_to_bv 64 (S + 2047)) x23 x24 x25 (Z_to_bv 64 i) x27 (Z_to_bv 64 (sv_nblock L)) x29 x30 x31)
            (a_F A) (Z_to_bv 64 0x1d840) (a_fc A) None m (seg_rom s0segs))).
    { induction k as [|k IH]; intros Hk L d s J i Ei; intros until pb; intros DM FR ST MU WM MI DP DI FU;
      pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN; pose proof rnums_words_length as RNL; lin_natZ RNL;
      cps_destruct DI as (NB & HDR & Hi & I16 & IU & NS2); unfold nb_ok in NB; prep DM MU; kq_intro.
      - (* [comment removed for export] *)
        cbn in Ei. subst i. rewrite K_L4O_exit in KQ.
        wstepl. wstepl. if_true_z.
        enter_sameF HMK DP.
        unfold dinv_HMK, nb_ok. split; [lia|]. split; [apply (hdr_ok_frame _ _ HDR); dmodel_cbn; reflexivity|]. split; [exact IU| exact NS2].
      - (* [comment removed for export] *)
        rewrite Nat2Z.inj_succ in Ei.
        unfold r_of in DR. dr_open. hide_all_but_at [S + 3452]%Z.
        pose proof (munch_refl [(S, S)]%Z m) as MUL. pose proof (wmono_refl s0segs m) as WML.
        wstepl. wstepl. if_false_z. wstepl. wstepl.
        lazymatch goal with H : u8arr _ ?mm (S + 3452)%Z (zb8 ?a ?n) |- _ =>
          pose proof (zb8_read1 s0segs mm (S + 3452) a n i _ H ltac:(lia) eq_refl) as RD end.
        pose proof (I16 i ltac:(lia)) as Bi.
        wstepl. clear RD. rewrite zxb_lit8 by lia.
        wstepl; if_cases Kb; zify_cond_z Kb.
        + (* [comment removed for export] *)
          rewrite K_L4O_clear in KQ by lia.
          wstepl.
          revive_all MUL WML AOK. kq_fold.
          enter_cutF (IH ltac:(lia) _ _ _ JK_ (i + 1)%Z ltac:(lia)) DP.
          unfold dinv_L4O, nb_ok. split; [lia|]. split; [apply (hdr_ok_frame _ _ HDR); dmodel_cbn; reflexivity|]. split; [lia|]. split; [exact I16|]. split; [exact IU| exact NS2].
        + (* [comment removed for export] *)
          rewrite K_L4O_set in KQ by lia.
          wstepl. wstepl. wstepl. wstepl. if_false_z.
          revive_all MUL WML AOK. enter_sameF HI DP.
          unfold dinv_HMAP2, nb_ok. dmodel_cbn. split; [lia|]. split; [apply (hdr_ok_frame _ _ HDR); dmodel_cbn; reflexivity|]. split; [lia|]. split; [lia|]. split; [exact I16| exact IU]. }
    unfold S0F_cut_HMAP2. intros until i. intros until pb. intros DM FR ST MU WM MI DP DI FU.
    pose proof DI as DI'. cps_destruct DI' as (_ & _ & Hi & _).
    eapply (G (Z.to_nat (16 - i)) ltac:(lia) L d s J i ltac:(lia)); eassumption.
  Qed.
End R.
End ACeilS1.
End S0F_dec_U4B.

Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import LinSplit DecFast DecFastT.
Local Ltac DecCut.revive H MUL WML AOK ::= DecFast.revive_cached H MUL WML AOK.
Local Ltac DecCut.dpure_from DP ::= DecFast.dpure_from_fast DP.
Local Ltac DecCut.open_dmem DM ::= DecFast.open_dmem_red DM.
Local Ltac DecTac.gb_next keep Wloc IB ::= DecFastT.gb_next_red keep Wloc IB.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import NatLit.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzImg0TacFR BzImg0Tac.
Local Ltac Zify.zify_pre_hook ::= NatLit.natlen_ctx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require NormFast RelLiaA SasFastF RelLia.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require RangeFast RangeFastEnv.
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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
(* [comment removed for export] *)
Lemma zb8_clear256 : forall a, zb8 (clear256 256 0 a) 256 = repeat (Z_to_bv 8 0) (Z.to_nat 256).
Proof.
  intros a. apply nth_error_ext. intros k.
  destruct (Nat.lt_ge_cases k (Z.to_nat 256)) as [Hk|Hk].
  - rewrite nth_error_repeat by exact Hk. replace k with (Z.to_nat (Z.of_nat k)) by lia.
    rewrite zb8_nth by lia. rewrite zget_clear256_in by lia. reflexivity.
  - rewrite (proj2 (nth_error_None _ _)) by (rewrite zb8_length_nat; lia).
    rewrite (proj2 (nth_error_None _ _)) by (rewrite repeat_length; lia). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma bit_flag : forall v, (0 <= v < 2)%Z -> (if (v =? 1)%Z then 1%Z else 0%Z) = v.
Proof. intros v Hv. destruct (Z.eqb_spec v 1); lia. Qed.

(* [comment removed for export] *)
Ltac ctx_fuel := match goal with FU : fuel_ok ?F1 _ _ |- _ => F1 end.
Tactic Notation "enter_nextK" constr(H) constr(DP) :=
  kq_fold; let F1 := ctx_fuel in enter_cutF (H F1 ltac:(lia) _ _ _ JK_) DP.

Section ACeilS1. Context {ACEIL__ : ACeil}.
Section R.
  Variable A : act14.
  Hypothesis AOK : act_ok 320 A.
  Variable F : nat.
  Hypothesis HMAP : forall F', (F' < F)%nat -> S0F_cut_HMAP A F'.
  Hypothesis HMAP2 : forall F', (F' < F)%nat -> S0F_cut_HMAP2 A F'.

  Notation usp := (bv_unsigned (a_sp A)).
  Notation cx := (a_cx A).
  Notation S := (b_s (a_cx A)).

  (* [comment removed for export] *)
  Lemma S0F_U4_xm : forall F', (F' < F)%nat ->
    forall (L : dsv) (d : dst) (s : dstrm) (J : jk) (iu : zarr)
           (x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x23 x24 x25 x27 x29 x30 x31 : word)
           (m : word -> option byte)
           (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96 f136 f144 f152 f160 f168 f176 f184 f192 f200 : word) (pb : list byte),
    dmem DI_S0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J d s) ->
    S0FR A m j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96
         (Z_to_bv 64 (S + 2124)) (Z_to_bv 64 (S + 7884)) (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 7820))
         f136 f144 f152 f160 f168 f176 f184 f192 f200 pb ->
    stk s0segs m (a_lo A) (usp + -320) ->
    munch (W14 DI_S0 cx usp) (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J d s ->
    (nb_ok L /\ hdr_ok d /\ in16_ok d /\ d_state d <> 2%Z) ->
    fuel_ok F' d s ->
    evt s0segs (QF A (K_L4O F' (sv_set_i L 256) (d_set_inUse d (clear256 256 0 iu)) s 0))
      (MS (mkR x1 (Z_to_bv 64 (usp + -320)) (a_gp A) (a_tp A) x5 x6 x7 (Z_to_bv 64 (S + 64036)) x9
              (Z_to_bv 64 16) x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 S) x20 x21
              (Z_to_bv 64 (S + 2047)) x23 x24 x25 (Z_to_bv 64 16) x27 (Z_to_bv 64 (sv_nblock L)) x29 x30 x31)
          (a_F A) (Z_to_bv 64 0x1d7b4) (a_fc A) None m (seg_rom s0segs)).
  Proof.
    intros F' LTF. intros until pb. (intros DM FR ST MU WM MI DP; cps_intros (NB & HDR & I16 & NS2); intros FU).
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN. pose proof rnums_words_length as RNL. lin_natZ RNL.
    unfold W14, D14, DSTATE_SIZE in MU. cbn [app blk_ivls b_s b_strm] in MU.
    open_dmemF DM. s2img. unfold r_of in DR. dr_open.
    kq_intro.
    hide_all_but_at [S + 3196; usp + -320]%Z.
    pose proof (munch_refl [(S + 3196, S + 3452); (usp + -320, usp)]%Z m) as MUL. pose proof (wmono_refl s0segs m) as WML.
    do 18 wstepl.
    lazymatch goal with H : u8arr _ _ (S + 3196)%Z ?bs |- _ =>
      apply rw_cells_of_u8arr in H; replace (length bs) with (Z.to_nat 256) in H by (rewrite zb8_length_nat; reflexivity);
      rename H into DST end.
    call (S0_memset_specZ (S + 3196) 256 0).
    1:{ exact DST. } 1:{ exact MI. }
    1:{ first [reflexivity | f_equal; lia]. } 1:{ reflexivity. } 1:{ reflexivity. } 1:{ lia. } 1:{ lia. } 1:{ lia. }
    match goal with H : rw_cells s0segs _ (S + 3196)%Z [CB _ (repeat _ _)] |- _ =>
      apply u8arr_of_rw_cells in H; rewrite <- (zb8_clear256 iu) in H; rename H into DRinUseZ end.
    match goal with H : mem_inv s0segs _ |- _ => rename H into MI end.
    do 16 wstepl.
    revive_all MUL WML AOK.
    enter_nextK HMAP2 DP.
    unfold dinv_L4O. dmodel_cbn. split; [exact NB|]. split; [apply (hdr_ok_frame _ _ HDR); dmodel_cbn; reflexivity|]. split; [lia|].
    split; [apply in16_ok_frame_inUse; exact I16 |]. split; [apply inUse_ok_clear| exact NS2].
  Qed.

  (* [comment removed for export] *)
  Lemma S0F_dec_U4A : S0F_cut_HMAP A F.
  Proof.
    unfold S0F_cut_HMAP. intros until pb. intros DM FR ST MU WM MI DP DI FU.
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN. pose proof rnums_words_length as RNL. lin_natZ RNL.
    unfold W14, D14, DSTATE_SIZE in MU. cbn [app blk_ivls b_s b_strm] in MU.
    unfold dinv_HMAP, nb_ok, op_ok in DI. cps_destruct DI as (NB & HDR & Hi & I16).
    open_dmemF DM. s2img.
    gbF_call (S0F_gb_1d610 A AOK (QF A) (S0F_dec_ret_ok A AOK) _ _ _ _ JK_) MU WM AOK DP FU.
    gbF_next [S; S + 3452]%Z [(S, S + 68); (S + 3452, S + 3468)]%Z.
    dr_open. hide_all_but_at [S; S + 3452]%Z.
    (* [comment removed for export] *)
    wstepl. wstepl. wstepl. wstepl. wstepl. gbv 10%Z 1%Z ub.
    rewrite edge_28 in KQ. kq_norm. rewrite (bit_flag ub) in KQ by (unset_Z; lia).
    (* [comment removed for export] *)
    lazymatch goal with H : u8arr _ _ (S + 3452)%Z _ |- _ =>
      zb8_sb H (sv_i L); try rewrite (Z.mod_small ub 256) in H by (unset_Z; lia) end.
    (* [comment removed for export] *)
    wstepl. wstepl. wstepl.
    wstepl; if_cases K16; zify_cond_z K16.
    - (* [comment removed for export] *)
      rewrite if_falseP in KQ by blia.
      revive_all MUL WML AOK. enter_nextK S0F_U4_xm DP.
      unfold nb_ok, in16_ok. dmodel_cbn. split; [lia|]. split; [apply (hdr_ok_frame _ _ HDR); dmodel_cbn; reflexivity|].
      split; [| cbv; discriminate].
      intros k Hk. rewrite zget_zset. destruct (Z.eqb_spec k (sv_i L)); [unset_Z; lia|]. apply I16. lia.
    - rewrite if_trueP in KQ by blia.
      revive_all MUL WML AOK. enter_nextF HMAP DP.
      unfold dinv_HMAP, nb_ok, op_ok. dmodel_cbn. split; [lia|]. split; [apply (hdr_ok_frame _ _ HDR); dmodel_cbn; reflexivity|]. split; [lia|].
      intros k Hk. rewrite zget_zset. destruct (Z.eqb_spec k (sv_i L)); [unset_Z; lia|]. apply I16. lia.
  Qed.
End R.
End ACeilS1.
