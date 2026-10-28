(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
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
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzDU5 BzDU2 BzDU4. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require DecCutF DecTacF DecTacFR S0F_decRet S0F_decCutsA S0F_decCuts4 S0F_gb_I.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU4 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecCutF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacFR OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decRet OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decCutsA OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decCuts4 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_gb_I.
From Stdlib Require Lia. 
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require LinSplit. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require DecFast DecFastT.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require NatLit.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzImg0TacFR BzImg0Tac.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require NormFast. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require RelLiaA. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require SasFastF. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require RelLia.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require RangeFast RangeFastEnv.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require CpsOpen.
Module S0F_dec_U4B.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.PropExec.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib.SegsS0.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzDefs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzModel OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzInv OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTables OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzContracts OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzContracts0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecCut OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTac2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecAux OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_dec_U13.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpMem OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU4 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecCutF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacFR OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decRet OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decCuts4 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_gb_I.
 Unset Lia Cache.
Import ListNotations. Local Open Scope bv_scope.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeil.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.LinSplit OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecFast OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecFastT.
Local Ltac DecCut.revive H MUL WML AOK ::= DecFast.revive_cached H MUL WML AOK.
Local Ltac DecCut.dpure_from DP ::= DecFast.dpure_from_fast DP.
Local Ltac DecCut.open_dmem DM ::= DecFast.open_dmem_red DM.
Local Ltac DecTac.gb_next keep Wloc IB ::= DecFastT.gb_next_red keep Wloc IB.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.NatLit.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzImg0TacFR OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzImg0Tac.
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
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.
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
    gbF_next [S; S + 3196; usp + -336]%Z [(S, S + 68); (S + 3196, S + 3452); (usp + -336, usp)]%Z.
    dr_open. hide_all_but_at [S; S + 3196; usp + -336]%Z.
    (* [comment removed for export] *)
    wstepl. wstepl. gbv 11%Z 1%Z ub. wstepl.
    rewrite edge_29 in KQ by (dmodel_cbn; lia). kq_norm.
    (* [comment removed for export] *)
    Ltac fin HO HI HDR MUL WML DP :=
      wstepl; wstepl; wstepl; notrap; wstepl; wstepl; wstepl; wstepl;
      let K := fresh "K15" in
      wstepl; if_cases K; zify_cond_z K;
      [ (* [comment removed for export] *)
        match goal with KQ : kq _ _ |- _ => rewrite (@if_falseP _ (_ <? 16)%Z) in KQ by blia end;
        wstepl; wstepl; notrap; wstepl; wstepl;
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
      wstepl. wstepl. wstepl. wstepl. notrap. wstepl. wstepl. wstepl. wstepl. wstepl. notrap.
      wstepl. wstepl. wstepl. notrap. wstepl. wstepl. wstepl. wstepl. notrap. wstepl. wstepl.
      lazymatch goal with H : u8arr _ _ (S + 3196)%Z _ |- _ => zb8_sb H (sv_i L * 16 + sv_j L)%Z end.
      fin HO HI HDR MUL WML DP; first [ apply in16_ok_frame_inUse; exact I16 | apply inUse_ok_set1'; unfold inUse_ok in IU; exact IU ].
  Qed.

  (* [comment removed for export] *)
  Lemma S0F_dec_U4B : S0F_cut_HMAP2I A F -> S0F_cut_HMK A F -> S0F_cut_HMAP2 A F.
  Proof.
    intros HI HMK.
    assert (G : forall k : nat, (k <= 16)%nat ->
      forall (L : dsv) (d : dst) (s : dstrm) (J : jk) (i : Z), i = (16 - Z.of_nat k)%Z ->
      forall (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x23 x24 x25 x26 x27 x28 x29 x31 : word)
         (m : word -> option byte)
         (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 f208 f216 : word) (pb : list byte),
      dmem DI_S0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J d s) ->
      S0FR A m j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 (Z_to_bv 64 (S + 2047)) f96 f104 f112 f120 f128 f136 f144 f152 f160
           f168 f176 f184 f192 (Z_to_bv 64 (S + 7820)) f208 f216 pb ->
      stk s0segs m (a_lo A) (usp + -336) ->
      munch (W14 DI_S0 cx usp) (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
      dpureF cx (a_b0 A) (a_payload A) J d s ->
      dinv_L4O L d i ->
      fuel_ok F d s ->
      evt s0segs (QF A (K_L4O F L d s i))
        (MS (mkR x1 (Z_to_bv 64 (usp + -336)) (a_gp A) (a_tp A) x5 x6 x7 x8 (Z_to_bv 64 i)
                x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 S) x19 (Z_to_bv 64 (S + 64036)) x21
                (Z_to_bv 64 (sv_nblock L)) x23 x24 x25 x26 x27 x28 x29 (Z_to_bv 64 (S + 7884)) x31)
            (a_F A) (Z_to_bv 64 0x26214) (a_fc A) None m (seg_rom s0segs))).
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
        unfold r_of in DR. dr_open. hide_all_but_at [S + 3452; usp + -336]%Z.
        pose proof (munch_refl [(usp + -336, usp)]%Z m) as MUL. pose proof (wmono_refl s0segs m) as WML.
        wstepl. wstepl. if_false_z. wstepl. notrap. wstepl. wstepl. wstepl. wstepl. notrap. wstepl.
        lazymatch goal with H : u8arr _ ?mm (S + 3452)%Z (zb8 ?a ?n) |- _ =>
          pose proof (zb8_read1 s0segs mm (S + 3452) a n i _ H ltac:(lia) eq_refl) as RD end.
        pose proof (I16 i ltac:(lia)) as Bi.
        wstepl. clear RD. rewrite zxb_lit8 by lia.
        wstepl; if_cases Kb; zify_cond_z Kb.
        + (* [comment removed for export] *)
          rewrite K_L4O_clear in KQ by lia.
          wstepl. wstepl. notrap. wstepl. wstepl.
          revive_all MUL WML AOK. kq_fold.
          enter_cutF (IH ltac:(lia) _ _ _ JK_ (i + 1)%Z ltac:(lia)) DP.
          unfold dinv_L4O, nb_ok. split; [lia|]. split; [apply (hdr_ok_frame _ _ HDR); dmodel_cbn; reflexivity|]. split; [lia|]. split; [exact I16|]. split; [exact IU| exact NS2].
        + (* [comment removed for export] *)
          rewrite K_L4O_set in KQ by lia.
          wstepl. wstepl. wstepl. wstepl. change (Z_to_le_bytes 8 0) with (le8 (Z_to_bv 64 0)). mem_after_store. wstepl. if_false_z.
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
Lemma zb8_clear256 : forall a, zb8 (clear256 256 0 a) 256 = repeat (Z_to_bv 8 0) (Z.to_nat 256).
Proof.
  intros a. apply nth_error_ext. intros k.
  destruct (Nat.lt_ge_cases k (Z.to_nat 256)) as [Hk|Hk].
  - rewrite nth_error_repeat by exact Hk. replace k with (Z.to_nat (Z.of_nat k)) by lia.
    rewrite zb8_nth by lia. rewrite zget_clear256_in by lia. reflexivity.
  - rewrite (proj2 (nth_error_None _ _)) by (rewrite zb8_length_nat; lia).
    rewrite (proj2 (nth_error_None _ _)) by (rewrite repeat_length; lia). reflexivity.
Qed.

Lemma zb8_clear256_snoc : forall a k, (0 <= k < 256)%Z ->
  zb8 (zset (clear256 (Z.to_nat k) 0 a) k 0) 256 = zb8 (clear256 (Z.to_nat (k + 1)) 0 a) 256.
Proof.
  intros a k Hk. apply nth_error_ext. intros n.
  destruct (Nat.lt_ge_cases n (Z.to_nat 256)) as [Hn|Hn].
  - replace n with (Z.to_nat (Z.of_nat n)) by lia. rewrite !zb8_nth by lia. f_equal. f_equal.
    rewrite zget_zset, !zget_clear256.
    destruct (Z.eqb_spec (Z.of_nat n) k) as [E|NE];
    destruct (Z.leb_spec 0 (Z.of_nat n)); destruct (Z.ltb_spec (Z.of_nat n) (0 + Z.of_nat (Z.to_nat k)));
    destruct (Z.ltb_spec (Z.of_nat n) (0 + Z.of_nat (Z.to_nat (k + 1)))); cbn [andb]; try reflexivity; try lia.
  - rewrite (proj2 (nth_error_None _ _)) by (rewrite zb8_length_nat; lia).
    rewrite (proj2 (nth_error_None _ _)) by (rewrite zb8_length_nat; lia). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma bit_flag : forall v, (0 <= v < 2)%Z -> (if (v =? 1)%Z then 1%Z else 0%Z) = v.
Proof. intros v Hv. destruct (Z.eqb_spec v 1); lia. Qed.

(* [comment removed for export] *)
Ltac ctx_fuel := match goal with FU : fuel_ok ?F1 _ _ |- _ => F1 end.
Tactic Notation "enter_nextK" constr(H) constr(DP) :=
  kq_fold; let F1 := ctx_fuel in enter_cutF (H F1 ltac:(lia) _ _ _ JK_) DP.
Ltac zb8_sb0 ARR i :=
  lazymatch goal with |- evt ?sg _ (MS _ _ _ _ _ ?mm _) =>
  lazymatch type of ARR with u8arr _ _ ?A (zb8 ?a ?n) =>
    let SO := fresh "SO" in
    pose proof (u8arr_store_ok sg mm A (zb8 a n) i _ ARR ltac:(rewrite zb8_length_nat; lia) eq_refl) as SO;
    step; try change (Z_to_le_bytes 1 0) with (le1 (Z_to_bv 64 0)); zb8_store_done ARR i; try clear SO; unfold wr8 in ARR;
    zsimp_in ARR; try rewrite Z.mod_small in ARR by lia; zsimp; bz32l
  end end.

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

  Definition S0F_cut_LZ (F' : nat) (k : Z) : Prop :=
    forall (L : dsv) (d : dst) (s : dstrm) (J : jk) (iu iu0 : zarr)
           (x1 x5 x6 x7 x8 x9 x13 x14 x15 x16 x17 x19 x21 x23 x24 x25 x26 x28 x29 x31 : word)
           (m : word -> option byte)
           (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 f208 f216 : word) (pb : list byte),
      dmem DI_S0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J (d_set_inUse d (clear256 (Z.to_nat k) 0 iu0)) s) ->
      S0FR A m j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 (Z_to_bv 64 (S + 2047)) f96 f104 f112 f120 f128 f136 f144 f152 f160
           f168 f176 f184 f192 (Z_to_bv 64 (S + 7820)) f208 f216 pb ->
      stk s0segs m (a_lo A) (usp + -336) ->
      munch (W14 DI_S0 cx usp) (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
      dpureF cx (a_b0 A) (a_payload A) J d s ->
      (nb_ok L /\ hdr_ok d /\ in16_ok d /\ d_state d <> 2%Z) ->
      fuel_ok F' d s ->
      evt s0segs (QF A (K_L4O F' (sv_set_i L 256) (d_set_inUse d (clear256 256 0 iu)) s 0))
        (MS (mkR x1 (Z_to_bv 64 (usp + -336)) (a_gp A) (a_tp A) x5 x6 x7 x8 x9
                (Z_to_bv 64 k) (Z_to_bv 64 (18446744073709551615 - (S + 3196))) (Z_to_bv 64 256) x13 x14 x15 x16 x17
                (Z_to_bv 64 S) x19 (Z_to_bv 64 (S + 64036)) x21 (Z_to_bv 64 (sv_nblock L)) x23 x24 x25 x26
                (Z_to_bv 64 (S + 3196 + k)) x28 x29 (Z_to_bv 64 (S + 7884)) x31)
            (a_F A) (Z_to_bv 64 0x26118) (a_fc A) None m (seg_rom s0segs)).

  Lemma S0F_U4_LZ_body : forall F' k, (0 <= k <= 255)%Z -> S0F_cut_HMAP2 A F' ->
    ((k < 255)%Z -> S0F_cut_LZ F' (k + 1)) -> S0F_cut_LZ F' k.
  Proof.
    intros F' k Hk HM2 NXT. unfold S0F_cut_LZ. intros until pb. (intros DM FR ST MU WM MI DP; cps_intros (NB & HDR & I16 & NS2); intros FU).
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN. pose proof rnums_words_length as RNL. lin_natZ RNL.
    unfold W14, D14, DSTATE_SIZE in MU. cbn [app blk_ivls b_s b_strm] in MU.
    open_dmemF DM. s2img. unfold r_of in DR. dr_open.
    kq_intro.
    hide_all_but_at [S + 3196]%Z.
    pose proof (munch_refl [(S + 3196, S + 3452)]%Z m) as MUL. pose proof (wmono_refl s0segs m) as WML.
    wstepl. notrap.
    lazymatch goal with H : u8arr _ _ (S + 3196)%Z _ |- _ =>
      zb8_sb0 H k; change (d_inUse (d_set_inUse d (clear256 (Z.to_nat k) 0 iu0))) with (clear256 (Z.to_nat k) 0 iu0) in H;
      rewrite (zb8_clear256_snoc iu0 k) in H by lia end.
    wstepl. wstepl.
    wstepl; if_cases Kl; zify_cond_z Kl.
    - pose proof (NXT ltac:(lia)) as NX. unfold S0F_cut_LZ in NX.
      revive_all MUL WML AOK.
      kq_fold. enter_cutF (NX _ _ _ JK_ iu iu0) DP.
      split; [exact NB| split; [exact HDR| split; [exact I16| exact NS2]]].
    - wstepl. wstepl.
      revive_all MUL WML AOK.
      lazymatch goal with H : u8arr _ _ (S + 3196)%Z _ |- _ =>
        replace (Z.to_nat (k + 1)) with 256%nat in H by lia; rewrite (zb8_clear256 iu0), <- (zb8_clear256 iu) in H end.
      kq_fold. enter_cutF (HM2 _ _ _ JK_ 0%Z) DP.
      unfold dinv_L4O. dmodel_cbn. split; [exact NB|]. split; [apply (hdr_ok_frame _ _ HDR); dmodel_cbn; reflexivity|]. split; [lia|].
      split; [apply in16_ok_frame_inUse; exact I16 |]. split; [apply inUse_ok_clear| exact NS2].
  Qed.

  Lemma S0F_U4_LZ : forall F', S0F_cut_HMAP2 A F' -> S0F_cut_LZ F' 0.
  Proof.
    intros F' HM2.
    assert (G : forall j : nat, (j <= 255)%nat -> S0F_cut_LZ F' (255 - Z.of_nat j)%Z).
    { induction j as [|j IH]; intros Hj.
      - apply S0F_U4_LZ_body; [lia | exact HM2 | intros; exfalso; lia].
      - apply S0F_U4_LZ_body; [lia | exact HM2 | intros _].
        replace (255 - Z.of_nat (Datatypes.S j) + 1)%Z with (255 - Z.of_nat j)%Z by lia. apply IH. lia. }
    exact (G 255%nat ltac:(lia)).
  Qed.

  (* [comment removed for export] *)
  Lemma S0F_U4_xm : forall F', (F' < F)%nat ->
    forall (L : dsv) (d : dst) (s : dstrm) (J : jk) (iu : zarr)
           (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x23 x24 x25 x26 x28 x29 x31 : word)
           (m : word -> option byte)
           (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 f208 f216 : word) (pb : list byte),
    dmem DI_S0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J d s) ->
    S0FR A m j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 (Z_to_bv 64 (S + 2047)) f96 f104 f112 f120 f128 f136 f144 f152 f160
         f168 f176 f184 f192 (Z_to_bv 64 (S + 7820)) f208 f216 pb ->
    stk s0segs m (a_lo A) (usp + -336) ->
    munch (W14 DI_S0 cx usp) (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J d s ->
    (nb_ok L /\ hdr_ok d /\ in16_ok d /\ d_state d <> 2%Z) ->
    fuel_ok F' d s ->
    evt s0segs (QF A (K_L4O F' (sv_set_i L 256) (d_set_inUse d (clear256 256 0 iu)) s 0))
      (MS (mkR x1 (Z_to_bv 64 (usp + -336)) (a_gp A) (a_tp A) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
              (Z_to_bv 64 S) x19 (Z_to_bv 64 (S + 64036)) x21 (Z_to_bv 64 (sv_nblock L)) x23 x24 x25 x26
              (Z_to_bv 64 (S + 3176)) x28 x29 (Z_to_bv 64 (S + 7884)) x31)
          (a_F A) (Z_to_bv 64 0x26108) (a_fc A) None m (seg_rom s0segs)).
  Proof.
    intros F' LTF. intros until pb. (intros DM FR ST MU WM MI DP; cps_intros (NB & HDR & I16 & NS2); intros FU).
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN. pose proof rnums_words_length as RNL. lin_natZ RNL.
    unfold W14, D14, DSTATE_SIZE in MU. cbn [app blk_ivls b_s b_strm] in MU.
    open_dmemF DM. s2img. unfold r_of in DR. dr_open.
    kq_intro.
    hide_all_but_at [S + 3196]%Z.
    pose proof (munch_refl [(S + 3196, S + 3452)]%Z m) as MUL. pose proof (wmono_refl s0segs m) as WML.
    do 4 wstepl.
    lazymatch goal with H : u8arr _ _ (S + 3196)%Z (zb8 ?a 256) |- _ =>
      change (zb8 a 256) with (zb8 (clear256 (Z.to_nat 0) 0 a) 256) in H end.
    revive_all MUL WML AOK.
    pose proof (S0F_U4_LZ F' (HMAP2 F' LTF)) as HZ. unfold S0F_cut_LZ in HZ.
    kq_fold. enter_cutF (HZ _ _ _ JK_ iu (d_inUse d)) DP.
    split; [exact NB| split; [exact HDR| split; [exact I16| exact NS2]]].
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
    gbF_next [S; S + 3452; usp + -336]%Z [(S, S + 68); (S + 3452, S + 3468)]%Z.
    dr_open. hide_all_but_at [S; S + 3452; usp + -336]%Z.
    (* [comment removed for export] *)
    wstepl. wstepl. gbv 11%Z 1%Z ub. wstepl.
    rewrite edge_28 in KQ. kq_norm.
    (* [comment removed for export] *)
    wstepl; if_cases Kbit; zify_cond_z Kbit;
    [ rewrite (@if_falseP _ (ub =? 1)%Z) in KQ by blia;
      wstepl; wstepl; notrap; wstepl; wstepl; wstepl; wstepl; notrap; wstepl;
      lazymatch goal with H : u8arr _ _ (S + 3452)%Z _ |- _ => zb8_sb0 H (sv_i L) end
    | rewrite (@if_trueP _ (ub =? 1)%Z) in KQ by blia;
      wstepl; wstepl; notrap; wstepl; wstepl; wstepl; wstepl; notrap; wstepl; wstepl;
      lazymatch goal with H : u8arr _ _ (S + 3452)%Z _ |- _ => zb8_sb H (sv_i L) end;
      wstepl ].
    (* [comment removed for export] *)
    all: wstepl; wstepl; wstepl.
    all: wstepl; if_cases K16; zify_cond_z K16.
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
    - rewrite if_falseP in KQ by blia.
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
