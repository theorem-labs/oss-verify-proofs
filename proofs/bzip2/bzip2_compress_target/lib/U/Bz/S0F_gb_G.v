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
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzDefs. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzTac2 BzInv. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTables. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzContracts BzContracts0 DecCut S0_dec_U13.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require DecCutF DecTacF S0F_decRet.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecCutF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decRet.
From Stdlib Require Lia. 
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require LinSplit. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require DecFast.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require NatLit.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzImg0TacF.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFastZ StoreFastC.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require NormFast. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require FLiaA.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require GbKit GbKitF.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require RangeFast RangeFastEnv.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import U0_decKit.
Module S0F_gb_F.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.PropExec.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib.SegsS0.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzDefs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzModel OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzInv OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTables OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzContracts OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzContracts0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecCut OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_dec_U13.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpMem.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecCutF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decRet.
 Unset Lia Cache.
Import ListNotations. Local Open Scope bv_scope.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeil.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.LinSplit OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecFast.
Local Ltac DecCut.revive H MUL WML AOK ::= DecFast.revive_cached H MUL WML AOK.
Local Ltac DecCut.dpure_from DP ::= DecFast.dpure_from_fast DP.
Local Ltac DecCut.open_dmem DM ::= DecFast.open_dmem_red DM.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.NatLit.
Local Ltac Zify.zify_pre_hook ::= NatLit.natlen_ctx.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.StoreFast.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzImg0TacF.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
   (* [comment removed for export] *)
Local Ltac mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
(* [comment removed for export] *)

Local Ltac lia ::= FLiaA.lia_f.
Local Ltac BzTac.bz32 ::= NormFast.bz32_m.
Local Ltac BzTac2.bz32l ::= NormFast.bz32l_m.
Local Ltac Zify.zify_pre_hook ::= NormFast.nf_pre_natlen.
Local Ltac DecCutF.unset_Z ::= NormFast.unset_Z_subst.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
   (* [comment removed for export] *)
(* [comment removed for export] *)

Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)

#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section ACeilS1. Context {ACEIL__ : ACeil}.

Section R.
  Variable A : act14.
  Hypothesis AOK : act_ok 320 A.

  Notation usp := (bv_unsigned (a_sp A)).
  Notation cx := (a_cx A).
  Notation S := (b_s (a_cx A)).
  Notation W := (W14 DI_S0 (a_cx A) (bv_unsigned (a_sp A))).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Ltac gbF_close DP MUL WML :=
    lazymatch goal with DM0 : dmem _ _ _ _ _ _ _ |- dmem _ ?cx _ _ _ ?mm _ =>
      eapply (GbKitF.gbF_dmem_close _ _ AOK _ (GbKit.di_in_img_ok DI_S0 eq_refl) _ _ _ _ _ _ _ _ DM0 DP MUL WML);
      [ dvF_cbn; dmodel_cbn; match goal with H : rw_cells _ mm (b_s cx) _ |- _ => exact_cells H end
      | dvF_cbn; dmodel_cbn; match goal with H : rw_cells _ mm (b_strm cx) _ |- _ => exact_cells H end
      | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity ]
    end.
  Ltac cut_sideG MUL WML DP :=
    lazymatch goal with
    | |- dmem _ _ _ _ _ _ _ => first [ gbF_close DP MUL WML | revive_all MUL WML AOK; cut_sideF DP ]
    | |- rw_cells _ _ (bv_unsigned (a_sp _) + _)%Z _ =>      (* [comment removed for export] *)
        first [ cut_sideF DP
              | match goal with H : hidden (rw_cells _ _ (bv_unsigned (a_sp _) + _)%Z _) |- _ => revive H MUL WML AOK end; cut_sideF DP
              | revive_all MUL WML AOK; cut_sideF DP ]
    | |- _ => cut_sideF DP
    end.
  Ltac gbF_exit HK HD STRM MUL WML DP MD FU breg n :=
    lazymatch type of HD with rw_cells _ _ _ ?cs =>
      let c := eval cbv beta iota zeta delta [cell_at csize Nat.eqb Nat.ltb Nat.leb Nat.sub Nat.add] in (cell_at cs 32%nat) in
      lazymatch c with Some (C4 (Z_to_bv 64 ?bbx)) =>
        let w := fresh "wb" in gbword breg w bbx;
        [ first [ apply sx32_mod32; lia | apply pullw_reg32; lia ]
        | erewrite (drun_bits' _ _ _ _ _ _ _ n) in MD by first [reflexivity | cbn; lia];
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          eapply evt_eq; [ | eapply (HK _ _ _ _ _ _ _ mm _ MD) ]; only 1: unify_memF;
          [ | eapply fuel_ok_gbst_bits; [exact FU | cbn; lia] | try cut_sideG MUL WML DP .. ];
          [ dvF_cbn; dmodel_cbn; st_eq | try (cbn [length]; unset_Z; lia) .. ] end ]
      end end.
  (* [comment removed for export] *)
  Ltac gbF_ret HRET MUL WML DP MD NB n :=
    erewrite (drun_eof' _ _ _ _ _ _ _ n) in MD by first [reflexivity | cbn; lia];
    rewrite MD;
    (eapply evt_eq; [ | eapply (HRET _ _ _ (JK _ _ _ _ _ _ _ _ _ _ _ _ _ _)) ]; only 1: unify_memF; try cut_sideG MUL WML DP; only 1: (dvF_cbn; dmodel_cbn; st_eq)); [exact NB | apply dpost14_ne; dmodel_cbn; cbv; discriminate].
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma S0F_gb_1cd5c : forall (Q : dres -> machine_state -> Prop), S0F_RET_OK A Q ->
    forall (F : nat) (L : dsv) (d : dst) (s : dstrm) (J : jk)
           (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte)
           (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 f200 f208 f216 : word) (pb : list byte),
    dmem DI_S0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J d s) ->
    S0FR A m j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 f200 f208 f216 pb ->
    stk s0segs m (a_lo A) (usp + -336) ->
    munch W (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J d s ->
    (0 <= sv_nblock L <= 900000)%Z ->
    fuel_ok F d s ->
    (forall (F1 : nat) (bb' bl' : Z) (inp' : list Z) (tin' : Z) (til' tih' : word) (m' : word -> option byte) (wb : word),
       let d2 := gbst d 43 bb' bl' in
       let s1 := DSTRM inp' (s_out s) (s_avail_out s) tin' (s_tout s) in
       drun F 43 L d s = dgo F1 (gb_after 43 (gbval bb' bl' 8) L (d_set_bsLive d2 (bl' - 8)) s1) ->
       fuel_ok F1 (d_set_bsLive d2 (bl' - 8)) s1 -> (F1 < F)%nat ->
       dmem DI_S0 cx (a_g1 A) (a_sv A) (a_payload A) m' (dvF cx (jk_set_t J til' tih') d2 s1) ->
       S0FR A m' j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 f200 f208 f216 pb ->
       stk s0segs m' (a_lo A) (usp + -336) ->
       munch W (a_m0 A) m' -> wmono s0segs (a_m0 A) m' -> mem_inv s0segs m' ->
       dpureF cx (a_b0 A) (a_payload A) (jk_set_t J til' tih') d2 s1 ->
       (0 <= bb' < 2^32)%Z -> (8 <= bl' <= 32)%Z -> (bv_unsigned wb mod 4294967296 = bb')%Z ->
       (8 * Z.of_nat (length inp') + bl' = 8 * Z.of_nat (length (s_in s)) + d_bsLive d)%Z ->
       forall (y12 y13 y14 y15 y16 y17 : word),
       evt s0segs (Q (drun F 43 L d s))
         (MS (mkR x1 (Z_to_bv 64 (usp + -336)) (a_gp A) (a_tp A) x5 x6 x7 x8 x9 (Z_to_bv 64 (bl' - 8)) wb y12 y13 y14 y15 y16 y17
                 (Z_to_bv 64 S) x19 (Z_to_bv 64 (S + 64036)) x21 (Z_to_bv 64 (sv_nblock L)) x23 x24 x25 x26 x27 x28 x29 x30 x31)
             (a_F A) (Z_to_bv 64 0x25978) (a_fc A) None m' (seg_rom s0segs))) ->
    evt s0segs (Q (drun F 43 L d s))
      (MS (mkR x1 (Z_to_bv 64 (usp + -336)) (a_gp A) (a_tp A) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
                 (Z_to_bv 64 S) x19 (Z_to_bv 64 (S + 64036)) x21 (Z_to_bv 64 (sv_nblock L)) x23 x24 x25 x26 x27 x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0x258c4) (a_fc A) None m (seg_rom s0segs)).
  Proof.
    intros Q HRET. intros until pb. intros DM FR ST MU WM MI DP NB FU HK.
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN. pose proof rnums_words_length as RNL. lin_natZ RNL.
    unfold W14, D14, DSTATE_SIZE in MU. cbn [app blk_ivls b_s b_strm] in MU.
    destruct s as [inp sout sav stin stout]. cbn [s_in s_out s_avail_out s_tin s_tout] in *.
    pose proof DM as DM0. open_dmemF DM. s2img. cbn [s_in s_out s_avail_out s_tin s_tout] in *.
    destruct (fuel_ok_pos _ _ _ (proj1 (dpureF_bl _ _ _ _ _ _ DP)) FU) as [f EF]. subst F.
    pose proof (drun_gbst f 43 L d (DSTRM inp sout sav stin stout)) as MD. apply (fuel_ok_gbst _ _ 43) in FU.
    pose proof (dpureF_in _ _ _ _ _ _ DP) as IR.
    set (bl := d_bsLive d) in *. set (bb := d_bsBuff d) in *.
    hide_all_but (HD, STRM).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (munch_refl [(S, S + 68); (b_strm cx, b_strm cx + 20)]%Z mm) as MUL;
      pose proof (wmono_refl s0segs mm) as WML end.
    wstepl. wstepl. wstepl. wstepl.
    wstepl. if_cases K; zify_cond_z K.
    { (* [comment removed for export] *)
      wstepl. wstepl. wstepl. notrap. wstepl.
      gbF_exit HK HD STRM MUL WML DP MD FU 11%Z 8%Z.
    }
    { (* [comment removed for export] *)
      wstepl. wstepl. wstepl. wstepl. wstepl. wstepl.
      rewrite (strm_flag_ok cx (proj1 AOK)).
      wstepl. notrap.
      wstepl.
      wstepl. if_cases K2; zify_cond K2.
      { (* [comment removed for export] *)
        assert (inp = []) as -> by (lin_unbox LIN; destruct inp; [reflexivity| exfalso; cbn [length] in K2, LIN; rewrite Nat2Z.inj_succ in K2, LIN; clear -K2 LIN; zb_masks; mlia]). clear K2.
        gbF_ret HRET MUL WML DP MD NB 8%Z.
      }
      { (* [comment removed for export] *)
        assert (AI1 : (1 <= Z.of_nat (length inp))%Z) by (lin_unbox LIN; clear - K2 LIN; zb_masks; mlia). clear K2. destruct inp as [|bz inp1]; [exfalso; cbn in AI1; lia|]. destruct (in_rel_head (a_payload A) _ _ _ IR eq_refl) as [b8 [NTH Ebz]]. cbn [s_in length] in NTH. cbn [length] in *. rewrite Nat2Z.inj_succ in *. subst bz.
        wstepl. wstepl. notrap.
        wstepl.
        pose proof PAY as PAYL. revive PAYL MUL WML AOK.
        pose proof (u8ro_read s0segs _ (b_src cx) (a_payload A) (b_len cx - Z.succ (Z.of_nat (length inp1)))%Z b8 _ PAYL ltac:(rewrite <- NTH; f_equal; lia) ltac:(lia) eq_refl) as RD.
        (let pv := reg_val 15%Z in lazymatch pv with Z_to_bv 64 ?e => replace e with (b_src cx + (b_len cx - Z.succ (Z.of_nat (length inp1))))%Z by lia end).
        wstepl. clear RD PAYL.
        wstepl. wstepl. wstepl. wstepl. wstepl.
        wstepl. notrap.
        wstepl. forget_reg 16%Z wtil.
        wstepl. wstepl. wstepl. forget_reg 16%Z wtil2. wstepl. wstepl. wstepl.
        (* [comment removed for export] *)
        cell_mod32 HD 32%nat. change (2^32)%Z with 4294967296%Z in HD. rewrite (pullw_mod32 bb b8) in HD by lia.
        set (bb1 := u32 (Z.lor (Z.shiftl bb 8) (bv_unsigned b8))) in *.
        pose proof (u32_range' (Z.lor (Z.shiftl bb 8) (bv_unsigned b8))) as Rbb1. change (u32 _) with bb1 in Rbb1.
        replace (b_src cx + (b_len cx - Z.succ (Z.of_nat (length inp1))) + 1)%Z with (b_src cx + (b_len cx - Z.of_nat (length inp1)))%Z in STRM by lia.
        replace (Z.succ (Z.of_nat (length inp1)) + -1)%Z with (Z.of_nat (length inp1)) in STRM by lia.
        erewrite (drun_pull_D _ _ _ _ _ _ 8%Z) in MD by first [reflexivity | cbn; lia]. change (u32 _) with bb1 in MD.
        apply (fuel_ok_pull_D _ _ _ _ _ bb1 _ _ _ _ _ (stin + 1)) in FU.
        destruct (fuel_ok_gbst_S _ _ _ _ _ _ FU ltac:(lia)) as [f1 Ef1]. subst f.
        pose proof (in_rel_tail _ _ (DSTRM inp1 sout sav (stin + 1) stout) _ _ IR eq_refl eq_refl) as IR1.
        wstepl. if_cases K3.
        { (* [comment removed for export] *)
          wstepl. wstepl. if_false_z.
          wstepl. wstepl. wstepl. notrap. wstepl.
          gbF_exit HK HD STRM MUL WML DP MD FU 11%Z 8%Z.
        }
        { (* [comment removed for export] *)
          wstepl. forget_reg 14%Z wtih. wstepl. wstepl.
          wstepl. wstepl. if_false_z.
          wstepl. wstepl. wstepl. notrap. wstepl.
          gbF_exit HK HD STRM MUL WML DP MD FU 11%Z 8%Z.
        }
      }
    }
  Qed.

  (* [comment removed for export] *)
  Lemma S0F_gb_1cdf8 : forall (Q : dres -> machine_state -> Prop), S0F_RET_OK A Q ->
    forall (F : nat) (L : dsv) (d : dst) (s : dstrm) (J : jk)
           (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte)
           (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 f200 f208 f216 : word) (pb : list byte),
    dmem DI_S0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J d s) ->
    S0FR A m j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 f200 f208 f216 pb ->
    stk s0segs m (a_lo A) (usp + -336) ->
    munch W (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J d s ->
    (0 <= sv_nblock L <= 900000)%Z ->
    fuel_ok F d s ->
    (forall (F1 : nat) (bb' bl' : Z) (inp' : list Z) (tin' : Z) (til' tih' : word) (m' : word -> option byte) (wb : word),
       let d2 := gbst d 44 bb' bl' in
       let s1 := DSTRM inp' (s_out s) (s_avail_out s) tin' (s_tout s) in
       drun F 44 L d s = dgo F1 (gb_after 44 (gbval bb' bl' 8) L (d_set_bsLive d2 (bl' - 8)) s1) ->
       fuel_ok F1 (d_set_bsLive d2 (bl' - 8)) s1 -> (F1 < F)%nat ->
       dmem DI_S0 cx (a_g1 A) (a_sv A) (a_payload A) m' (dvF cx (jk_set_t J til' tih') d2 s1) ->
       S0FR A m' j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 f200 f208 f216 pb ->
       stk s0segs m' (a_lo A) (usp + -336) ->
       munch W (a_m0 A) m' -> wmono s0segs (a_m0 A) m' -> mem_inv s0segs m' ->
       dpureF cx (a_b0 A) (a_payload A) (jk_set_t J til' tih') d2 s1 ->
       (0 <= bb' < 2^32)%Z -> (8 <= bl' <= 32)%Z -> (bv_unsigned wb mod 4294967296 = bb')%Z ->
       (8 * Z.of_nat (length inp') + bl' = 8 * Z.of_nat (length (s_in s)) + d_bsLive d)%Z ->
       forall (y12 y13 y14 y15 y16 y17 : word),
       evt s0segs (Q (drun F 44 L d s))
         (MS (mkR x1 (Z_to_bv 64 (usp + -336)) (a_gp A) (a_tp A) x5 x6 x7 x8 x9 (Z_to_bv 64 (bl' - 8)) wb y12 y13 y14 y15 y16 y17
                 (Z_to_bv 64 S) x19 (Z_to_bv 64 (S + 64036)) x21 (Z_to_bv 64 (sv_nblock L)) x23 x24 x25 x26 x27 x28 x29 x30 x31)
             (a_F A) (Z_to_bv 64 0x25a40) (a_fc A) None m' (seg_rom s0segs))) ->
    evt s0segs (Q (drun F 44 L d s))
      (MS (mkR x1 (Z_to_bv 64 (usp + -336)) (a_gp A) (a_tp A) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
                 (Z_to_bv 64 S) x19 (Z_to_bv 64 (S + 64036)) x21 (Z_to_bv 64 (sv_nblock L)) x23 x24 x25 x26 x27 x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0x2598c) (a_fc A) None m (seg_rom s0segs)).
  Proof.
    intros Q HRET. intros until pb. intros DM FR ST MU WM MI DP NB FU HK.
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN. pose proof rnums_words_length as RNL. lin_natZ RNL.
    unfold W14, D14, DSTATE_SIZE in MU. cbn [app blk_ivls b_s b_strm] in MU.
    destruct s as [inp sout sav stin stout]. cbn [s_in s_out s_avail_out s_tin s_tout] in *.
    pose proof DM as DM0. open_dmemF DM. s2img. cbn [s_in s_out s_avail_out s_tin s_tout] in *.
    destruct (fuel_ok_pos _ _ _ (proj1 (dpureF_bl _ _ _ _ _ _ DP)) FU) as [f EF]. subst F.
    pose proof (drun_gbst f 44 L d (DSTRM inp sout sav stin stout)) as MD. apply (fuel_ok_gbst _ _ 44) in FU.
    pose proof (dpureF_in _ _ _ _ _ _ DP) as IR.
    set (bl := d_bsLive d) in *. set (bb := d_bsBuff d) in *.
    hide_all_but (HD, STRM).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (munch_refl [(S, S + 68); (b_strm cx, b_strm cx + 20)]%Z mm) as MUL;
      pose proof (wmono_refl s0segs mm) as WML end.
    wstepl. wstepl. wstepl. wstepl.
    wstepl. if_cases K; zify_cond_z K.
    { (* [comment removed for export] *)
      wstepl. wstepl. wstepl. notrap. wstepl.
      gbF_exit HK HD STRM MUL WML DP MD FU 11%Z 8%Z.
    }
    { (* [comment removed for export] *)
      wstepl. wstepl. wstepl. wstepl. wstepl. wstepl.
      rewrite (strm_flag_ok cx (proj1 AOK)).
      wstepl. notrap.
      wstepl.
      wstepl. if_cases K2; zify_cond K2.
      { (* [comment removed for export] *)
        assert (inp = []) as -> by (lin_unbox LIN; destruct inp; [reflexivity| exfalso; cbn [length] in K2, LIN; rewrite Nat2Z.inj_succ in K2, LIN; clear -K2 LIN; zb_masks; mlia]). clear K2.
        gbF_ret HRET MUL WML DP MD NB 8%Z.
      }
      { (* [comment removed for export] *)
        assert (AI1 : (1 <= Z.of_nat (length inp))%Z) by (lin_unbox LIN; clear - K2 LIN; zb_masks; mlia). clear K2. destruct inp as [|bz inp1]; [exfalso; cbn in AI1; lia|]. destruct (in_rel_head (a_payload A) _ _ _ IR eq_refl) as [b8 [NTH Ebz]]. cbn [s_in length] in NTH. cbn [length] in *. rewrite Nat2Z.inj_succ in *. subst bz.
        wstepl. wstepl. notrap.
        wstepl.
        pose proof PAY as PAYL. revive PAYL MUL WML AOK.
        pose proof (u8ro_read s0segs _ (b_src cx) (a_payload A) (b_len cx - Z.succ (Z.of_nat (length inp1)))%Z b8 _ PAYL ltac:(rewrite <- NTH; f_equal; lia) ltac:(lia) eq_refl) as RD.
        (let pv := reg_val 15%Z in lazymatch pv with Z_to_bv 64 ?e => replace e with (b_src cx + (b_len cx - Z.succ (Z.of_nat (length inp1))))%Z by lia end).
        wstepl. clear RD PAYL.
        wstepl. wstepl. wstepl. wstepl. wstepl.
        wstepl. notrap.
        wstepl. forget_reg 16%Z wtil.
        wstepl. wstepl. wstepl. forget_reg 16%Z wtil2. wstepl. wstepl. wstepl.
        (* [comment removed for export] *)
        cell_mod32 HD 32%nat. change (2^32)%Z with 4294967296%Z in HD. rewrite (pullw_mod32 bb b8) in HD by lia.
        set (bb1 := u32 (Z.lor (Z.shiftl bb 8) (bv_unsigned b8))) in *.
        pose proof (u32_range' (Z.lor (Z.shiftl bb 8) (bv_unsigned b8))) as Rbb1. change (u32 _) with bb1 in Rbb1.
        replace (b_src cx + (b_len cx - Z.succ (Z.of_nat (length inp1))) + 1)%Z with (b_src cx + (b_len cx - Z.of_nat (length inp1)))%Z in STRM by lia.
        replace (Z.succ (Z.of_nat (length inp1)) + -1)%Z with (Z.of_nat (length inp1)) in STRM by lia.
        erewrite (drun_pull_D _ _ _ _ _ _ 8%Z) in MD by first [reflexivity | cbn; lia]. change (u32 _) with bb1 in MD.
        apply (fuel_ok_pull_D _ _ _ _ _ bb1 _ _ _ _ _ (stin + 1)) in FU.
        destruct (fuel_ok_gbst_S _ _ _ _ _ _ FU ltac:(lia)) as [f1 Ef1]. subst f.
        pose proof (in_rel_tail _ _ (DSTRM inp1 sout sav (stin + 1) stout) _ _ IR eq_refl eq_refl) as IR1.
        wstepl. if_cases K3.
        { (* [comment removed for export] *)
          wstepl. wstepl. if_false_z.
          wstepl. wstepl. wstepl. notrap. wstepl.
          gbF_exit HK HD STRM MUL WML DP MD FU 11%Z 8%Z.
        }
        { (* [comment removed for export] *)
          wstepl. forget_reg 14%Z wtih. wstepl. wstepl.
          wstepl. wstepl. if_false_z.
          wstepl. wstepl. wstepl. notrap. wstepl.
          gbF_exit HK HD STRM MUL WML DP MD FU 11%Z 8%Z.
        }
      }
    }
  Qed.

  (* [comment removed for export] *)
  Lemma S0F_gb_1ce94 : forall (Q : dres -> machine_state -> Prop), S0F_RET_OK A Q ->
    forall (F : nat) (L : dsv) (d : dst) (s : dstrm) (J : jk)
           (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte)
           (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 f200 f208 f216 : word) (pb : list byte),
    dmem DI_S0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J d s) ->
    S0FR A m j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 f200 f208 f216 pb ->
    stk s0segs m (a_lo A) (usp + -336) ->
    munch W (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J d s ->
    (0 <= sv_nblock L <= 900000)%Z ->
    fuel_ok F d s ->
    (forall (F1 : nat) (bb' bl' : Z) (inp' : list Z) (tin' : Z) (til' tih' : word) (m' : word -> option byte) (wb : word),
       let d2 := gbst d 45 bb' bl' in
       let s1 := DSTRM inp' (s_out s) (s_avail_out s) tin' (s_tout s) in
       drun F 45 L d s = dgo F1 (gb_after 45 (gbval bb' bl' 8) L (d_set_bsLive d2 (bl' - 8)) s1) ->
       fuel_ok F1 (d_set_bsLive d2 (bl' - 8)) s1 -> (F1 < F)%nat ->
       dmem DI_S0 cx (a_g1 A) (a_sv A) (a_payload A) m' (dvF cx (jk_set_t J til' tih') d2 s1) ->
       S0FR A m' j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 f200 f208 f216 pb ->
       stk s0segs m' (a_lo A) (usp + -336) ->
       munch W (a_m0 A) m' -> wmono s0segs (a_m0 A) m' -> mem_inv s0segs m' ->
       dpureF cx (a_b0 A) (a_payload A) (jk_set_t J til' tih') d2 s1 ->
       (0 <= bb' < 2^32)%Z -> (8 <= bl' <= 32)%Z -> (bv_unsigned wb mod 4294967296 = bb')%Z ->
       (8 * Z.of_nat (length inp') + bl' = 8 * Z.of_nat (length (s_in s)) + d_bsLive d)%Z ->
       forall (y12 y13 y14 y15 y16 y17 : word),
       evt s0segs (Q (drun F 45 L d s))
         (MS (mkR x1 (Z_to_bv 64 (usp + -336)) (a_gp A) (a_tp A) x5 x6 x7 x8 x9 (Z_to_bv 64 (bl' - 8)) wb y12 y13 y14 y15 y16 y17
                 (Z_to_bv 64 S) x19 (Z_to_bv 64 (S + 64036)) x21 (Z_to_bv 64 (sv_nblock L)) x23 x24 x25 x26 x27 x28 x29 x30 x31)
             (a_F A) (Z_to_bv 64 0x25b08) (a_fc A) None m' (seg_rom s0segs))) ->
    evt s0segs (Q (drun F 45 L d s))
      (MS (mkR x1 (Z_to_bv 64 (usp + -336)) (a_gp A) (a_tp A) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
                 (Z_to_bv 64 S) x19 (Z_to_bv 64 (S + 64036)) x21 (Z_to_bv 64 (sv_nblock L)) x23 x24 x25 x26 x27 x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0x25a54) (a_fc A) None m (seg_rom s0segs)).
  Proof.
    intros Q HRET. intros until pb. intros DM FR ST MU WM MI DP NB FU HK.
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN. pose proof rnums_words_length as RNL. lin_natZ RNL.
    unfold W14, D14, DSTATE_SIZE in MU. cbn [app blk_ivls b_s b_strm] in MU.
    destruct s as [inp sout sav stin stout]. cbn [s_in s_out s_avail_out s_tin s_tout] in *.
    pose proof DM as DM0. open_dmemF DM. s2img. cbn [s_in s_out s_avail_out s_tin s_tout] in *.
    destruct (fuel_ok_pos _ _ _ (proj1 (dpureF_bl _ _ _ _ _ _ DP)) FU) as [f EF]. subst F.
    pose proof (drun_gbst f 45 L d (DSTRM inp sout sav stin stout)) as MD. apply (fuel_ok_gbst _ _ 45) in FU.
    pose proof (dpureF_in _ _ _ _ _ _ DP) as IR.
    set (bl := d_bsLive d) in *. set (bb := d_bsBuff d) in *.
    hide_all_but (HD, STRM).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (munch_refl [(S, S + 68); (b_strm cx, b_strm cx + 20)]%Z mm) as MUL;
      pose proof (wmono_refl s0segs mm) as WML end.
    wstepl. wstepl. wstepl. wstepl.
    wstepl. if_cases K; zify_cond_z K.
    { (* [comment removed for export] *)
      wstepl. wstepl. wstepl. notrap. wstepl.
      gbF_exit HK HD STRM MUL WML DP MD FU 11%Z 8%Z.
    }
    { (* [comment removed for export] *)
      wstepl. wstepl. wstepl. wstepl. wstepl. wstepl.
      rewrite (strm_flag_ok cx (proj1 AOK)).
      wstepl. notrap.
      wstepl.
      wstepl. if_cases K2; zify_cond K2.
      { (* [comment removed for export] *)
        assert (inp = []) as -> by (lin_unbox LIN; destruct inp; [reflexivity| exfalso; cbn [length] in K2, LIN; rewrite Nat2Z.inj_succ in K2, LIN; clear -K2 LIN; zb_masks; mlia]). clear K2.
        gbF_ret HRET MUL WML DP MD NB 8%Z.
      }
      { (* [comment removed for export] *)
        assert (AI1 : (1 <= Z.of_nat (length inp))%Z) by (lin_unbox LIN; clear - K2 LIN; zb_masks; mlia). clear K2. destruct inp as [|bz inp1]; [exfalso; cbn in AI1; lia|]. destruct (in_rel_head (a_payload A) _ _ _ IR eq_refl) as [b8 [NTH Ebz]]. cbn [s_in length] in NTH. cbn [length] in *. rewrite Nat2Z.inj_succ in *. subst bz.
        wstepl. wstepl. notrap.
        wstepl.
        pose proof PAY as PAYL. revive PAYL MUL WML AOK.
        pose proof (u8ro_read s0segs _ (b_src cx) (a_payload A) (b_len cx - Z.succ (Z.of_nat (length inp1)))%Z b8 _ PAYL ltac:(rewrite <- NTH; f_equal; lia) ltac:(lia) eq_refl) as RD.
        (let pv := reg_val 15%Z in lazymatch pv with Z_to_bv 64 ?e => replace e with (b_src cx + (b_len cx - Z.succ (Z.of_nat (length inp1))))%Z by lia end).
        wstepl. clear RD PAYL.
        wstepl. wstepl. wstepl. wstepl. wstepl.
        wstepl. notrap.
        wstepl. forget_reg 16%Z wtil.
        wstepl. wstepl. wstepl. forget_reg 16%Z wtil2. wstepl. wstepl. wstepl.
        (* [comment removed for export] *)
        cell_mod32 HD 32%nat. change (2^32)%Z with 4294967296%Z in HD. rewrite (pullw_mod32 bb b8) in HD by lia.
        set (bb1 := u32 (Z.lor (Z.shiftl bb 8) (bv_unsigned b8))) in *.
        pose proof (u32_range' (Z.lor (Z.shiftl bb 8) (bv_unsigned b8))) as Rbb1. change (u32 _) with bb1 in Rbb1.
        replace (b_src cx + (b_len cx - Z.succ (Z.of_nat (length inp1))) + 1)%Z with (b_src cx + (b_len cx - Z.of_nat (length inp1)))%Z in STRM by lia.
        replace (Z.succ (Z.of_nat (length inp1)) + -1)%Z with (Z.of_nat (length inp1)) in STRM by lia.
        erewrite (drun_pull_D _ _ _ _ _ _ 8%Z) in MD by first [reflexivity | cbn; lia]. change (u32 _) with bb1 in MD.
        apply (fuel_ok_pull_D _ _ _ _ _ bb1 _ _ _ _ _ (stin + 1)) in FU.
        destruct (fuel_ok_gbst_S _ _ _ _ _ _ FU ltac:(lia)) as [f1 Ef1]. subst f.
        pose proof (in_rel_tail _ _ (DSTRM inp1 sout sav (stin + 1) stout) _ _ IR eq_refl eq_refl) as IR1.
        wstepl. if_cases K3.
        { (* [comment removed for export] *)
          wstepl. wstepl. if_false_z.
          wstepl. wstepl. wstepl. notrap. wstepl.
          gbF_exit HK HD STRM MUL WML DP MD FU 11%Z 8%Z.
        }
        { (* [comment removed for export] *)
          wstepl. forget_reg 14%Z wtih. wstepl. wstepl.
          wstepl. wstepl. if_false_z.
          wstepl. wstepl. wstepl. notrap. wstepl.
          gbF_exit HK HD STRM MUL WML DP MD FU 11%Z 8%Z.
        }
      }
    }
  Qed.

End R.

End ACeilS1.
End S0F_gb_F.

From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require LinSplit. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require DecFast.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require NatLit.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzImg0TacF.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFastZ StoreFastC.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require NormFast. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require FLiaA.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require GbKit GbKitF.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require RangeFast RangeFastEnv.
Module S0F_gb_H.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.PropExec.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib.SegsS0.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzDefs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzModel OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzInv OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTables OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzContracts OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzContracts0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecCut OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_dec_U13.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpMem.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecCutF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decRet.
 Unset Lia Cache.
Import ListNotations. Local Open Scope bv_scope.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeil.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.LinSplit OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecFast.
Local Ltac DecCut.revive H MUL WML AOK ::= DecFast.revive_cached H MUL WML AOK.
Local Ltac DecCut.dpure_from DP ::= DecFast.dpure_from_fast DP.
Local Ltac DecCut.open_dmem DM ::= DecFast.open_dmem_red DM.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.NatLit.
Local Ltac Zify.zify_pre_hook ::= NatLit.natlen_ctx.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.StoreFast.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzImg0TacF.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
   (* [comment removed for export] *)
Local Ltac mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
(* [comment removed for export] *)

Local Ltac lia ::= FLiaA.lia_f.
Local Ltac BzTac.bz32 ::= NormFast.bz32_m.
Local Ltac BzTac2.bz32l ::= NormFast.bz32l_m.
Local Ltac Zify.zify_pre_hook ::= NormFast.nf_pre_natlen.
Local Ltac DecCutF.unset_Z ::= NormFast.unset_Z_subst.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
   (* [comment removed for export] *)
(* [comment removed for export] *)

Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)

#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section ACeilS1. Context {ACEIL__ : ACeil}.

Section R.
  Variable A : act14.
  Hypothesis AOK : act_ok 320 A.

  Notation usp := (bv_unsigned (a_sp A)).
  Notation cx := (a_cx A).
  Notation S := (b_s (a_cx A)).
  Notation W := (W14 DI_S0 (a_cx A) (bv_unsigned (a_sp A))).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Ltac gbF_close DP MUL WML :=
    lazymatch goal with DM0 : dmem _ _ _ _ _ _ _ |- dmem _ ?cx _ _ _ ?mm _ =>
      eapply (GbKitF.gbF_dmem_close _ _ AOK _ (GbKit.di_in_img_ok DI_S0 eq_refl) _ _ _ _ _ _ _ _ DM0 DP MUL WML);
      [ dvF_cbn; dmodel_cbn; match goal with H : rw_cells _ mm (b_s cx) _ |- _ => exact_cells H end
      | dvF_cbn; dmodel_cbn; match goal with H : rw_cells _ mm (b_strm cx) _ |- _ => exact_cells H end
      | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity ]
    end.
  Ltac cut_sideG MUL WML DP :=
    lazymatch goal with
    | |- dmem _ _ _ _ _ _ _ => first [ gbF_close DP MUL WML | revive_all MUL WML AOK; cut_sideF DP ]
    | |- rw_cells _ _ (bv_unsigned (a_sp _) + _)%Z _ =>      (* [comment removed for export] *)
        first [ cut_sideF DP
              | match goal with H : hidden (rw_cells _ _ (bv_unsigned (a_sp _) + _)%Z _) |- _ => revive H MUL WML AOK end; cut_sideF DP
              | revive_all MUL WML AOK; cut_sideF DP ]
    | |- _ => cut_sideF DP
    end.
  Ltac gbF_exit HK HD STRM MUL WML DP MD FU breg n :=
    lazymatch type of HD with rw_cells _ _ _ ?cs =>
      let c := eval cbv beta iota zeta delta [cell_at csize Nat.eqb Nat.ltb Nat.leb Nat.sub Nat.add] in (cell_at cs 32%nat) in
      lazymatch c with Some (C4 (Z_to_bv 64 ?bbx)) =>
        let w := fresh "wb" in gbword breg w bbx;
        [ first [ apply sx32_mod32; lia | apply pullw_reg32; lia ]
        | erewrite (drun_bits' _ _ _ _ _ _ _ n) in MD by first [reflexivity | cbn; lia];
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          eapply evt_eq; [ | eapply (HK _ _ _ _ _ _ _ mm _ MD) ]; only 1: unify_memF;
          [ | eapply fuel_ok_gbst_bits; [exact FU | cbn; lia] | try cut_sideG MUL WML DP .. ];
          [ dvF_cbn; dmodel_cbn; st_eq | try (cbn [length]; unset_Z; lia) .. ] end ]
      end end.
  (* [comment removed for export] *)
  Ltac gbF_ret HRET MUL WML DP MD NB n :=
    erewrite (drun_eof' _ _ _ _ _ _ _ n) in MD by first [reflexivity | cbn; lia];
    rewrite MD;
    (eapply evt_eq; [ | eapply (HRET _ _ _ (JK _ _ _ _ _ _ _ _ _ _ _ _ _ _)) ]; only 1: unify_memF; try cut_sideG MUL WML DP; only 1: (dvF_cbn; dmodel_cbn; st_eq)); [exact NB | apply dpost14_ne; dmodel_cbn; cbv; discriminate].
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma S0F_gb_1d118 : forall (Q : dres -> machine_state -> Prop), S0F_RET_OK A Q ->
    forall (F : nat) (L : dsv) (d : dst) (s : dstrm) (J : jk)
           (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte)
           (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 f200 f208 f216 : word) (pb : list byte),
    dmem DI_S0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J d s) ->
    S0FR A m j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 f200 f208 f216 pb ->
    stk s0segs m (a_lo A) (usp + -336) ->
    munch W (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J d s ->
    (0 <= sv_nblock L <= 900000)%Z ->
    fuel_ok F d s ->
    (forall (F1 : nat) (bb' bl' : Z) (inp' : list Z) (tin' : Z) (til' tih' : word) (m' : word -> option byte) (wb : word),
       let d2 := gbst d 49 bb' bl' in
       let s1 := DSTRM inp' (s_out s) (s_avail_out s) tin' (s_tout s) in
       drun F 49 L d s = dgo F1 (gb_after 49 (gbval bb' bl' 8) L (d_set_bsLive d2 (bl' - 8)) s1) ->
       fuel_ok F1 (d_set_bsLive d2 (bl' - 8)) s1 -> (F1 < F)%nat ->
       dmem DI_S0 cx (a_g1 A) (a_sv A) (a_payload A) m' (dvF cx (jk_set_t J til' tih') d2 s1) ->
       S0FR A m' j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 f200 f208 f216 pb ->
       stk s0segs m' (a_lo A) (usp + -336) ->
       munch W (a_m0 A) m' -> wmono s0segs (a_m0 A) m' -> mem_inv s0segs m' ->
       dpureF cx (a_b0 A) (a_payload A) (jk_set_t J til' tih') d2 s1 ->
       (0 <= bb' < 2^32)%Z -> (8 <= bl' <= 32)%Z -> (bv_unsigned wb mod 4294967296 = bb')%Z ->
       (8 * Z.of_nat (length inp') + bl' = 8 * Z.of_nat (length (s_in s)) + d_bsLive d)%Z ->
       forall (y12 y13 y14 y15 y16 y17 : word),
       evt s0segs (Q (drun F 49 L d s))
         (MS (mkR x1 (Z_to_bv 64 (usp + -336)) (a_gp A) (a_tp A) x5 x6 x7 x8 x9 (Z_to_bv 64 (bl' - 8)) wb y12 y13 y14 y15 y16 y17
                 (Z_to_bv 64 S) x19 (Z_to_bv 64 (S + 64036)) x21 (Z_to_bv 64 (sv_nblock L)) x23 x24 x25 x26 x27 x28 x29 x30 x31)
             (a_F A) (Z_to_bv 64 0x25e58) (a_fc A) None m' (seg_rom s0segs))) ->
    evt s0segs (Q (drun F 49 L d s))
      (MS (mkR x1 (Z_to_bv 64 (usp + -336)) (a_gp A) (a_tp A) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
                 (Z_to_bv 64 S) x19 (Z_to_bv 64 (S + 64036)) x21 (Z_to_bv 64 (sv_nblock L)) x23 x24 x25 x26 x27 x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0x25da0) (a_fc A) None m (seg_rom s0segs)).
  Proof.
    intros Q HRET. intros until pb. intros DM FR ST MU WM MI DP NB FU HK.
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN. pose proof rnums_words_length as RNL. lin_natZ RNL.
    unfold W14, D14, DSTATE_SIZE in MU. cbn [app blk_ivls b_s b_strm] in MU.
    destruct s as [inp sout sav stin stout]. cbn [s_in s_out s_avail_out s_tin s_tout] in *.
    pose proof DM as DM0. open_dmemF DM. s2img. cbn [s_in s_out s_avail_out s_tin s_tout] in *.
    destruct (fuel_ok_pos _ _ _ (proj1 (dpureF_bl _ _ _ _ _ _ DP)) FU) as [f EF]. subst F.
    pose proof (drun_gbst f 49 L d (DSTRM inp sout sav stin stout)) as MD. apply (fuel_ok_gbst _ _ 49) in FU.
    pose proof (dpureF_in _ _ _ _ _ _ DP) as IR.
    set (bl := d_bsLive d) in *. set (bb := d_bsBuff d) in *.
    hide_all_but (HD, STRM).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (munch_refl [(S, S + 68); (b_strm cx, b_strm cx + 20)]%Z mm) as MUL;
      pose proof (wmono_refl s0segs mm) as WML end.
    wstepl. wstepl. wstepl. wstepl.
    wstepl. if_cases K; zify_cond_z K.
    { (* [comment removed for export] *)
      wstepl. wstepl. wstepl. notrap. wstepl.
      gbF_exit HK HD STRM MUL WML DP MD FU 11%Z 8%Z.
    }
    { (* [comment removed for export] *)
      wstepl. wstepl. wstepl. wstepl. wstepl. wstepl.
      rewrite (strm_flag_ok cx (proj1 AOK)).
      wstepl. notrap.
      wstepl.
      wstepl. if_cases K2; zify_cond K2.
      { (* [comment removed for export] *)
        assert (AI1 : (1 <= Z.of_nat (length inp))%Z) by (lin_unbox LIN; clear - K2 LIN; zb_masks; mlia). clear K2. destruct inp as [|bz inp1]; [exfalso; cbn in AI1; lia|]. destruct (in_rel_head (a_payload A) _ _ _ IR eq_refl) as [b8 [NTH Ebz]]. cbn [s_in length] in NTH. cbn [length] in *. rewrite Nat2Z.inj_succ in *. subst bz.
        wstepl. wstepl. notrap.
        wstepl.
        pose proof PAY as PAYL. revive PAYL MUL WML AOK.
        pose proof (u8ro_read s0segs _ (b_src cx) (a_payload A) (b_len cx - Z.succ (Z.of_nat (length inp1)))%Z b8 _ PAYL ltac:(rewrite <- NTH; f_equal; lia) ltac:(lia) eq_refl) as RD.
        (let pv := reg_val 15%Z in lazymatch pv with Z_to_bv 64 ?e => replace e with (b_src cx + (b_len cx - Z.succ (Z.of_nat (length inp1))))%Z by lia end).
        wstepl. clear RD PAYL.
        wstepl. wstepl. wstepl. wstepl. wstepl.
        wstepl. notrap.
        wstepl. forget_reg 16%Z wtil.
        wstepl. wstepl. wstepl. forget_reg 16%Z wtil2. wstepl. wstepl. wstepl.
        (* [comment removed for export] *)
        cell_mod32 HD 32%nat. change (2^32)%Z with 4294967296%Z in HD. rewrite (pullw_mod32 bb b8) in HD by lia.
        set (bb1 := u32 (Z.lor (Z.shiftl bb 8) (bv_unsigned b8))) in *.
        pose proof (u32_range' (Z.lor (Z.shiftl bb 8) (bv_unsigned b8))) as Rbb1. change (u32 _) with bb1 in Rbb1.
        replace (b_src cx + (b_len cx - Z.succ (Z.of_nat (length inp1))) + 1)%Z with (b_src cx + (b_len cx - Z.of_nat (length inp1)))%Z in STRM by lia.
        replace (Z.succ (Z.of_nat (length inp1)) + -1)%Z with (Z.of_nat (length inp1)) in STRM by lia.
        erewrite (drun_pull_D _ _ _ _ _ _ 8%Z) in MD by first [reflexivity | cbn; lia]. change (u32 _) with bb1 in MD.
        apply (fuel_ok_pull_D _ _ _ _ _ bb1 _ _ _ _ _ (stin + 1)) in FU.
        destruct (fuel_ok_gbst_S _ _ _ _ _ _ FU ltac:(lia)) as [f1 Ef1]. subst f.
        pose proof (in_rel_tail _ _ (DSTRM inp1 sout sav (stin + 1) stout) _ _ IR eq_refl eq_refl) as IR1.
        wstepl. if_cases K3.
        { (* [comment removed for export] *)
          wstepl. wstepl. if_false_z.
          wstepl. wstepl. wstepl. notrap. wstepl.
          gbF_exit HK HD STRM MUL WML DP MD FU 11%Z 8%Z.
        }
        { (* [comment removed for export] *)
          wstepl. forget_reg 14%Z wtih. wstepl. wstepl.
          wstepl. wstepl. if_false_z.
          wstepl. wstepl. wstepl. notrap. wstepl.
          gbF_exit HK HD STRM MUL WML DP MD FU 11%Z 8%Z.
        }
      }
      { (* [comment removed for export] *)
        assert (inp = []) as -> by (lin_unbox LIN; destruct inp; [reflexivity| exfalso; cbn [length] in K2, LIN; rewrite Nat2Z.inj_succ in K2, LIN; clear -K2 LIN; zb_masks; mlia]). clear K2.
        wstepl.
        gbF_ret HRET MUL WML DP MD NB 8%Z.
      }
    }
  Qed.

  (* [comment removed for export] *)
  Lemma S0F_gb_1d1bc : forall (Q : dres -> machine_state -> Prop), S0F_RET_OK A Q ->
    forall (F : nat) (L : dsv) (d : dst) (s : dstrm) (J : jk)
           (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte)
           (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 f200 f208 f216 : word) (pb : list byte),
    dmem DI_S0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J d s) ->
    S0FR A m j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 f200 f208 f216 pb ->
    stk s0segs m (a_lo A) (usp + -336) ->
    munch W (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J d s ->
    (0 <= sv_nblock L <= 900000)%Z ->
    fuel_ok F d s ->
    (forall (F1 : nat) (bb' bl' : Z) (inp' : list Z) (tin' : Z) (til' tih' : word) (m' : word -> option byte) (wb : word),
       let d2 := gbst d 50 bb' bl' in
       let s1 := DSTRM inp' (s_out s) (s_avail_out s) tin' (s_tout s) in
       drun F 50 L d s = dgo F1 (gb_after 50 (gbval bb' bl' 8) L (d_set_bsLive d2 (bl' - 8)) s1) ->
       fuel_ok F1 (d_set_bsLive d2 (bl' - 8)) s1 -> (F1 < F)%nat ->
       dmem DI_S0 cx (a_g1 A) (a_sv A) (a_payload A) m' (dvF cx (jk_set_t J til' tih') d2 s1) ->
       S0FR A m' j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 f200 f208 f216 pb ->
       stk s0segs m' (a_lo A) (usp + -336) ->
       munch W (a_m0 A) m' -> wmono s0segs (a_m0 A) m' -> mem_inv s0segs m' ->
       dpureF cx (a_b0 A) (a_payload A) (jk_set_t J til' tih') d2 s1 ->
       (0 <= bb' < 2^32)%Z -> (8 <= bl' <= 32)%Z -> (bv_unsigned wb mod 4294967296 = bb')%Z ->
       (8 * Z.of_nat (length inp') + bl' = 8 * Z.of_nat (length (s_in s)) + d_bsLive d)%Z ->
       forall (y12 y13 y14 y15 y16 y17 : word),
       evt s0segs (Q (drun F 50 L d s))
         (MS (mkR x1 (Z_to_bv 64 (usp + -336)) (a_gp A) (a_tp A) x5 x6 x7 x8 x9 (Z_to_bv 64 (bl' - 8)) wb y12 y13 y14 y15 y16 y17
                 (Z_to_bv 64 S) x19 (Z_to_bv 64 (S + 64036)) x21 (Z_to_bv 64 (sv_nblock L)) x23 x24 x25 x26 x27 x28 x29 x30 x31)
             (a_F A) (Z_to_bv 64 0x25f30) (a_fc A) None m' (seg_rom s0segs))) ->
    evt s0segs (Q (drun F 50 L d s))
      (MS (mkR x1 (Z_to_bv 64 (usp + -336)) (a_gp A) (a_tp A) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
                 (Z_to_bv 64 S) x19 (Z_to_bv 64 (S + 64036)) x21 (Z_to_bv 64 (sv_nblock L)) x23 x24 x25 x26 x27 x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0x25e78) (a_fc A) None m (seg_rom s0segs)).
  Proof.
    intros Q HRET. intros until pb. intros DM FR ST MU WM MI DP NB FU HK.
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN. pose proof rnums_words_length as RNL. lin_natZ RNL.
    unfold W14, D14, DSTATE_SIZE in MU. cbn [app blk_ivls b_s b_strm] in MU.
    destruct s as [inp sout sav stin stout]. cbn [s_in s_out s_avail_out s_tin s_tout] in *.
    pose proof DM as DM0. open_dmemF DM. s2img. cbn [s_in s_out s_avail_out s_tin s_tout] in *.
    destruct (fuel_ok_pos _ _ _ (proj1 (dpureF_bl _ _ _ _ _ _ DP)) FU) as [f EF]. subst F.
    pose proof (drun_gbst f 50 L d (DSTRM inp sout sav stin stout)) as MD. apply (fuel_ok_gbst _ _ 50) in FU.
    pose proof (dpureF_in _ _ _ _ _ _ DP) as IR.
    set (bl := d_bsLive d) in *. set (bb := d_bsBuff d) in *.
    hide_all_but (HD, STRM).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (munch_refl [(S, S + 68); (b_strm cx, b_strm cx + 20)]%Z mm) as MUL;
      pose proof (wmono_refl s0segs mm) as WML end.
    wstepl. wstepl. wstepl. wstepl.
    wstepl. if_cases K; zify_cond_z K.
    { (* [comment removed for export] *)
      wstepl. wstepl. wstepl. notrap. wstepl.
      gbF_exit HK HD STRM MUL WML DP MD FU 11%Z 8%Z.
    }
    { (* [comment removed for export] *)
      wstepl. wstepl. wstepl. wstepl. wstepl. wstepl.
      rewrite (strm_flag_ok cx (proj1 AOK)).
      wstepl. notrap.
      wstepl.
      wstepl. if_cases K2; zify_cond K2.
      { (* [comment removed for export] *)
        assert (AI1 : (1 <= Z.of_nat (length inp))%Z) by (lin_unbox LIN; clear - K2 LIN; zb_masks; mlia). clear K2. destruct inp as [|bz inp1]; [exfalso; cbn in AI1; lia|]. destruct (in_rel_head (a_payload A) _ _ _ IR eq_refl) as [b8 [NTH Ebz]]. cbn [s_in length] in NTH. cbn [length] in *. rewrite Nat2Z.inj_succ in *. subst bz.
        wstepl. wstepl. notrap.
        wstepl.
        pose proof PAY as PAYL. revive PAYL MUL WML AOK.
        pose proof (u8ro_read s0segs _ (b_src cx) (a_payload A) (b_len cx - Z.succ (Z.of_nat (length inp1)))%Z b8 _ PAYL ltac:(rewrite <- NTH; f_equal; lia) ltac:(lia) eq_refl) as RD.
        (let pv := reg_val 15%Z in lazymatch pv with Z_to_bv 64 ?e => replace e with (b_src cx + (b_len cx - Z.succ (Z.of_nat (length inp1))))%Z by lia end).
        wstepl. clear RD PAYL.
        wstepl. wstepl. wstepl. wstepl. wstepl.
        wstepl. notrap.
        wstepl. forget_reg 16%Z wtil.
        wstepl. wstepl. wstepl. forget_reg 16%Z wtil2. wstepl. wstepl. wstepl.
        (* [comment removed for export] *)
        cell_mod32 HD 32%nat. change (2^32)%Z with 4294967296%Z in HD. rewrite (pullw_mod32 bb b8) in HD by lia.
        set (bb1 := u32 (Z.lor (Z.shiftl bb 8) (bv_unsigned b8))) in *.
        pose proof (u32_range' (Z.lor (Z.shiftl bb 8) (bv_unsigned b8))) as Rbb1. change (u32 _) with bb1 in Rbb1.
        replace (b_src cx + (b_len cx - Z.succ (Z.of_nat (length inp1))) + 1)%Z with (b_src cx + (b_len cx - Z.of_nat (length inp1)))%Z in STRM by lia.
        replace (Z.succ (Z.of_nat (length inp1)) + -1)%Z with (Z.of_nat (length inp1)) in STRM by lia.
        erewrite (drun_pull_D _ _ _ _ _ _ 8%Z) in MD by first [reflexivity | cbn; lia]. change (u32 _) with bb1 in MD.
        apply (fuel_ok_pull_D _ _ _ _ _ bb1 _ _ _ _ _ (stin + 1)) in FU.
        destruct (fuel_ok_gbst_S _ _ _ _ _ _ FU ltac:(lia)) as [f1 Ef1]. subst f.
        pose proof (in_rel_tail _ _ (DSTRM inp1 sout sav (stin + 1) stout) _ _ IR eq_refl eq_refl) as IR1.
        wstepl. if_cases K3.
        { (* [comment removed for export] *)
          wstepl. wstepl. if_false_z.
          wstepl. wstepl. wstepl. notrap. wstepl.
          gbF_exit HK HD STRM MUL WML DP MD FU 11%Z 8%Z.
        }
        { (* [comment removed for export] *)
          wstepl. forget_reg 14%Z wtih. wstepl. wstepl.
          wstepl. wstepl. if_false_z.
          wstepl. wstepl. wstepl. notrap. wstepl.
          gbF_exit HK HD STRM MUL WML DP MD FU 11%Z 8%Z.
        }
      }
      { (* [comment removed for export] *)
        assert (inp = []) as -> by (lin_unbox LIN; destruct inp; [reflexivity| exfalso; cbn [length] in K2, LIN; rewrite Nat2Z.inj_succ in K2, LIN; clear -K2 LIN; zb_masks; mlia]). clear K2.
        wstepl.
        gbF_ret HRET MUL WML DP MD NB 8%Z.
      }
    }
  Qed.

End R.

End ACeilS1.
End S0F_gb_H.

Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import LinSplit. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import DecFast.
Local Ltac DecCut.revive H MUL WML AOK ::= DecFast.revive_cached H MUL WML AOK.
Local Ltac DecCut.dpure_from DP ::= DecFast.dpure_from_fast DP.
Local Ltac DecCut.open_dmem DM ::= DecFast.open_dmem_red DM.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import NatLit.
Local Ltac Zify.zify_pre_hook ::= NatLit.natlen_ctx.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzImg0TacF.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFastZ StoreFastC.   (* [comment removed for export] *)
Local Ltac mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require NormFast. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require FLiaA.
Local Ltac lia ::= FLiaA.lia_f.
Local Ltac BzTac.bz32 ::= NormFast.bz32_m.
Local Ltac BzTac2.bz32l ::= NormFast.bz32l_m.
Local Ltac Zify.zify_pre_hook ::= NormFast.nf_pre_natlen.
Local Ltac DecCutF.unset_Z ::= NormFast.unset_Z_subst.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require GbKit GbKitF.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section ACeilS1. Context {ACEIL__ : ACeil}.

Section R.
  Variable A : act14.
  Hypothesis AOK : act_ok 320 A.

  Notation usp := (bv_unsigned (a_sp A)).
  Notation cx := (a_cx A).
  Notation S := (b_s (a_cx A)).
  Notation W := (W14 DI_S0 (a_cx A) (bv_unsigned (a_sp A))).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Ltac gbF_close DP MUL WML :=
    lazymatch goal with DM0 : dmem _ _ _ _ _ _ _ |- dmem _ ?cx _ _ _ ?mm _ =>
      eapply (GbKitF.gbF_dmem_close _ _ AOK _ (GbKit.di_in_img_ok DI_S0 eq_refl) _ _ _ _ _ _ _ _ DM0 DP MUL WML);
      [ dvF_cbn; dmodel_cbn; match goal with H : rw_cells _ mm (b_s cx) _ |- _ => exact_cells H end
      | dvF_cbn; dmodel_cbn; match goal with H : rw_cells _ mm (b_strm cx) _ |- _ => exact_cells H end
      | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity ]
    end.
  Ltac cut_sideG MUL WML DP :=
    lazymatch goal with
    | |- dmem _ _ _ _ _ _ _ => first [ gbF_close DP MUL WML | revive_all MUL WML AOK; cut_sideF DP ]
    | |- rw_cells _ _ (bv_unsigned (a_sp _) + _)%Z _ =>      (* [comment removed for export] *)
        first [ cut_sideF DP
              | match goal with H : hidden (rw_cells _ _ (bv_unsigned (a_sp _) + _)%Z _) |- _ => revive H MUL WML AOK end; cut_sideF DP
              | revive_all MUL WML AOK; cut_sideF DP ]
    | |- _ => cut_sideF DP
    end.
  Ltac gbF_exit HK HD STRM MUL WML DP MD FU breg n :=
    lazymatch type of HD with rw_cells _ _ _ ?cs =>
      let c := eval cbv beta iota zeta delta [cell_at csize Nat.eqb Nat.ltb Nat.leb Nat.sub Nat.add] in (cell_at cs 32%nat) in
      lazymatch c with Some (C4 (Z_to_bv 64 ?bbx)) =>
        let w := fresh "wb" in gbword breg w bbx;
        [ first [ apply sx32_mod32; lia | apply pullw_reg32; lia ]
        | erewrite (drun_bits' _ _ _ _ _ _ _ n) in MD by first [reflexivity | cbn; lia];
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          eapply evt_eq; [ | eapply (HK _ _ _ _ _ _ _ mm _ MD) ]; only 1: unify_memF;
          [ | eapply fuel_ok_gbst_bits; [exact FU | cbn; lia] | try cut_sideG MUL WML DP .. ];
          [ dvF_cbn; dmodel_cbn; st_eq | try (cbn [length]; unset_Z; lia) .. ] end ]
      end end.
  (* [comment removed for export] *)
  Ltac gbF_ret HRET MUL WML DP MD NB n :=
    erewrite (drun_eof' _ _ _ _ _ _ _ n) in MD by first [reflexivity | cbn; lia];
    rewrite MD;
    (eapply evt_eq; [ | eapply (HRET _ _ _ (JK _ _ _ _ _ _ _ _ _ _ _ _ _ _)) ]; only 1: unify_memF; try cut_sideG MUL WML DP; only 1: (dvF_cbn; dmodel_cbn; st_eq)); [exact NB | apply dpost14_ne; dmodel_cbn; cbv; discriminate].
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma S0F_gb_1cf30 : forall (Q : dres -> machine_state -> Prop), S0F_RET_OK A Q ->
    forall (F : nat) (L : dsv) (d : dst) (s : dstrm) (J : jk)
           (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte)
           (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 f200 f208 f216 : word) (pb : list byte),
    dmem DI_S0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J d s) ->
    S0FR A m j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 f200 f208 f216 pb ->
    stk s0segs m (a_lo A) (usp + -336) ->
    munch W (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J d s ->
    (0 <= sv_nblock L <= 900000)%Z ->
    fuel_ok F d s ->
    (forall (F1 : nat) (bb' bl' : Z) (inp' : list Z) (tin' : Z) (til' tih' : word) (m' : word -> option byte) (wb : word),
       let d2 := gbst d 46 bb' bl' in
       let s1 := DSTRM inp' (s_out s) (s_avail_out s) tin' (s_tout s) in
       drun F 46 L d s = dgo F1 (gb_after 46 (gbval bb' bl' 8) L (d_set_bsLive d2 (bl' - 8)) s1) ->
       fuel_ok F1 (d_set_bsLive d2 (bl' - 8)) s1 -> (F1 < F)%nat ->
       dmem DI_S0 cx (a_g1 A) (a_sv A) (a_payload A) m' (dvF cx (jk_set_t J til' tih') d2 s1) ->
       S0FR A m' j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 f200 f208 f216 pb ->
       stk s0segs m' (a_lo A) (usp + -336) ->
       munch W (a_m0 A) m' -> wmono s0segs (a_m0 A) m' -> mem_inv s0segs m' ->
       dpureF cx (a_b0 A) (a_payload A) (jk_set_t J til' tih') d2 s1 ->
       (0 <= bb' < 2^32)%Z -> (8 <= bl' <= 32)%Z -> (bv_unsigned wb mod 4294967296 = bb')%Z ->
       (8 * Z.of_nat (length inp') + bl' = 8 * Z.of_nat (length (s_in s)) + d_bsLive d)%Z ->
       forall (y12 y13 y14 y15 y16 y17 : word),
       evt s0segs (Q (drun F 46 L d s))
         (MS (mkR x1 (Z_to_bv 64 (usp + -336)) (a_gp A) (a_tp A) x5 x6 x7 x8 x9 (Z_to_bv 64 (bl' - 8)) wb y12 y13 y14 y15 y16 y17
                 (Z_to_bv 64 S) x19 (Z_to_bv 64 (S + 64036)) x21 (Z_to_bv 64 (sv_nblock L)) x23 x24 x25 x26 x27 x28 x29 x30 x31)
             (a_F A) (Z_to_bv 64 0x25bd4) (a_fc A) None m' (seg_rom s0segs))) ->
    evt s0segs (Q (drun F 46 L d s))
      (MS (mkR x1 (Z_to_bv 64 (usp + -336)) (a_gp A) (a_tp A) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
                 (Z_to_bv 64 S) x19 (Z_to_bv 64 (S + 64036)) x21 (Z_to_bv 64 (sv_nblock L)) x23 x24 x25 x26 x27 x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0x25b1c) (a_fc A) None m (seg_rom s0segs)).
  Proof.
    intros Q HRET. intros until pb. intros DM FR ST MU WM MI DP NB FU HK.
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN. pose proof rnums_words_length as RNL. lin_natZ RNL.
    unfold W14, D14, DSTATE_SIZE in MU. cbn [app blk_ivls b_s b_strm] in MU.
    destruct s as [inp sout sav stin stout]. cbn [s_in s_out s_avail_out s_tin s_tout] in *.
    pose proof DM as DM0. open_dmemF DM. s2img. cbn [s_in s_out s_avail_out s_tin s_tout] in *.
    destruct (fuel_ok_pos _ _ _ (proj1 (dpureF_bl _ _ _ _ _ _ DP)) FU) as [f EF]. subst F.
    pose proof (drun_gbst f 46 L d (DSTRM inp sout sav stin stout)) as MD. apply (fuel_ok_gbst _ _ 46) in FU.
    pose proof (dpureF_in _ _ _ _ _ _ DP) as IR.
    set (bl := d_bsLive d) in *. set (bb := d_bsBuff d) in *.
    hide_all_but (HD, STRM).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (munch_refl [(S, S + 68); (b_strm cx, b_strm cx + 20)]%Z mm) as MUL;
      pose proof (wmono_refl s0segs mm) as WML end.
    wstepl. wstepl. wstepl. wstepl.
    wstepl. if_cases K; zify_cond_z K.
    { (* [comment removed for export] *)
      wstepl. wstepl. wstepl. notrap. wstepl.
      gbF_exit HK HD STRM MUL WML DP MD FU 11%Z 8%Z.
    }
    { (* [comment removed for export] *)
      wstepl. wstepl. wstepl. wstepl. wstepl. wstepl.
      rewrite (strm_flag_ok cx (proj1 AOK)).
      wstepl. notrap.
      wstepl.
      wstepl. if_cases K2; zify_cond K2.
      { (* [comment removed for export] *)
        assert (AI1 : (1 <= Z.of_nat (length inp))%Z) by (lin_unbox LIN; clear - K2 LIN; zb_masks; mlia). clear K2. destruct inp as [|bz inp1]; [exfalso; cbn in AI1; lia|]. destruct (in_rel_head (a_payload A) _ _ _ IR eq_refl) as [b8 [NTH Ebz]]. cbn [s_in length] in NTH. cbn [length] in *. rewrite Nat2Z.inj_succ in *. subst bz.
        wstepl. wstepl. notrap.
        wstepl.
        pose proof PAY as PAYL. revive PAYL MUL WML AOK.
        pose proof (u8ro_read s0segs _ (b_src cx) (a_payload A) (b_len cx - Z.succ (Z.of_nat (length inp1)))%Z b8 _ PAYL ltac:(rewrite <- NTH; f_equal; lia) ltac:(lia) eq_refl) as RD.
        (let pv := reg_val 15%Z in lazymatch pv with Z_to_bv 64 ?e => replace e with (b_src cx + (b_len cx - Z.succ (Z.of_nat (length inp1))))%Z by lia end).
        wstepl. clear RD PAYL.
        wstepl. wstepl. wstepl. wstepl. wstepl.
        wstepl. notrap.
        wstepl. forget_reg 16%Z wtil.
        wstepl. wstepl. wstepl. forget_reg 16%Z wtil2. wstepl. wstepl. wstepl.
        (* [comment removed for export] *)
        cell_mod32 HD 32%nat. change (2^32)%Z with 4294967296%Z in HD. rewrite (pullw_mod32 bb b8) in HD by lia.
        set (bb1 := u32 (Z.lor (Z.shiftl bb 8) (bv_unsigned b8))) in *.
        pose proof (u32_range' (Z.lor (Z.shiftl bb 8) (bv_unsigned b8))) as Rbb1. change (u32 _) with bb1 in Rbb1.
        replace (b_src cx + (b_len cx - Z.succ (Z.of_nat (length inp1))) + 1)%Z with (b_src cx + (b_len cx - Z.of_nat (length inp1)))%Z in STRM by lia.
        replace (Z.succ (Z.of_nat (length inp1)) + -1)%Z with (Z.of_nat (length inp1)) in STRM by lia.
        erewrite (drun_pull_D _ _ _ _ _ _ 8%Z) in MD by first [reflexivity | cbn; lia]. change (u32 _) with bb1 in MD.
        apply (fuel_ok_pull_D _ _ _ _ _ bb1 _ _ _ _ _ (stin + 1)) in FU.
        destruct (fuel_ok_gbst_S _ _ _ _ _ _ FU ltac:(lia)) as [f1 Ef1]. subst f.
        pose proof (in_rel_tail _ _ (DSTRM inp1 sout sav (stin + 1) stout) _ _ IR eq_refl eq_refl) as IR1.
        wstepl. if_cases K3.
        { (* [comment removed for export] *)
          wstepl. wstepl. if_false_z.
          wstepl. wstepl. wstepl. notrap. wstepl.
          gbF_exit HK HD STRM MUL WML DP MD FU 11%Z 8%Z.
        }
        { (* [comment removed for export] *)
          wstepl. forget_reg 14%Z wtih. wstepl. wstepl.
          wstepl. wstepl. if_false_z.
          wstepl. wstepl. wstepl. notrap. wstepl.
          gbF_exit HK HD STRM MUL WML DP MD FU 11%Z 8%Z.
        }
      }
      { (* [comment removed for export] *)
        assert (inp = []) as -> by (lin_unbox LIN; destruct inp; [reflexivity| exfalso; cbn [length] in K2, LIN; rewrite Nat2Z.inj_succ in K2, LIN; clear -K2 LIN; zb_masks; mlia]). clear K2.
        wstepl.
        gbF_ret HRET MUL WML DP MD NB 8%Z.
      }
    }
  Qed.

  (* [comment removed for export] *)
  Lemma S0F_gb_1cfd0 : forall (Q : dres -> machine_state -> Prop), S0F_RET_OK A Q ->
    forall (F : nat) (L : dsv) (d : dst) (s : dstrm) (J : jk)
           (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte)
           (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 f200 f208 f216 : word) (pb : list byte),
    dmem DI_S0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J d s) ->
    S0FR A m j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 f200 f208 f216 pb ->
    stk s0segs m (a_lo A) (usp + -336) ->
    munch W (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J d s ->
    (0 <= sv_nblock L <= 900000)%Z ->
    fuel_ok F d s ->
    (forall (F1 : nat) (bb' bl' : Z) (inp' : list Z) (tin' : Z) (til' tih' : word) (m' : word -> option byte) (wb : word),
       let d2 := gbst d 47 bb' bl' in
       let s1 := DSTRM inp' (s_out s) (s_avail_out s) tin' (s_tout s) in
       drun F 47 L d s = dgo F1 (gb_after 47 (gbval bb' bl' 8) L (d_set_bsLive d2 (bl' - 8)) s1) ->
       fuel_ok F1 (d_set_bsLive d2 (bl' - 8)) s1 -> (F1 < F)%nat ->
       dmem DI_S0 cx (a_g1 A) (a_sv A) (a_payload A) m' (dvF cx (jk_set_t J til' tih') d2 s1) ->
       S0FR A m' j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 f200 f208 f216 pb ->
       stk s0segs m' (a_lo A) (usp + -336) ->
       munch W (a_m0 A) m' -> wmono s0segs (a_m0 A) m' -> mem_inv s0segs m' ->
       dpureF cx (a_b0 A) (a_payload A) (jk_set_t J til' tih') d2 s1 ->
       (0 <= bb' < 2^32)%Z -> (8 <= bl' <= 32)%Z -> (bv_unsigned wb mod 4294967296 = bb')%Z ->
       (8 * Z.of_nat (length inp') + bl' = 8 * Z.of_nat (length (s_in s)) + d_bsLive d)%Z ->
       forall (y12 y13 y14 y15 y16 y17 : word),
       evt s0segs (Q (drun F 47 L d s))
         (MS (mkR x1 (Z_to_bv 64 (usp + -336)) (a_gp A) (a_tp A) x5 x6 x7 x8 x9 (Z_to_bv 64 (bl' - 8)) wb y12 y13 y14 y15 y16 y17
                 (Z_to_bv 64 S) x19 (Z_to_bv 64 (S + 64036)) x21 (Z_to_bv 64 (sv_nblock L)) x23 x24 x25 x26 x27 x28 x29 x30 x31)
             (a_F A) (Z_to_bv 64 0x25ca8) (a_fc A) None m' (seg_rom s0segs))) ->
    evt s0segs (Q (drun F 47 L d s))
      (MS (mkR x1 (Z_to_bv 64 (usp + -336)) (a_gp A) (a_tp A) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
                 (Z_to_bv 64 S) x19 (Z_to_bv 64 (S + 64036)) x21 (Z_to_bv 64 (sv_nblock L)) x23 x24 x25 x26 x27 x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0x25bf0) (a_fc A) None m (seg_rom s0segs)).
  Proof.
    intros Q HRET. intros until pb. intros DM FR ST MU WM MI DP NB FU HK.
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN. pose proof rnums_words_length as RNL. lin_natZ RNL.
    unfold W14, D14, DSTATE_SIZE in MU. cbn [app blk_ivls b_s b_strm] in MU.
    destruct s as [inp sout sav stin stout]. cbn [s_in s_out s_avail_out s_tin s_tout] in *.
    pose proof DM as DM0. open_dmemF DM. s2img. cbn [s_in s_out s_avail_out s_tin s_tout] in *.
    destruct (fuel_ok_pos _ _ _ (proj1 (dpureF_bl _ _ _ _ _ _ DP)) FU) as [f EF]. subst F.
    pose proof (drun_gbst f 47 L d (DSTRM inp sout sav stin stout)) as MD. apply (fuel_ok_gbst _ _ 47) in FU.
    pose proof (dpureF_in _ _ _ _ _ _ DP) as IR.
    set (bl := d_bsLive d) in *. set (bb := d_bsBuff d) in *.
    hide_all_but (HD, STRM).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (munch_refl [(S, S + 68); (b_strm cx, b_strm cx + 20)]%Z mm) as MUL;
      pose proof (wmono_refl s0segs mm) as WML end.
    wstepl. wstepl. wstepl. wstepl.
    wstepl. if_cases K; zify_cond_z K.
    { (* [comment removed for export] *)
      wstepl. wstepl. wstepl. notrap. wstepl.
      gbF_exit HK HD STRM MUL WML DP MD FU 11%Z 8%Z.
    }
    { (* [comment removed for export] *)
      wstepl. wstepl. wstepl. wstepl. wstepl. wstepl.
      rewrite (strm_flag_ok cx (proj1 AOK)).
      wstepl. notrap.
      wstepl.
      wstepl. if_cases K2; zify_cond K2.
      { (* [comment removed for export] *)
        assert (AI1 : (1 <= Z.of_nat (length inp))%Z) by (lin_unbox LIN; clear - K2 LIN; zb_masks; mlia). clear K2. destruct inp as [|bz inp1]; [exfalso; cbn in AI1; lia|]. destruct (in_rel_head (a_payload A) _ _ _ IR eq_refl) as [b8 [NTH Ebz]]. cbn [s_in length] in NTH. cbn [length] in *. rewrite Nat2Z.inj_succ in *. subst bz.
        wstepl. wstepl. notrap.
        wstepl.
        pose proof PAY as PAYL. revive PAYL MUL WML AOK.
        pose proof (u8ro_read s0segs _ (b_src cx) (a_payload A) (b_len cx - Z.succ (Z.of_nat (length inp1)))%Z b8 _ PAYL ltac:(rewrite <- NTH; f_equal; lia) ltac:(lia) eq_refl) as RD.
        (let pv := reg_val 15%Z in lazymatch pv with Z_to_bv 64 ?e => replace e with (b_src cx + (b_len cx - Z.succ (Z.of_nat (length inp1))))%Z by lia end).
        wstepl. clear RD PAYL.
        wstepl. wstepl. wstepl. wstepl. wstepl.
        wstepl. notrap.
        wstepl. forget_reg 16%Z wtil.
        wstepl. wstepl. wstepl. forget_reg 16%Z wtil2. wstepl. wstepl. wstepl.
        (* [comment removed for export] *)
        cell_mod32 HD 32%nat. change (2^32)%Z with 4294967296%Z in HD. rewrite (pullw_mod32 bb b8) in HD by lia.
        set (bb1 := u32 (Z.lor (Z.shiftl bb 8) (bv_unsigned b8))) in *.
        pose proof (u32_range' (Z.lor (Z.shiftl bb 8) (bv_unsigned b8))) as Rbb1. change (u32 _) with bb1 in Rbb1.
        replace (b_src cx + (b_len cx - Z.succ (Z.of_nat (length inp1))) + 1)%Z with (b_src cx + (b_len cx - Z.of_nat (length inp1)))%Z in STRM by lia.
        replace (Z.succ (Z.of_nat (length inp1)) + -1)%Z with (Z.of_nat (length inp1)) in STRM by lia.
        erewrite (drun_pull_D _ _ _ _ _ _ 8%Z) in MD by first [reflexivity | cbn; lia]. change (u32 _) with bb1 in MD.
        apply (fuel_ok_pull_D _ _ _ _ _ bb1 _ _ _ _ _ (stin + 1)) in FU.
        destruct (fuel_ok_gbst_S _ _ _ _ _ _ FU ltac:(lia)) as [f1 Ef1]. subst f.
        pose proof (in_rel_tail _ _ (DSTRM inp1 sout sav (stin + 1) stout) _ _ IR eq_refl eq_refl) as IR1.
        wstepl. if_cases K3.
        { (* [comment removed for export] *)
          wstepl. wstepl. if_false_z.
          wstepl. wstepl. wstepl. notrap. wstepl.
          gbF_exit HK HD STRM MUL WML DP MD FU 11%Z 8%Z.
        }
        { (* [comment removed for export] *)
          wstepl. forget_reg 14%Z wtih. wstepl. wstepl.
          wstepl. wstepl. if_false_z.
          wstepl. wstepl. wstepl. notrap. wstepl.
          gbF_exit HK HD STRM MUL WML DP MD FU 11%Z 8%Z.
        }
      }
      { (* [comment removed for export] *)
        assert (inp = []) as -> by (lin_unbox LIN; destruct inp; [reflexivity| exfalso; cbn [length] in K2, LIN; rewrite Nat2Z.inj_succ in K2, LIN; clear -K2 LIN; zb_masks; mlia]). clear K2.
        wstepl.
        gbF_ret HRET MUL WML DP MD NB 8%Z.
      }
    }
  Qed.

  (* [comment removed for export] *)
  Lemma S0F_gb_1d074 : forall (Q : dres -> machine_state -> Prop), S0F_RET_OK A Q ->
    forall (F : nat) (L : dsv) (d : dst) (s : dstrm) (J : jk)
           (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte)
           (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 f200 f208 f216 : word) (pb : list byte),
    dmem DI_S0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J d s) ->
    S0FR A m j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 f200 f208 f216 pb ->
    stk s0segs m (a_lo A) (usp + -336) ->
    munch W (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J d s ->
    (0 <= sv_nblock L <= 900000)%Z ->
    fuel_ok F d s ->
    (forall (F1 : nat) (bb' bl' : Z) (inp' : list Z) (tin' : Z) (til' tih' : word) (m' : word -> option byte) (wb : word),
       let d2 := gbst d 48 bb' bl' in
       let s1 := DSTRM inp' (s_out s) (s_avail_out s) tin' (s_tout s) in
       drun F 48 L d s = dgo F1 (gb_after 48 (gbval bb' bl' 8) L (d_set_bsLive d2 (bl' - 8)) s1) ->
       fuel_ok F1 (d_set_bsLive d2 (bl' - 8)) s1 -> (F1 < F)%nat ->
       dmem DI_S0 cx (a_g1 A) (a_sv A) (a_payload A) m' (dvF cx (jk_set_t J til' tih') d2 s1) ->
       S0FR A m' j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 f200 f208 f216 pb ->
       stk s0segs m' (a_lo A) (usp + -336) ->
       munch W (a_m0 A) m' -> wmono s0segs (a_m0 A) m' -> mem_inv s0segs m' ->
       dpureF cx (a_b0 A) (a_payload A) (jk_set_t J til' tih') d2 s1 ->
       (0 <= bb' < 2^32)%Z -> (8 <= bl' <= 32)%Z -> (bv_unsigned wb mod 4294967296 = bb')%Z ->
       (8 * Z.of_nat (length inp') + bl' = 8 * Z.of_nat (length (s_in s)) + d_bsLive d)%Z ->
       forall (y12 y13 y14 y15 y16 y17 : word),
       evt s0segs (Q (drun F 48 L d s))
         (MS (mkR x1 (Z_to_bv 64 (usp + -336)) (a_gp A) (a_tp A) x5 x6 x7 x8 x9 (Z_to_bv 64 (bl' - 8)) wb y12 y13 y14 y15 y16 y17
                 (Z_to_bv 64 S) x19 (Z_to_bv 64 (S + 64036)) x21 (Z_to_bv 64 (sv_nblock L)) x23 x24 x25 x26 x27 x28 x29 x30 x31)
             (a_F A) (Z_to_bv 64 0x25d80) (a_fc A) None m' (seg_rom s0segs))) ->
    evt s0segs (Q (drun F 48 L d s))
      (MS (mkR x1 (Z_to_bv 64 (usp + -336)) (a_gp A) (a_tp A) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
                 (Z_to_bv 64 S) x19 (Z_to_bv 64 (S + 64036)) x21 (Z_to_bv 64 (sv_nblock L)) x23 x24 x25 x26 x27 x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0x25cc8) (a_fc A) None m (seg_rom s0segs)).
  Proof.
    intros Q HRET. intros until pb. intros DM FR ST MU WM MI DP NB FU HK.
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN. pose proof rnums_words_length as RNL. lin_natZ RNL.
    unfold W14, D14, DSTATE_SIZE in MU. cbn [app blk_ivls b_s b_strm] in MU.
    destruct s as [inp sout sav stin stout]. cbn [s_in s_out s_avail_out s_tin s_tout] in *.
    pose proof DM as DM0. open_dmemF DM. s2img. cbn [s_in s_out s_avail_out s_tin s_tout] in *.
    destruct (fuel_ok_pos _ _ _ (proj1 (dpureF_bl _ _ _ _ _ _ DP)) FU) as [f EF]. subst F.
    pose proof (drun_gbst f 48 L d (DSTRM inp sout sav stin stout)) as MD. apply (fuel_ok_gbst _ _ 48) in FU.
    pose proof (dpureF_in _ _ _ _ _ _ DP) as IR.
    set (bl := d_bsLive d) in *. set (bb := d_bsBuff d) in *.
    hide_all_but (HD, STRM).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (munch_refl [(S, S + 68); (b_strm cx, b_strm cx + 20)]%Z mm) as MUL;
      pose proof (wmono_refl s0segs mm) as WML end.
    wstepl. wstepl. wstepl. wstepl.
    wstepl. if_cases K; zify_cond_z K.
    { (* [comment removed for export] *)
      wstepl. wstepl. wstepl. notrap. wstepl.
      gbF_exit HK HD STRM MUL WML DP MD FU 11%Z 8%Z.
    }
    { (* [comment removed for export] *)
      wstepl. wstepl. wstepl. wstepl. wstepl. wstepl.
      rewrite (strm_flag_ok cx (proj1 AOK)).
      wstepl. notrap.
      wstepl.
      wstepl. if_cases K2; zify_cond K2.
      { (* [comment removed for export] *)
        assert (AI1 : (1 <= Z.of_nat (length inp))%Z) by (lin_unbox LIN; clear - K2 LIN; zb_masks; mlia). clear K2. destruct inp as [|bz inp1]; [exfalso; cbn in AI1; lia|]. destruct (in_rel_head (a_payload A) _ _ _ IR eq_refl) as [b8 [NTH Ebz]]. cbn [s_in length] in NTH. cbn [length] in *. rewrite Nat2Z.inj_succ in *. subst bz.
        wstepl. wstepl. notrap.
        wstepl.
        pose proof PAY as PAYL. revive PAYL MUL WML AOK.
        pose proof (u8ro_read s0segs _ (b_src cx) (a_payload A) (b_len cx - Z.succ (Z.of_nat (length inp1)))%Z b8 _ PAYL ltac:(rewrite <- NTH; f_equal; lia) ltac:(lia) eq_refl) as RD.
        (let pv := reg_val 15%Z in lazymatch pv with Z_to_bv 64 ?e => replace e with (b_src cx + (b_len cx - Z.succ (Z.of_nat (length inp1))))%Z by lia end).
        wstepl. clear RD PAYL.
        wstepl. wstepl. wstepl. wstepl. wstepl.
        wstepl. notrap.
        wstepl. forget_reg 16%Z wtil.
        wstepl. wstepl. wstepl. forget_reg 16%Z wtil2. wstepl. wstepl. wstepl.
        (* [comment removed for export] *)
        cell_mod32 HD 32%nat. change (2^32)%Z with 4294967296%Z in HD. rewrite (pullw_mod32 bb b8) in HD by lia.
        set (bb1 := u32 (Z.lor (Z.shiftl bb 8) (bv_unsigned b8))) in *.
        pose proof (u32_range' (Z.lor (Z.shiftl bb 8) (bv_unsigned b8))) as Rbb1. change (u32 _) with bb1 in Rbb1.
        replace (b_src cx + (b_len cx - Z.succ (Z.of_nat (length inp1))) + 1)%Z with (b_src cx + (b_len cx - Z.of_nat (length inp1)))%Z in STRM by lia.
        replace (Z.succ (Z.of_nat (length inp1)) + -1)%Z with (Z.of_nat (length inp1)) in STRM by lia.
        erewrite (drun_pull_D _ _ _ _ _ _ 8%Z) in MD by first [reflexivity | cbn; lia]. change (u32 _) with bb1 in MD.
        apply (fuel_ok_pull_D _ _ _ _ _ bb1 _ _ _ _ _ (stin + 1)) in FU.
        destruct (fuel_ok_gbst_S _ _ _ _ _ _ FU ltac:(lia)) as [f1 Ef1]. subst f.
        pose proof (in_rel_tail _ _ (DSTRM inp1 sout sav (stin + 1) stout) _ _ IR eq_refl eq_refl) as IR1.
        wstepl. if_cases K3.
        { (* [comment removed for export] *)
          wstepl. wstepl. if_false_z.
          wstepl. wstepl. wstepl. notrap. wstepl.
          gbF_exit HK HD STRM MUL WML DP MD FU 11%Z 8%Z.
        }
        { (* [comment removed for export] *)
          wstepl. forget_reg 14%Z wtih. wstepl. wstepl.
          wstepl. wstepl. if_false_z.
          wstepl. wstepl. wstepl. notrap. wstepl.
          gbF_exit HK HD STRM MUL WML DP MD FU 11%Z 8%Z.
        }
      }
      { (* [comment removed for export] *)
        assert (inp = []) as -> by (lin_unbox LIN; destruct inp; [reflexivity| exfalso; cbn [length] in K2, LIN; rewrite Nat2Z.inj_succ in K2, LIN; clear -K2 LIN; zb_masks; mlia]). clear K2.
        wstepl.
        gbF_ret HRET MUL WML DP MD NB 8%Z.
      }
    }
  Qed.

End R.

End ACeilS1.
