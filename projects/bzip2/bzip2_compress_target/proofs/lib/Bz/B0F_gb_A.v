(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0 SegsB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzDefs BzModel BzTac BzTac2 BzInv BzTables BzContracts.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK DecCutFB DecTacFB B0F_decV B0F_decRet.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import AsanKit AsanKitB0.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutFB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decV OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decRet.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import LinSplit.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import NatLit.
Local Ltac Zify.zify_pre_hook ::= NatLit.natlen_ctx.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import StoreFast.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFastZ StoreFastC.
Local Ltac mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require NormFast FLiaA.
Local Ltac lia ::= FLiaA.lia_f.
Local Ltac BzTac.bz32 ::= NormFast.bz32_m.
Local Ltac BzTac2.bz32l ::= NormFast.bz32l_m.
Local Ltac Zify.zify_pre_hook ::= NormFast.nf_pre_natlen.
Local Ltac DecCutF.unset_Z ::= NormFast.unset_Z_subst.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require GbKitB.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import GbTacB.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Lib.Step.solve_load ::= AsanKit.asan_solve_load.

Section ACeilS1. Context {ACEIL__ : ACeil}.

Section R.
  Variable A : act14.
  Hypothesis AOK : act_ok BIHI0 A.
  Hypothesis ASH : act_sh DI_B0 A.

  Notation usp := (bv_unsigned (a_sp A)).
  Notation cx := (a_cx A).
  Notation S := (b_s (a_cx A)).
  Notation W := (W14 A).

  (* [comment removed for export] *)
  Lemma B0F_gb_aa508 : forall (Q : dres -> machine_state -> Prop), B0F_RET_OK A Q ->
    forall (F : nat) (L : dsv) (d : dst) (s : dstrm) (J : jk)
           (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x23 x24 x25 x28 x29 x30 x31 : word)
           (m : word -> option byte)
           (w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 : word)
           (w344 w352 w360 w368 w376 w384 w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 w496 w504 w520 w528 w720 w728 w736 w744 w752 : word),
    dmem DI_B0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J d s) ->
    B0FL A m w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 ->
    B0FH A m w344 w352 w360 w368 w376 w384 (Z_to_bv 64 (a_shs A)) w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 (Z_to_bv 64 (sv_nblock L)) w496 w504 (Z_to_bv 64 (a_fb A)) w520 w528 (Z_to_bv 64 (a_shs A + 1)) w720 w728 w736 w744 w752 ->
    aframe A m ->
    stk b0segs m (a_lo A) (a_P A) ->
    munch W (a_m0 A) m -> wmono b0segs (a_m0 A) m -> mem_inv b0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J d s ->
    (0 <= sv_nblock L <= 900000)%Z ->
    fuel_ok F d s ->
    (forall (F1 : nat) (bb' bl' : Z) (inp' : list Z) (tin' : Z) (til' tih' : word) (m' : word -> option byte),
       let d2 := gbst d 14 bb' bl' in
       let s1 := DSTRM inp' (s_out s) (s_avail_out s) tin' (s_tout s) in
       drun F 14 L d s = dgo F1 (gb_after 14 (gbval bb' bl' 8) L (d_set_bsLive d2 (bl' - 8)) s1) ->
       fuel_ok F1 (d_set_bsLive d2 (bl' - 8)) s1 -> (F1 < F)%nat ->
       dmem DI_B0 cx (a_g1 A) (a_sv A) (a_payload A) m' (dvF cx (jk_set_t J til' tih') d2 s1) ->
       aframe A m' ->
       stk b0segs m' (a_lo A) (a_P A) ->
       munch W (a_m0 A) m' -> wmono b0segs (a_m0 A) m' -> mem_inv b0segs m' ->
       dpureF cx (a_b0 A) (a_payload A) (jk_set_t J til' tih') d2 s1 ->
       (0 <= bb' < 2^32)%Z -> (8 <= bl' <= 32)%Z ->
       (8 * Z.of_nat (length inp') + bl' = 8 * Z.of_nat (length (s_in s)) + d_bsLive d)%Z ->
       forall (y1 y7 y12 y13 y14 y15 y16 y18 y19 y21 y23 y24 y25 y28 y29 y30 y31 yw32 yw40 yw48 yw56 : word),
       B0FL A m' w0 w8 w16 w24 yw32 yw40 yw48 yw56 w64 w72 w80 w88 w96 w104 w112 w120 ->
       B0FH A m' w344 w352 w360 w368 w376 w384 (Z_to_bv 64 (a_shs A)) w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 (Z_to_bv 64 (sv_nblock L)) w496 w504 (Z_to_bv 64 (a_fb A)) w520 w528 (Z_to_bv 64 (a_shs A + 1)) w720 w728 w736 w744 w752 ->
       evt b0segs (Q (drun F 14 L d s))
         (MS (mkR y1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) (Z_to_bv 64 (a_shs A + -2147450876)) (Z_to_bv 64 (bl')) y7 (a_sp A) (Z_to_bv 64 (a_P A)) (Z_to_bv 64 (S + 36)) (Z_to_bv 64 (S + 32)) y12 y13 y14 y15 y16 (Z_to_bv 64 (a_shs A + 4)) y18 y19 (Z_to_bv 64 (S + 64036)) y21 (Z_to_bv 64 2147450880) y23 y24 y25 (Z_to_bv 64 S) (Z_to_bv 64 (a_shf A)) y28 y29 y30 y31)
             (a_F A) (Z_to_bv 64 0xaa814) (a_fc A) None m' (seg_rom b0segs))) ->
    evt b0segs (Q (drun F 14 L d s))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) x5 x6 x7 (a_sp A) (Z_to_bv 64 (a_P A)) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 (S + 64036)) x21 (Z_to_bv 64 2147450880) x23 x24 x25 (Z_to_bv 64 S) (Z_to_bv 64 (a_shf A)) x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0xaa7cc) (a_fc A) None m (seg_rom b0segs)).
  Proof.
    intros Q HRET. intros until w752. intros DM FRL FRH AF ST MU WM MI DP NB FU HK.
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN. pose proof rnums_words_length as RNL. lin_natZ RNL.
    unfold_W14 MU. open_ash ASH AOK. pose proof (proj2 ANS : saddr S (a_shs A)) as ANS0. pose proof (proj1 ANS) as S8. pose proof (proj1 ANT) as STRM8.
    pose proof (act_sep_s_strm _ _ AOK : id _) as SEPst.
    destruct s as [inp sout sav stin stout]. cbn [s_in s_out s_avail_out s_tin s_tout] in *.
    pose proof DM as DM0. open_dmemF DM. b0img. cbn [s_in s_out s_avail_out s_tin s_tout] in *.
    destruct (fuel_ok_pos _ _ _ (proj1 (dpureF_bl _ _ _ _ _ _ DP)) FU) as [f EF]. subst F.
    pose proof (drun_gbst f 14 L d (DSTRM inp sout sav stin stout)) as MD. apply (fuel_ok_gbst _ _ 14) in FU.
    pose proof (dpureF_in _ _ _ _ _ _ DP) as IR.
    set (bl := d_bsLive d) in *. set (bb := d_bsBuff d) in *.
    hide_all_but (HD, STRM, FRL, FRH).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (munch_refl [(S, S + 68); (b_strm cx, b_strm cx + 20); (a_P A, a_P A + 128); (a_P A + 344, a_P A + 760)]%Z mm) as MUL;
      pose proof (wmono_refl b0segs mm) as WML end.
    brun. if_cases K; zify_cond_z K.
    { (* [comment removed for export] *)
      brun_to 0xaa814%Z. sh_norm.
      gbA_exit HK MUL WML DP MD FU 8%Z.
    }
    { (* [comment removed for export] *)
      brun. if_cases K2_1; zify_cond K2_1.
      { (* [comment removed for export] *)
        assert (AI1 : (1 <= Z.of_nat (length inp))%Z) by (lin_unbox LIN; clear - K2_1 LIN; zb_masks; mlia). clear K2_1. destruct inp as [|bz1 inp1]; [exfalso; cbn in AI1; lia|]. destruct (in_rel_head (a_payload A) _ _ _ IR eq_refl) as [b8_1 [NTH1 Ebz1]]. cbn [s_in length] in NTH1. cbn [length] in *. rewrite Nat2Z.inj_succ in *. subst bz1.
        brun_to 0xade68%Z. forget_reg 1%Z wj1_1. forget_reg 24%Z wj24_1.
        ack_rd (b_src cx + (b_len cx - Z.succ (Z.of_nat (length inp1))))%Z 1%Z.
        brun_to 0xade70%Z. ack_merge.
        brun_to 0xade74%Z.
        pose proof (GbKitB.gbF_payload_tr _ _ AOK DI_B0 _ _ _ _ _ DM0 MUL) as PAYL. b0img.
        pose proof (u8ro_read b0segs _ (b_src cx) (a_payload A) (b_len cx - Z.succ (Z.of_nat (length inp1)))%Z b8_1 _ PAYL ltac:(rewrite <- NTH1; f_equal; lia) ltac:(lia) eq_refl) as RD.
        (let pv := reg_val 16%Z in lazymatch pv with Z_to_bv 64 ?e => replace e with (b_src cx + (b_len cx - Z.succ (Z.of_nat (length inp1))))%Z by lia end).
        wstepl. clear RD PAYL.
        brun_to 0xaded4%Z.
        (* [comment removed for export] *)
        cell_mod32 HD 32%nat. change (2^32)%Z with 4294967296%Z in HD. rewrite (pullw_mod32 bb b8_1) in HD by lia.
        set (bb1 := u32 (Z.lor (Z.shiftl bb 8) (bv_unsigned b8_1))) in *.
        pose proof (u32_range' (Z.lor (Z.shiftl bb 8) (bv_unsigned b8_1))) as Rbb1. change (u32 _) with bb1 in Rbb1.
        replace (b_src cx + (b_len cx - Z.succ (Z.of_nat (length inp1))) + 1)%Z with (b_src cx + (b_len cx - Z.of_nat (length inp1)))%Z in STRM by lia.
        replace (Z.succ (Z.of_nat (length inp1)) + -1)%Z with (Z.of_nat (length inp1)) in STRM by lia.
        erewrite (drun_pull_D _ _ _ _ _ _ 8%Z) in MD by first [reflexivity | cbn; lia]. change (u32 _) with bb1 in MD.
        apply (fuel_ok_pull_D _ _ _ _ _ bb1 _ _ _ _ _ (stin + 1)) in FU.
        destruct (fuel_ok_gbst_S _ _ _ _ _ _ FU ltac:(lia)) as [f1 Ef1]. subst f.
        pose proof (in_rel_tail _ _ (DSTRM inp1 sout sav (stin + 1) stout) _ _ IR eq_refl eq_refl) as IR1.
        til_joinA 16%Z 0xadeec%Z HD STRM FRL FRH ST MU WM MI MUL WML.
        { brun. if_cases K3_1; [ til_useA JN | brun_to 0xadeec%Z; til_useA JN ]. }
        brun. if_false_z.
        brun_to 0xaa814%Z. sh_norm.
        gbA_exit HK MUL WML DP MD FU 8%Z.
      }
      { (* [comment removed for export] *)
        assert (inp = []) as -> by (lin_unbox LIN; destruct inp; [reflexivity| exfalso; cbn [length] in K2_1, LIN; rewrite Nat2Z.inj_succ in K2_1, LIN; clear -K2_1 LIN; zb_masks; mlia]). clear K2_1.
        brun_to 0xa9f7c%Z.
        gbA_ret HRET MUL WML DP MD NB 8%Z.
      }
    }
  Qed.

  (* [comment removed for export] *)
  Lemma B0F_gb_aa5a4 : forall (Q : dres -> machine_state -> Prop), B0F_RET_OK A Q ->
    forall (F : nat) (L : dsv) (d : dst) (s : dstrm) (J : jk)
           (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x23 x24 x25 x28 x29 x30 x31 : word)
           (m : word -> option byte)
           (w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 : word)
           (w344 w352 w360 w368 w376 w384 w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 w496 w504 w520 w528 w720 w728 w736 w744 w752 : word),
    dmem DI_B0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J d s) ->
    B0FL A m w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 ->
    B0FH A m w344 w352 w360 w368 w376 w384 (Z_to_bv 64 (a_shs A)) w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 (Z_to_bv 64 (sv_nblock L)) w496 w504 (Z_to_bv 64 (a_fb A)) w520 w528 (Z_to_bv 64 (a_shs A + 1)) w720 w728 w736 w744 w752 ->
    aframe A m ->
    stk b0segs m (a_lo A) (a_P A) ->
    munch W (a_m0 A) m -> wmono b0segs (a_m0 A) m -> mem_inv b0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J d s ->
    (0 <= sv_nblock L <= 900000)%Z ->
    fuel_ok F d s ->
    (forall (F1 : nat) (bb' bl' : Z) (inp' : list Z) (tin' : Z) (til' tih' : word) (m' : word -> option byte),
       let d2 := gbst d 15 bb' bl' in
       let s1 := DSTRM inp' (s_out s) (s_avail_out s) tin' (s_tout s) in
       drun F 15 L d s = dgo F1 (gb_after 15 (gbval bb' bl' 8) L (d_set_bsLive d2 (bl' - 8)) s1) ->
       fuel_ok F1 (d_set_bsLive d2 (bl' - 8)) s1 -> (F1 < F)%nat ->
       dmem DI_B0 cx (a_g1 A) (a_sv A) (a_payload A) m' (dvF cx (jk_set_t J til' tih') d2 s1) ->
       aframe A m' ->
       stk b0segs m' (a_lo A) (a_P A) ->
       munch W (a_m0 A) m' -> wmono b0segs (a_m0 A) m' -> mem_inv b0segs m' ->
       dpureF cx (a_b0 A) (a_payload A) (jk_set_t J til' tih') d2 s1 ->
       (0 <= bb' < 2^32)%Z -> (8 <= bl' <= 32)%Z ->
       (8 * Z.of_nat (length inp') + bl' = 8 * Z.of_nat (length (s_in s)) + d_bsLive d)%Z ->
       forall (y1 y7 y12 y13 y14 y15 y16 y18 y19 y21 y23 y24 y25 y28 y29 y30 y31 yw32 yw40 yw48 yw56 : word),
       B0FL A m' w0 w8 w16 w24 yw32 yw40 yw48 yw56 w64 w72 w80 w88 w96 w104 w112 w120 ->
       B0FH A m' w344 w352 w360 w368 w376 w384 (Z_to_bv 64 (a_shs A)) w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 (Z_to_bv 64 (sv_nblock L)) w496 w504 (Z_to_bv 64 (a_fb A)) w520 w528 (Z_to_bv 64 (a_shs A + 1)) w720 w728 w736 w744 w752 ->
       evt b0segs (Q (drun F 15 L d s))
         (MS (mkR y1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) (Z_to_bv 64 (a_shs A + -2147450876)) (Z_to_bv 64 (bl')) y7 (a_sp A) (Z_to_bv 64 (a_P A)) (Z_to_bv 64 (S + 36)) (Z_to_bv 64 (S + 32)) y12 y13 y14 y15 y16 (Z_to_bv 64 (a_shs A + 4)) y18 y19 (Z_to_bv 64 (S + 64036)) y21 (Z_to_bv 64 2147450880) y23 y24 y25 (Z_to_bv 64 S) (Z_to_bv 64 (a_shf A)) y28 y29 y30 y31)
             (a_F A) (Z_to_bv 64 0xaa8b0) (a_fc A) None m' (seg_rom b0segs))) ->
    evt b0segs (Q (drun F 15 L d s))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) x5 x6 x7 (a_sp A) (Z_to_bv 64 (a_P A)) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 (S + 64036)) x21 (Z_to_bv 64 2147450880) x23 x24 x25 (Z_to_bv 64 S) (Z_to_bv 64 (a_shf A)) x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0xaa868) (a_fc A) None m (seg_rom b0segs)).
  Proof.
    intros Q HRET. intros until w752. intros DM FRL FRH AF ST MU WM MI DP NB FU HK.
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN. pose proof rnums_words_length as RNL. lin_natZ RNL.
    unfold_W14 MU. open_ash ASH AOK. pose proof (proj2 ANS : saddr S (a_shs A)) as ANS0. pose proof (proj1 ANS) as S8. pose proof (proj1 ANT) as STRM8.
    pose proof (act_sep_s_strm _ _ AOK : id _) as SEPst.
    destruct s as [inp sout sav stin stout]. cbn [s_in s_out s_avail_out s_tin s_tout] in *.
    pose proof DM as DM0. open_dmemF DM. b0img. cbn [s_in s_out s_avail_out s_tin s_tout] in *.
    destruct (fuel_ok_pos _ _ _ (proj1 (dpureF_bl _ _ _ _ _ _ DP)) FU) as [f EF]. subst F.
    pose proof (drun_gbst f 15 L d (DSTRM inp sout sav stin stout)) as MD. apply (fuel_ok_gbst _ _ 15) in FU.
    pose proof (dpureF_in _ _ _ _ _ _ DP) as IR.
    set (bl := d_bsLive d) in *. set (bb := d_bsBuff d) in *.
    hide_all_but (HD, STRM, FRL, FRH).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (munch_refl [(S, S + 68); (b_strm cx, b_strm cx + 20); (a_P A, a_P A + 128); (a_P A + 344, a_P A + 760)]%Z mm) as MUL;
      pose proof (wmono_refl b0segs mm) as WML end.
    brun. if_cases K; zify_cond_z K.
    { (* [comment removed for export] *)
      brun_to 0xaa8b0%Z. sh_norm.
      gbA_exit HK MUL WML DP MD FU 8%Z.
    }
    { (* [comment removed for export] *)
      brun. if_cases K2_1; zify_cond K2_1.
      { (* [comment removed for export] *)
        assert (AI1 : (1 <= Z.of_nat (length inp))%Z) by (lin_unbox LIN; clear - K2_1 LIN; zb_masks; mlia). clear K2_1. destruct inp as [|bz1 inp1]; [exfalso; cbn in AI1; lia|]. destruct (in_rel_head (a_payload A) _ _ _ IR eq_refl) as [b8_1 [NTH1 Ebz1]]. cbn [s_in length] in NTH1. cbn [length] in *. rewrite Nat2Z.inj_succ in *. subst bz1.
        brun_to 0xadaf8%Z. forget_reg 1%Z wj1_1. forget_reg 24%Z wj24_1.
        ack_rd (b_src cx + (b_len cx - Z.succ (Z.of_nat (length inp1))))%Z 1%Z.
        brun_to 0xadb00%Z. ack_merge.
        brun_to 0xadb04%Z.
        pose proof (GbKitB.gbF_payload_tr _ _ AOK DI_B0 _ _ _ _ _ DM0 MUL) as PAYL. b0img.
        pose proof (u8ro_read b0segs _ (b_src cx) (a_payload A) (b_len cx - Z.succ (Z.of_nat (length inp1)))%Z b8_1 _ PAYL ltac:(rewrite <- NTH1; f_equal; lia) ltac:(lia) eq_refl) as RD.
        (let pv := reg_val 16%Z in lazymatch pv with Z_to_bv 64 ?e => replace e with (b_src cx + (b_len cx - Z.succ (Z.of_nat (length inp1))))%Z by lia end).
        wstepl. clear RD PAYL.
        brun_to 0xadb64%Z.
        (* [comment removed for export] *)
        cell_mod32 HD 32%nat. change (2^32)%Z with 4294967296%Z in HD. rewrite (pullw_mod32 bb b8_1) in HD by lia.
        set (bb1 := u32 (Z.lor (Z.shiftl bb 8) (bv_unsigned b8_1))) in *.
        pose proof (u32_range' (Z.lor (Z.shiftl bb 8) (bv_unsigned b8_1))) as Rbb1. change (u32 _) with bb1 in Rbb1.
        replace (b_src cx + (b_len cx - Z.succ (Z.of_nat (length inp1))) + 1)%Z with (b_src cx + (b_len cx - Z.of_nat (length inp1)))%Z in STRM by lia.
        replace (Z.succ (Z.of_nat (length inp1)) + -1)%Z with (Z.of_nat (length inp1)) in STRM by lia.
        erewrite (drun_pull_D _ _ _ _ _ _ 8%Z) in MD by first [reflexivity | cbn; lia]. change (u32 _) with bb1 in MD.
        apply (fuel_ok_pull_D _ _ _ _ _ bb1 _ _ _ _ _ (stin + 1)) in FU.
        destruct (fuel_ok_gbst_S _ _ _ _ _ _ FU ltac:(lia)) as [f1 Ef1]. subst f.
        pose proof (in_rel_tail _ _ (DSTRM inp1 sout sav (stin + 1) stout) _ _ IR eq_refl eq_refl) as IR1.
        til_joinA 16%Z 0xadb7c%Z HD STRM FRL FRH ST MU WM MI MUL WML.
        { brun. if_cases K3_1; [ til_useA JN | brun_to 0xadb7c%Z; til_useA JN ]. }
        brun. if_false_z.
        brun_to 0xaa8b0%Z. sh_norm.
        gbA_exit HK MUL WML DP MD FU 8%Z.
      }
      { (* [comment removed for export] *)
        assert (inp = []) as -> by (lin_unbox LIN; destruct inp; [reflexivity| exfalso; cbn [length] in K2_1, LIN; rewrite Nat2Z.inj_succ in K2_1, LIN; clear -K2_1 LIN; zb_masks; mlia]). clear K2_1.
        brun_to 0xa9f7c%Z.
        gbA_ret HRET MUL WML DP MD NB 8%Z.
      }
    }
  Qed.

  (* [comment removed for export] *)
  Lemma B0F_gb_aa634 : forall (Q : dres -> machine_state -> Prop), B0F_RET_OK A Q ->
    forall (F : nat) (L : dsv) (d : dst) (s : dstrm) (J : jk)
           (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x23 x24 x25 x28 x29 x30 x31 : word)
           (m : word -> option byte)
           (w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 : word)
           (w344 w352 w360 w368 w376 w384 w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 w496 w504 w520 w528 w720 w728 w736 w744 w752 : word),
    dmem DI_B0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J d s) ->
    B0FL A m w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 ->
    B0FH A m w344 w352 w360 w368 w376 w384 (Z_to_bv 64 (a_shs A)) w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 (Z_to_bv 64 (sv_nblock L)) w496 w504 (Z_to_bv 64 (a_fb A)) w520 w528 (Z_to_bv 64 (a_shs A + 1)) w720 w728 w736 w744 w752 ->
    aframe A m ->
    stk b0segs m (a_lo A) (a_P A) ->
    munch W (a_m0 A) m -> wmono b0segs (a_m0 A) m -> mem_inv b0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J d s ->
    (0 <= sv_nblock L <= 900000)%Z ->
    fuel_ok F d s ->
    (forall (F1 : nat) (bb' bl' : Z) (inp' : list Z) (tin' : Z) (til' tih' : word) (m' : word -> option byte),
       let d2 := gbst d 16 bb' bl' in
       let s1 := DSTRM inp' (s_out s) (s_avail_out s) tin' (s_tout s) in
       drun F 16 L d s = dgo F1 (gb_after 16 (gbval bb' bl' 8) L (d_set_bsLive d2 (bl' - 8)) s1) ->
       fuel_ok F1 (d_set_bsLive d2 (bl' - 8)) s1 -> (F1 < F)%nat ->
       dmem DI_B0 cx (a_g1 A) (a_sv A) (a_payload A) m' (dvF cx (jk_set_t J til' tih') d2 s1) ->
       aframe A m' ->
       stk b0segs m' (a_lo A) (a_P A) ->
       munch W (a_m0 A) m' -> wmono b0segs (a_m0 A) m' -> mem_inv b0segs m' ->
       dpureF cx (a_b0 A) (a_payload A) (jk_set_t J til' tih') d2 s1 ->
       (0 <= bb' < 2^32)%Z -> (8 <= bl' <= 32)%Z ->
       (8 * Z.of_nat (length inp') + bl' = 8 * Z.of_nat (length (s_in s)) + d_bsLive d)%Z ->
       forall (y1 y7 y12 y13 y14 y15 y16 y18 y19 y21 y23 y24 y25 y28 y29 y30 y31 yw32 yw40 yw48 yw56 : word),
       B0FL A m' w0 w8 w16 w24 yw32 yw40 yw48 yw56 w64 w72 w80 w88 w96 w104 w112 w120 ->
       B0FH A m' w344 w352 w360 w368 w376 w384 (Z_to_bv 64 (a_shs A)) w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 (Z_to_bv 64 (sv_nblock L)) w496 w504 (Z_to_bv 64 (a_fb A)) w520 w528 (Z_to_bv 64 (a_shs A + 1)) w720 w728 w736 w744 w752 ->
       evt b0segs (Q (drun F 16 L d s))
         (MS (mkR y1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) (Z_to_bv 64 (a_shs A + -2147450876)) (Z_to_bv 64 (bl')) y7 (a_sp A) (Z_to_bv 64 (a_P A)) (Z_to_bv 64 (S + 36)) (Z_to_bv 64 (S + 32)) y12 y13 y14 y15 y16 (Z_to_bv 64 (a_shs A + 4)) y18 y19 (Z_to_bv 64 (S + 64036)) y21 (Z_to_bv 64 2147450880) y23 y24 y25 (Z_to_bv 64 S) (Z_to_bv 64 (a_shf A)) y28 y29 y30 y31)
             (a_F A) (Z_to_bv 64 0xaa940) (a_fc A) None m' (seg_rom b0segs))) ->
    evt b0segs (Q (drun F 16 L d s))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) x5 x6 x7 (a_sp A) (Z_to_bv 64 (a_P A)) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 (S + 64036)) x21 (Z_to_bv 64 2147450880) x23 x24 x25 (Z_to_bv 64 S) (Z_to_bv 64 (a_shf A)) x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0xaa8f8) (a_fc A) None m (seg_rom b0segs)).
  Proof.
    intros Q HRET. intros until w752. intros DM FRL FRH AF ST MU WM MI DP NB FU HK.
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN. pose proof rnums_words_length as RNL. lin_natZ RNL.
    unfold_W14 MU. open_ash ASH AOK. pose proof (proj2 ANS : saddr S (a_shs A)) as ANS0. pose proof (proj1 ANS) as S8. pose proof (proj1 ANT) as STRM8.
    pose proof (act_sep_s_strm _ _ AOK : id _) as SEPst.
    destruct s as [inp sout sav stin stout]. cbn [s_in s_out s_avail_out s_tin s_tout] in *.
    pose proof DM as DM0. open_dmemF DM. b0img. cbn [s_in s_out s_avail_out s_tin s_tout] in *.
    destruct (fuel_ok_pos _ _ _ (proj1 (dpureF_bl _ _ _ _ _ _ DP)) FU) as [f EF]. subst F.
    pose proof (drun_gbst f 16 L d (DSTRM inp sout sav stin stout)) as MD. apply (fuel_ok_gbst _ _ 16) in FU.
    pose proof (dpureF_in _ _ _ _ _ _ DP) as IR.
    set (bl := d_bsLive d) in *. set (bb := d_bsBuff d) in *.
    hide_all_but (HD, STRM, FRL, FRH).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (munch_refl [(S, S + 68); (b_strm cx, b_strm cx + 20); (a_P A, a_P A + 128); (a_P A + 344, a_P A + 760)]%Z mm) as MUL;
      pose proof (wmono_refl b0segs mm) as WML end.
    brun. if_cases K; zify_cond_z K.
    { (* [comment removed for export] *)
      brun_to 0xaa940%Z. sh_norm.
      gbA_exit HK MUL WML DP MD FU 8%Z.
    }
    { (* [comment removed for export] *)
      brun. if_cases K2_1; zify_cond K2_1.
      { (* [comment removed for export] *)
        assert (AI1 : (1 <= Z.of_nat (length inp))%Z) by (lin_unbox LIN; clear - K2_1 LIN; zb_masks; mlia). clear K2_1. destruct inp as [|bz1 inp1]; [exfalso; cbn in AI1; lia|]. destruct (in_rel_head (a_payload A) _ _ _ IR eq_refl) as [b8_1 [NTH1 Ebz1]]. cbn [s_in length] in NTH1. cbn [length] in *. rewrite Nat2Z.inj_succ in *. subst bz1.
        brun_to 0xad788%Z. forget_reg 1%Z wj1_1. forget_reg 24%Z wj24_1.
        ack_rd (b_src cx + (b_len cx - Z.succ (Z.of_nat (length inp1))))%Z 1%Z.
        brun_to 0xad790%Z. ack_merge.
        brun_to 0xad794%Z.
        pose proof (GbKitB.gbF_payload_tr _ _ AOK DI_B0 _ _ _ _ _ DM0 MUL) as PAYL. b0img.
        pose proof (u8ro_read b0segs _ (b_src cx) (a_payload A) (b_len cx - Z.succ (Z.of_nat (length inp1)))%Z b8_1 _ PAYL ltac:(rewrite <- NTH1; f_equal; lia) ltac:(lia) eq_refl) as RD.
        (let pv := reg_val 16%Z in lazymatch pv with Z_to_bv 64 ?e => replace e with (b_src cx + (b_len cx - Z.succ (Z.of_nat (length inp1))))%Z by lia end).
        wstepl. clear RD PAYL.
        brun_to 0xad7f4%Z.
        (* [comment removed for export] *)
        cell_mod32 HD 32%nat. change (2^32)%Z with 4294967296%Z in HD. rewrite (pullw_mod32 bb b8_1) in HD by lia.
        set (bb1 := u32 (Z.lor (Z.shiftl bb 8) (bv_unsigned b8_1))) in *.
        pose proof (u32_range' (Z.lor (Z.shiftl bb 8) (bv_unsigned b8_1))) as Rbb1. change (u32 _) with bb1 in Rbb1.
        replace (b_src cx + (b_len cx - Z.succ (Z.of_nat (length inp1))) + 1)%Z with (b_src cx + (b_len cx - Z.of_nat (length inp1)))%Z in STRM by lia.
        replace (Z.succ (Z.of_nat (length inp1)) + -1)%Z with (Z.of_nat (length inp1)) in STRM by lia.
        erewrite (drun_pull_D _ _ _ _ _ _ 8%Z) in MD by first [reflexivity | cbn; lia]. change (u32 _) with bb1 in MD.
        apply (fuel_ok_pull_D _ _ _ _ _ bb1 _ _ _ _ _ (stin + 1)) in FU.
        destruct (fuel_ok_gbst_S _ _ _ _ _ _ FU ltac:(lia)) as [f1 Ef1]. subst f.
        pose proof (in_rel_tail _ _ (DSTRM inp1 sout sav (stin + 1) stout) _ _ IR eq_refl eq_refl) as IR1.
        til_joinA 16%Z 0xad80c%Z HD STRM FRL FRH ST MU WM MI MUL WML.
        { brun. if_cases K3_1; [ til_useA JN | brun_to 0xad80c%Z; til_useA JN ]. }
        brun. if_false_z.
        brun_to 0xaa940%Z. sh_norm.
        gbA_exit HK MUL WML DP MD FU 8%Z.
      }
      { (* [comment removed for export] *)
        assert (inp = []) as -> by (lin_unbox LIN; destruct inp; [reflexivity| exfalso; cbn [length] in K2_1, LIN; rewrite Nat2Z.inj_succ in K2_1, LIN; clear -K2_1 LIN; zb_masks; mlia]). clear K2_1.
        brun_to 0xa9f7c%Z.
        gbA_ret HRET MUL WML DP MD NB 8%Z.
      }
    }
  Qed.

  (* [comment removed for export] *)
  Lemma B0F_gb_aa6c4 : forall (Q : dres -> machine_state -> Prop), B0F_RET_OK A Q ->
    forall (F : nat) (L : dsv) (d : dst) (s : dstrm) (J : jk)
           (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x23 x24 x25 x28 x29 x30 x31 : word)
           (m : word -> option byte)
           (w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 : word)
           (w344 w352 w360 w368 w376 w384 w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 w496 w504 w520 w528 w720 w728 w736 w744 w752 : word),
    dmem DI_B0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J d s) ->
    B0FL A m w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 ->
    B0FH A m w344 w352 w360 w368 w376 w384 (Z_to_bv 64 (a_shs A)) w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 (Z_to_bv 64 (sv_nblock L)) w496 w504 (Z_to_bv 64 (a_fb A)) w520 w528 (Z_to_bv 64 (a_shs A + 1)) w720 w728 w736 w744 w752 ->
    aframe A m ->
    stk b0segs m (a_lo A) (a_P A) ->
    munch W (a_m0 A) m -> wmono b0segs (a_m0 A) m -> mem_inv b0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J d s ->
    (0 <= sv_nblock L <= 900000)%Z ->
    fuel_ok F d s ->
    (forall (F1 : nat) (bb' bl' : Z) (inp' : list Z) (tin' : Z) (til' tih' : word) (m' : word -> option byte),
       let d2 := gbst d 17 bb' bl' in
       let s1 := DSTRM inp' (s_out s) (s_avail_out s) tin' (s_tout s) in
       drun F 17 L d s = dgo F1 (gb_after 17 (gbval bb' bl' 8) L (d_set_bsLive d2 (bl' - 8)) s1) ->
       fuel_ok F1 (d_set_bsLive d2 (bl' - 8)) s1 -> (F1 < F)%nat ->
       dmem DI_B0 cx (a_g1 A) (a_sv A) (a_payload A) m' (dvF cx (jk_set_t J til' tih') d2 s1) ->
       aframe A m' ->
       stk b0segs m' (a_lo A) (a_P A) ->
       munch W (a_m0 A) m' -> wmono b0segs (a_m0 A) m' -> mem_inv b0segs m' ->
       dpureF cx (a_b0 A) (a_payload A) (jk_set_t J til' tih') d2 s1 ->
       (0 <= bb' < 2^32)%Z -> (8 <= bl' <= 32)%Z ->
       (8 * Z.of_nat (length inp') + bl' = 8 * Z.of_nat (length (s_in s)) + d_bsLive d)%Z ->
       forall (y1 y7 y12 y13 y14 y15 y16 y18 y19 y21 y23 y24 y25 y28 y29 y30 y31 yw32 yw40 yw48 yw56 : word),
       B0FL A m' w0 w8 w16 w24 yw32 yw40 yw48 yw56 w64 w72 w80 w88 w96 w104 w112 w120 ->
       B0FH A m' w344 w352 w360 w368 w376 w384 (Z_to_bv 64 (a_shs A)) w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 (Z_to_bv 64 (sv_nblock L)) w496 w504 (Z_to_bv 64 (a_fb A)) w520 w528 (Z_to_bv 64 (a_shs A + 1)) w720 w728 w736 w744 w752 ->
       evt b0segs (Q (drun F 17 L d s))
         (MS (mkR y1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) (Z_to_bv 64 (a_shs A + -2147450876)) (Z_to_bv 64 (bl')) y7 (a_sp A) (Z_to_bv 64 (a_P A)) (Z_to_bv 64 (S + 36)) (Z_to_bv 64 (S + 32)) y12 y13 y14 y15 y16 (Z_to_bv 64 (a_shs A + 4)) y18 y19 (Z_to_bv 64 (S + 64036)) y21 (Z_to_bv 64 2147450880) y23 y24 y25 (Z_to_bv 64 S) (Z_to_bv 64 (a_shf A)) y28 y29 y30 y31)
             (a_F A) (Z_to_bv 64 0xaa9d0) (a_fc A) None m' (seg_rom b0segs))) ->
    evt b0segs (Q (drun F 17 L d s))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) x5 x6 x7 (a_sp A) (Z_to_bv 64 (a_P A)) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 (S + 64036)) x21 (Z_to_bv 64 2147450880) x23 x24 x25 (Z_to_bv 64 S) (Z_to_bv 64 (a_shf A)) x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0xaa988) (a_fc A) None m (seg_rom b0segs)).
  Proof.
    intros Q HRET. intros until w752. intros DM FRL FRH AF ST MU WM MI DP NB FU HK.
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN. pose proof rnums_words_length as RNL. lin_natZ RNL.
    unfold_W14 MU. open_ash ASH AOK. pose proof (proj2 ANS : saddr S (a_shs A)) as ANS0. pose proof (proj1 ANS) as S8. pose proof (proj1 ANT) as STRM8.
    pose proof (act_sep_s_strm _ _ AOK : id _) as SEPst.
    destruct s as [inp sout sav stin stout]. cbn [s_in s_out s_avail_out s_tin s_tout] in *.
    pose proof DM as DM0. open_dmemF DM. b0img. cbn [s_in s_out s_avail_out s_tin s_tout] in *.
    destruct (fuel_ok_pos _ _ _ (proj1 (dpureF_bl _ _ _ _ _ _ DP)) FU) as [f EF]. subst F.
    pose proof (drun_gbst f 17 L d (DSTRM inp sout sav stin stout)) as MD. apply (fuel_ok_gbst _ _ 17) in FU.
    pose proof (dpureF_in _ _ _ _ _ _ DP) as IR.
    set (bl := d_bsLive d) in *. set (bb := d_bsBuff d) in *.
    hide_all_but (HD, STRM, FRL, FRH).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (munch_refl [(S, S + 68); (b_strm cx, b_strm cx + 20); (a_P A, a_P A + 128); (a_P A + 344, a_P A + 760)]%Z mm) as MUL;
      pose proof (wmono_refl b0segs mm) as WML end.
    brun. if_cases K; zify_cond_z K.
    { (* [comment removed for export] *)
      brun_to 0xaa9d0%Z. sh_norm.
      gbA_exit HK MUL WML DP MD FU 8%Z.
    }
    { (* [comment removed for export] *)
      brun. if_cases K2_1; zify_cond K2_1.
      { (* [comment removed for export] *)
        assert (AI1 : (1 <= Z.of_nat (length inp))%Z) by (lin_unbox LIN; clear - K2_1 LIN; zb_masks; mlia). clear K2_1. destruct inp as [|bz1 inp1]; [exfalso; cbn in AI1; lia|]. destruct (in_rel_head (a_payload A) _ _ _ IR eq_refl) as [b8_1 [NTH1 Ebz1]]. cbn [s_in length] in NTH1. cbn [length] in *. rewrite Nat2Z.inj_succ in *. subst bz1.
        brun_to 0xad418%Z. forget_reg 1%Z wj1_1. forget_reg 24%Z wj24_1.
        ack_rd (b_src cx + (b_len cx - Z.succ (Z.of_nat (length inp1))))%Z 1%Z.
        brun_to 0xad420%Z. ack_merge.
        brun_to 0xad424%Z.
        pose proof (GbKitB.gbF_payload_tr _ _ AOK DI_B0 _ _ _ _ _ DM0 MUL) as PAYL. b0img.
        pose proof (u8ro_read b0segs _ (b_src cx) (a_payload A) (b_len cx - Z.succ (Z.of_nat (length inp1)))%Z b8_1 _ PAYL ltac:(rewrite <- NTH1; f_equal; lia) ltac:(lia) eq_refl) as RD.
        (let pv := reg_val 16%Z in lazymatch pv with Z_to_bv 64 ?e => replace e with (b_src cx + (b_len cx - Z.succ (Z.of_nat (length inp1))))%Z by lia end).
        wstepl. clear RD PAYL.
        brun_to 0xad484%Z.
        (* [comment removed for export] *)
        cell_mod32 HD 32%nat. change (2^32)%Z with 4294967296%Z in HD. rewrite (pullw_mod32 bb b8_1) in HD by lia.
        set (bb1 := u32 (Z.lor (Z.shiftl bb 8) (bv_unsigned b8_1))) in *.
        pose proof (u32_range' (Z.lor (Z.shiftl bb 8) (bv_unsigned b8_1))) as Rbb1. change (u32 _) with bb1 in Rbb1.
        replace (b_src cx + (b_len cx - Z.succ (Z.of_nat (length inp1))) + 1)%Z with (b_src cx + (b_len cx - Z.of_nat (length inp1)))%Z in STRM by lia.
        replace (Z.succ (Z.of_nat (length inp1)) + -1)%Z with (Z.of_nat (length inp1)) in STRM by lia.
        erewrite (drun_pull_D _ _ _ _ _ _ 8%Z) in MD by first [reflexivity | cbn; lia]. change (u32 _) with bb1 in MD.
        apply (fuel_ok_pull_D _ _ _ _ _ bb1 _ _ _ _ _ (stin + 1)) in FU.
        destruct (fuel_ok_gbst_S _ _ _ _ _ _ FU ltac:(lia)) as [f1 Ef1]. subst f.
        pose proof (in_rel_tail _ _ (DSTRM inp1 sout sav (stin + 1) stout) _ _ IR eq_refl eq_refl) as IR1.
        til_joinA 16%Z 0xad49c%Z HD STRM FRL FRH ST MU WM MI MUL WML.
        { brun. if_cases K3_1; [ til_useA JN | brun_to 0xad49c%Z; til_useA JN ]. }
        brun. if_false_z.
        brun_to 0xaa9d0%Z. sh_norm.
        gbA_exit HK MUL WML DP MD FU 8%Z.
      }
      { (* [comment removed for export] *)
        assert (inp = []) as -> by (lin_unbox LIN; destruct inp; [reflexivity| exfalso; cbn [length] in K2_1, LIN; rewrite Nat2Z.inj_succ in K2_1, LIN; clear -K2_1 LIN; zb_masks; mlia]). clear K2_1.
        brun_to 0xa9f7c%Z.
        gbA_ret HRET MUL WML DP MD NB 8%Z.
      }
    }
  Qed.

  (* [comment removed for export] *)
  Lemma B0F_gb_aa754 : forall (Q : dres -> machine_state -> Prop), B0F_RET_OK A Q ->
    forall (F : nat) (L : dsv) (d : dst) (s : dstrm) (J : jk)
           (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x23 x24 x25 x28 x29 x30 x31 : word)
           (m : word -> option byte)
           (w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 : word)
           (w344 w352 w360 w368 w376 w384 w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 w496 w504 w520 w528 w720 w728 w736 w744 w752 : word),
    dmem DI_B0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J d s) ->
    B0FL A m w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 ->
    B0FH A m w344 w352 w360 w368 w376 w384 (Z_to_bv 64 (a_shs A)) w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 (Z_to_bv 64 (sv_nblock L)) w496 w504 (Z_to_bv 64 (a_fb A)) w520 w528 (Z_to_bv 64 (a_shs A + 1)) w720 w728 w736 w744 w752 ->
    aframe A m ->
    stk b0segs m (a_lo A) (a_P A) ->
    munch W (a_m0 A) m -> wmono b0segs (a_m0 A) m -> mem_inv b0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J d s ->
    (0 <= sv_nblock L <= 900000)%Z ->
    fuel_ok F d s ->
    (forall (F1 : nat) (bb' bl' : Z) (inp' : list Z) (tin' : Z) (til' tih' : word) (m' : word -> option byte),
       let d2 := gbst d 18 bb' bl' in
       let s1 := DSTRM inp' (s_out s) (s_avail_out s) tin' (s_tout s) in
       drun F 18 L d s = dgo F1 (gb_after 18 (gbval bb' bl' 8) L (d_set_bsLive d2 (bl' - 8)) s1) ->
       fuel_ok F1 (d_set_bsLive d2 (bl' - 8)) s1 -> (F1 < F)%nat ->
       dmem DI_B0 cx (a_g1 A) (a_sv A) (a_payload A) m' (dvF cx (jk_set_t J til' tih') d2 s1) ->
       aframe A m' ->
       stk b0segs m' (a_lo A) (a_P A) ->
       munch W (a_m0 A) m' -> wmono b0segs (a_m0 A) m' -> mem_inv b0segs m' ->
       dpureF cx (a_b0 A) (a_payload A) (jk_set_t J til' tih') d2 s1 ->
       (0 <= bb' < 2^32)%Z -> (8 <= bl' <= 32)%Z ->
       (8 * Z.of_nat (length inp') + bl' = 8 * Z.of_nat (length (s_in s)) + d_bsLive d)%Z ->
       forall (y1 y7 y12 y13 y14 y15 y16 y18 y19 y21 y23 y24 y25 y28 y29 y30 y31 yw32 yw40 yw48 yw56 : word),
       B0FL A m' w0 w8 w16 w24 yw32 yw40 yw48 yw56 w64 w72 w80 w88 w96 w104 w112 w120 ->
       B0FH A m' w344 w352 w360 w368 w376 w384 (Z_to_bv 64 (a_shs A)) w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 (Z_to_bv 64 (sv_nblock L)) w496 w504 (Z_to_bv 64 (a_fb A)) w520 w528 (Z_to_bv 64 (a_shs A + 1)) w720 w728 w736 w744 w752 ->
       evt b0segs (Q (drun F 18 L d s))
         (MS (mkR y1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) (Z_to_bv 64 (a_shs A + -2147450876)) (Z_to_bv 64 (bl')) y7 (a_sp A) (Z_to_bv 64 (a_P A)) (Z_to_bv 64 (S + 36)) (Z_to_bv 64 (S + 32)) y12 y13 y14 y15 y16 (Z_to_bv 64 (a_shs A + 4)) y18 y19 (Z_to_bv 64 (S + 64036)) y21 (Z_to_bv 64 2147450880) y23 y24 y25 (Z_to_bv 64 S) (Z_to_bv 64 (a_shf A)) y28 y29 y30 y31)
             (a_F A) (Z_to_bv 64 0xaaa60) (a_fc A) None m' (seg_rom b0segs))) ->
    evt b0segs (Q (drun F 18 L d s))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) x5 x6 x7 (a_sp A) (Z_to_bv 64 (a_P A)) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 (S + 64036)) x21 (Z_to_bv 64 2147450880) x23 x24 x25 (Z_to_bv 64 S) (Z_to_bv 64 (a_shf A)) x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0xaaa18) (a_fc A) None m (seg_rom b0segs)).
  Proof.
    intros Q HRET. intros until w752. intros DM FRL FRH AF ST MU WM MI DP NB FU HK.
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN. pose proof rnums_words_length as RNL. lin_natZ RNL.
    unfold_W14 MU. open_ash ASH AOK. pose proof (proj2 ANS : saddr S (a_shs A)) as ANS0. pose proof (proj1 ANS) as S8. pose proof (proj1 ANT) as STRM8.
    pose proof (act_sep_s_strm _ _ AOK : id _) as SEPst.
    destruct s as [inp sout sav stin stout]. cbn [s_in s_out s_avail_out s_tin s_tout] in *.
    pose proof DM as DM0. open_dmemF DM. b0img. cbn [s_in s_out s_avail_out s_tin s_tout] in *.
    destruct (fuel_ok_pos _ _ _ (proj1 (dpureF_bl _ _ _ _ _ _ DP)) FU) as [f EF]. subst F.
    pose proof (drun_gbst f 18 L d (DSTRM inp sout sav stin stout)) as MD. apply (fuel_ok_gbst _ _ 18) in FU.
    pose proof (dpureF_in _ _ _ _ _ _ DP) as IR.
    set (bl := d_bsLive d) in *. set (bb := d_bsBuff d) in *.
    hide_all_but (HD, STRM, FRL, FRH).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (munch_refl [(S, S + 68); (b_strm cx, b_strm cx + 20); (a_P A, a_P A + 128); (a_P A + 344, a_P A + 760)]%Z mm) as MUL;
      pose proof (wmono_refl b0segs mm) as WML end.
    brun. if_cases K; zify_cond_z K.
    { (* [comment removed for export] *)
      brun_to 0xaaa60%Z. sh_norm.
      gbA_exit HK MUL WML DP MD FU 8%Z.
    }
    { (* [comment removed for export] *)
      brun. if_cases K2_1; zify_cond K2_1.
      { (* [comment removed for export] *)
        assert (AI1 : (1 <= Z.of_nat (length inp))%Z) by (lin_unbox LIN; clear - K2_1 LIN; zb_masks; mlia). clear K2_1. destruct inp as [|bz1 inp1]; [exfalso; cbn in AI1; lia|]. destruct (in_rel_head (a_payload A) _ _ _ IR eq_refl) as [b8_1 [NTH1 Ebz1]]. cbn [s_in length] in NTH1. cbn [length] in *. rewrite Nat2Z.inj_succ in *. subst bz1.
        brun_to 0xad0a8%Z. forget_reg 1%Z wj1_1. forget_reg 24%Z wj24_1.
        ack_rd (b_src cx + (b_len cx - Z.succ (Z.of_nat (length inp1))))%Z 1%Z.
        brun_to 0xad0b0%Z. ack_merge.
        brun_to 0xad0b4%Z.
        pose proof (GbKitB.gbF_payload_tr _ _ AOK DI_B0 _ _ _ _ _ DM0 MUL) as PAYL. b0img.
        pose proof (u8ro_read b0segs _ (b_src cx) (a_payload A) (b_len cx - Z.succ (Z.of_nat (length inp1)))%Z b8_1 _ PAYL ltac:(rewrite <- NTH1; f_equal; lia) ltac:(lia) eq_refl) as RD.
        (let pv := reg_val 16%Z in lazymatch pv with Z_to_bv 64 ?e => replace e with (b_src cx + (b_len cx - Z.succ (Z.of_nat (length inp1))))%Z by lia end).
        wstepl. clear RD PAYL.
        brun_to 0xad114%Z.
        (* [comment removed for export] *)
        cell_mod32 HD 32%nat. change (2^32)%Z with 4294967296%Z in HD. rewrite (pullw_mod32 bb b8_1) in HD by lia.
        set (bb1 := u32 (Z.lor (Z.shiftl bb 8) (bv_unsigned b8_1))) in *.
        pose proof (u32_range' (Z.lor (Z.shiftl bb 8) (bv_unsigned b8_1))) as Rbb1. change (u32 _) with bb1 in Rbb1.
        replace (b_src cx + (b_len cx - Z.succ (Z.of_nat (length inp1))) + 1)%Z with (b_src cx + (b_len cx - Z.of_nat (length inp1)))%Z in STRM by lia.
        replace (Z.succ (Z.of_nat (length inp1)) + -1)%Z with (Z.of_nat (length inp1)) in STRM by lia.
        erewrite (drun_pull_D _ _ _ _ _ _ 8%Z) in MD by first [reflexivity | cbn; lia]. change (u32 _) with bb1 in MD.
        apply (fuel_ok_pull_D _ _ _ _ _ bb1 _ _ _ _ _ (stin + 1)) in FU.
        destruct (fuel_ok_gbst_S _ _ _ _ _ _ FU ltac:(lia)) as [f1 Ef1]. subst f.
        pose proof (in_rel_tail _ _ (DSTRM inp1 sout sav (stin + 1) stout) _ _ IR eq_refl eq_refl) as IR1.
        til_joinA 16%Z 0xad12c%Z HD STRM FRL FRH ST MU WM MI MUL WML.
        { brun. if_cases K3_1; [ til_useA JN | brun_to 0xad12c%Z; til_useA JN ]. }
        brun. if_false_z.
        brun_to 0xaaa60%Z. sh_norm.
        gbA_exit HK MUL WML DP MD FU 8%Z.
      }
      { (* [comment removed for export] *)
        assert (inp = []) as -> by (lin_unbox LIN; destruct inp; [reflexivity| exfalso; cbn [length] in K2_1, LIN; rewrite Nat2Z.inj_succ in K2_1, LIN; clear -K2_1 LIN; zb_masks; mlia]). clear K2_1.
        brun_to 0xa9f7c%Z.
        gbA_ret HRET MUL WML DP MD NB 8%Z.
      }
    }
  Qed.

  (* [comment removed for export] *)
  Lemma B0F_gb_aa7e4 : forall (Q : dres -> machine_state -> Prop), B0F_RET_OK A Q ->
    forall (F : nat) (L : dsv) (d : dst) (s : dstrm) (J : jk)
           (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x23 x24 x25 x28 x29 x30 x31 : word)
           (m : word -> option byte)
           (w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 : word)
           (w344 w352 w360 w368 w376 w384 w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 w496 w504 w520 w528 w720 w728 w736 w744 w752 : word),
    dmem DI_B0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J d s) ->
    B0FL A m w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 ->
    B0FH A m w344 w352 w360 w368 w376 w384 (Z_to_bv 64 (a_shs A)) w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 (Z_to_bv 64 (sv_nblock L)) w496 w504 (Z_to_bv 64 (a_fb A)) w520 w528 (Z_to_bv 64 (a_shs A + 1)) w720 w728 w736 w744 w752 ->
    aframe A m ->
    stk b0segs m (a_lo A) (a_P A) ->
    munch W (a_m0 A) m -> wmono b0segs (a_m0 A) m -> mem_inv b0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J d s ->
    (0 <= sv_nblock L <= 900000)%Z ->
    fuel_ok F d s ->
    (forall (F1 : nat) (bb' bl' : Z) (inp' : list Z) (tin' : Z) (til' tih' : word) (m' : word -> option byte),
       let d2 := gbst d 19 bb' bl' in
       let s1 := DSTRM inp' (s_out s) (s_avail_out s) tin' (s_tout s) in
       drun F 19 L d s = dgo F1 (gb_after 19 (gbval bb' bl' 8) L (d_set_bsLive d2 (bl' - 8)) s1) ->
       fuel_ok F1 (d_set_bsLive d2 (bl' - 8)) s1 -> (F1 < F)%nat ->
       dmem DI_B0 cx (a_g1 A) (a_sv A) (a_payload A) m' (dvF cx (jk_set_t J til' tih') d2 s1) ->
       aframe A m' ->
       stk b0segs m' (a_lo A) (a_P A) ->
       munch W (a_m0 A) m' -> wmono b0segs (a_m0 A) m' -> mem_inv b0segs m' ->
       dpureF cx (a_b0 A) (a_payload A) (jk_set_t J til' tih') d2 s1 ->
       (0 <= bb' < 2^32)%Z -> (8 <= bl' <= 32)%Z ->
       (8 * Z.of_nat (length inp') + bl' = 8 * Z.of_nat (length (s_in s)) + d_bsLive d)%Z ->
       forall (y1 y7 y12 y13 y14 y15 y16 y18 y19 y21 y23 y24 y25 y28 y29 y30 y31 yw32 yw40 yw48 yw56 : word),
       B0FL A m' w0 w8 w16 w24 yw32 yw40 yw48 yw56 w64 w72 w80 w88 w96 w104 w112 w120 ->
       B0FH A m' w344 w352 w360 w368 w376 w384 (Z_to_bv 64 (a_shs A)) w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 (Z_to_bv 64 (sv_nblock L)) w496 w504 (Z_to_bv 64 (a_fb A)) w520 w528 (Z_to_bv 64 (a_shs A + 1)) w720 w728 w736 w744 w752 ->
       evt b0segs (Q (drun F 19 L d s))
         (MS (mkR y1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) (Z_to_bv 64 (a_shs A + -2147450876)) (Z_to_bv 64 (bl')) y7 (a_sp A) (Z_to_bv 64 (a_P A)) (Z_to_bv 64 (S + 36)) (Z_to_bv 64 (S + 32)) y12 y13 y14 y15 y16 (Z_to_bv 64 (a_shs A + 4)) y18 y19 (Z_to_bv 64 (S + 64036)) y21 (Z_to_bv 64 2147450880) y23 y24 y25 (Z_to_bv 64 S) (Z_to_bv 64 (a_shf A)) y28 y29 y30 y31)
             (a_F A) (Z_to_bv 64 0xaaaf0) (a_fc A) None m' (seg_rom b0segs))) ->
    evt b0segs (Q (drun F 19 L d s))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) x5 x6 x7 (a_sp A) (Z_to_bv 64 (a_P A)) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 (S + 64036)) x21 (Z_to_bv 64 2147450880) x23 x24 x25 (Z_to_bv 64 S) (Z_to_bv 64 (a_shf A)) x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0xaaaa8) (a_fc A) None m (seg_rom b0segs)).
  Proof.
    intros Q HRET. intros until w752. intros DM FRL FRH AF ST MU WM MI DP NB FU HK.
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN. pose proof rnums_words_length as RNL. lin_natZ RNL.
    unfold_W14 MU. open_ash ASH AOK. pose proof (proj2 ANS : saddr S (a_shs A)) as ANS0. pose proof (proj1 ANS) as S8. pose proof (proj1 ANT) as STRM8.
    pose proof (act_sep_s_strm _ _ AOK : id _) as SEPst.
    destruct s as [inp sout sav stin stout]. cbn [s_in s_out s_avail_out s_tin s_tout] in *.
    pose proof DM as DM0. open_dmemF DM. b0img. cbn [s_in s_out s_avail_out s_tin s_tout] in *.
    destruct (fuel_ok_pos _ _ _ (proj1 (dpureF_bl _ _ _ _ _ _ DP)) FU) as [f EF]. subst F.
    pose proof (drun_gbst f 19 L d (DSTRM inp sout sav stin stout)) as MD. apply (fuel_ok_gbst _ _ 19) in FU.
    pose proof (dpureF_in _ _ _ _ _ _ DP) as IR.
    set (bl := d_bsLive d) in *. set (bb := d_bsBuff d) in *.
    hide_all_but (HD, STRM, FRL, FRH).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (munch_refl [(S, S + 68); (b_strm cx, b_strm cx + 20); (a_P A, a_P A + 128); (a_P A + 344, a_P A + 760)]%Z mm) as MUL;
      pose proof (wmono_refl b0segs mm) as WML end.
    brun. if_cases K; zify_cond_z K.
    { (* [comment removed for export] *)
      brun_to 0xaaaf0%Z. sh_norm.
      gbA_exit HK MUL WML DP MD FU 8%Z.
    }
    { (* [comment removed for export] *)
      brun. if_cases K2_1; zify_cond K2_1.
      { (* [comment removed for export] *)
        assert (AI1 : (1 <= Z.of_nat (length inp))%Z) by (lin_unbox LIN; clear - K2_1 LIN; zb_masks; mlia). clear K2_1. destruct inp as [|bz1 inp1]; [exfalso; cbn in AI1; lia|]. destruct (in_rel_head (a_payload A) _ _ _ IR eq_refl) as [b8_1 [NTH1 Ebz1]]. cbn [s_in length] in NTH1. cbn [length] in *. rewrite Nat2Z.inj_succ in *. subst bz1.
        brun_to 0xacef0%Z. forget_reg 1%Z wj1_1. forget_reg 24%Z wj24_1.
        ack_rd (b_src cx + (b_len cx - Z.succ (Z.of_nat (length inp1))))%Z 1%Z.
        brun_to 0xacef8%Z. ack_merge.
        brun_to 0xacefc%Z.
        pose proof (GbKitB.gbF_payload_tr _ _ AOK DI_B0 _ _ _ _ _ DM0 MUL) as PAYL. b0img.
        pose proof (u8ro_read b0segs _ (b_src cx) (a_payload A) (b_len cx - Z.succ (Z.of_nat (length inp1)))%Z b8_1 _ PAYL ltac:(rewrite <- NTH1; f_equal; lia) ltac:(lia) eq_refl) as RD.
        (let pv := reg_val 16%Z in lazymatch pv with Z_to_bv 64 ?e => replace e with (b_src cx + (b_len cx - Z.succ (Z.of_nat (length inp1))))%Z by lia end).
        wstepl. clear RD PAYL.
        brun_to 0xacf5c%Z.
        (* [comment removed for export] *)
        cell_mod32 HD 32%nat. change (2^32)%Z with 4294967296%Z in HD. rewrite (pullw_mod32 bb b8_1) in HD by lia.
        set (bb1 := u32 (Z.lor (Z.shiftl bb 8) (bv_unsigned b8_1))) in *.
        pose proof (u32_range' (Z.lor (Z.shiftl bb 8) (bv_unsigned b8_1))) as Rbb1. change (u32 _) with bb1 in Rbb1.
        replace (b_src cx + (b_len cx - Z.succ (Z.of_nat (length inp1))) + 1)%Z with (b_src cx + (b_len cx - Z.of_nat (length inp1)))%Z in STRM by lia.
        replace (Z.succ (Z.of_nat (length inp1)) + -1)%Z with (Z.of_nat (length inp1)) in STRM by lia.
        erewrite (drun_pull_D _ _ _ _ _ _ 8%Z) in MD by first [reflexivity | cbn; lia]. change (u32 _) with bb1 in MD.
        apply (fuel_ok_pull_D _ _ _ _ _ bb1 _ _ _ _ _ (stin + 1)) in FU.
        destruct (fuel_ok_gbst_S _ _ _ _ _ _ FU ltac:(lia)) as [f1 Ef1]. subst f.
        pose proof (in_rel_tail _ _ (DSTRM inp1 sout sav (stin + 1) stout) _ _ IR eq_refl eq_refl) as IR1.
        til_joinA 16%Z 0xacf74%Z HD STRM FRL FRH ST MU WM MI MUL WML.
        { brun. if_cases K3_1; [ til_useA JN | brun_to 0xacf74%Z; til_useA JN ]. }
        brun. if_false_z.
        brun_to 0xaaaf0%Z. sh_norm.
        gbA_exit HK MUL WML DP MD FU 8%Z.
      }
      { (* [comment removed for export] *)
        assert (inp = []) as -> by (lin_unbox LIN; destruct inp; [reflexivity| exfalso; cbn [length] in K2_1, LIN; rewrite Nat2Z.inj_succ in K2_1, LIN; clear -K2_1 LIN; zb_masks; mlia]). clear K2_1.
        brun_to 0xa9f7c%Z.
        gbA_ret HRET MUL WML DP MD NB 8%Z.
      }
    }
  Qed.

End R.

End ACeilS1.
