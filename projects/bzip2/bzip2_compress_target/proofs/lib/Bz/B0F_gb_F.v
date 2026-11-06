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
  Lemma B0F_gb_b12ec : forall (Q : dres -> machine_state -> Prop), B0F_RET_OK A Q ->
    forall (F : nat) (L : dsv) (d : dst) (s : dstrm) (J : jk)
           (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x23 x24 x25 x28 x29 x30 x31 : word)
           (m : word -> option byte)
           (w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 : word)
           (w344 w352 w360 w368 w376 w384 w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 w496 w504 w520 w528 w720 w736 w744 w752 : word),
    dmem DI_B0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J d s) ->
    B0FL A m w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 ->
    B0FH A m w344 w352 w360 w368 w376 w384 (Z_to_bv 64 (a_shs A)) w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 (Z_to_bv 64 (sv_nblock L)) w496 w504 (Z_to_bv 64 (a_fb A)) w520 w528 (Z_to_bv 64 (a_shs A + 1)) w720 (Z_to_bv 64 (sv_zn L)) w736 w744 w752 ->
    aframe A m ->
    stk b0segs m (a_lo A) (a_P A) ->
    munch W (a_m0 A) m -> wmono b0segs (a_m0 A) m -> mem_inv b0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J d s ->
    (0 <= sv_nblock L <= 900000)%Z ->
    (1 <= sv_zn L <= 20)%Z ->
    fuel_ok F d s ->
    (forall (F1 : nat) (bb' bl' : Z) (inp' : list Z) (tin' : Z) (til' tih' : word) (m' : word -> option byte),
       let d2 := gbst d 36 bb' bl' in
       let s1 := DSTRM inp' (s_out s) (s_avail_out s) tin' (s_tout s) in
       drun F 36 L d s = dgo F1 (gb_after 36 (gbval bb' bl' (sv_zn L)) L (d_set_bsLive d2 (bl' - (sv_zn L))) s1) ->
       fuel_ok F1 (d_set_bsLive d2 (bl' - (sv_zn L))) s1 -> (F1 < F)%nat ->
       dmem DI_B0 cx (a_g1 A) (a_sv A) (a_payload A) m' (dvF cx (jk_set_t J til' tih') d2 s1) ->
       aframe A m' ->
       stk b0segs m' (a_lo A) (a_P A) ->
       munch W (a_m0 A) m' -> wmono b0segs (a_m0 A) m' -> mem_inv b0segs m' ->
       dpureF cx (a_b0 A) (a_payload A) (jk_set_t J til' tih') d2 s1 ->
       (0 <= bb' < 2^32)%Z -> (sv_zn L <= bl' <= 32)%Z ->
       (8 * Z.of_nat (length inp') + bl' = 8 * Z.of_nat (length (s_in s)) + d_bsLive d)%Z ->
       forall (y6 y7 y12 y13 y14 y15 y16 y18 y19 y21 y23 y24 y25 y29 y30 y31 yw64 yw80 yw88 yw112 : word),
       B0FL A m' w0 w8 w16 w24 w32 w40 w48 w56 yw64 w72 yw80 yw88 w96 w104 yw112 w120 ->
       B0FH A m' w344 w352 w360 w368 w376 w384 (Z_to_bv 64 (a_shs A)) w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 (Z_to_bv 64 (sv_nblock L)) w496 w504 (Z_to_bv 64 (a_fb A)) w520 w528 (Z_to_bv 64 (a_shs A + 1)) w720 (Z_to_bv 64 (sv_zn L)) w736 w744 w752 ->
       evt b0segs (Q (drun F 36 L d s))
         (MS (mkR (Z_to_bv 64 (bl')) (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) (Z_to_bv 64 (a_shs A + -2147450876)) y6 y7 (a_sp A) (Z_to_bv 64 (a_P A)) (Z_to_bv 64 (S + 36)) (Z_to_bv 64 (S + 32)) y12 y13 y14 y15 y16 (Z_to_bv 64 (a_shs A + 4)) y18 y19 (Z_to_bv 64 (S + 64036)) y21 (Z_to_bv 64 2147450880) y23 y24 y25 (Z_to_bv 64 S) (Z_to_bv 64 (a_shf A)) (Z_to_bv 64 (bl')) y29 y30 y31)
             (a_F A) (Z_to_bv 64 0xb1798) (a_fc A) None m' (seg_rom b0segs))) ->
    evt b0segs (Q (drun F 36 L d s))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) x5 x6 x7 (a_sp A) (Z_to_bv 64 (a_P A)) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 (S + 64036)) x21 (Z_to_bv 64 2147450880) x23 x24 x25 (Z_to_bv 64 S) (Z_to_bv 64 (a_shf A)) x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0xb15b0) (a_fc A) None m (seg_rom b0segs)).
  Proof.
    intros Q HRET. intros until w752. intros DM FRL FRH AF ST MU WM MI DP NB ZNR FU HK.
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN. pose proof rnums_words_length as RNL. lin_natZ RNL.
    unfold_W14 MU. open_ash ASH AOK. pose proof (proj2 ANS : saddr S (a_shs A)) as ANS0. pose proof (proj1 ANS) as S8. pose proof (proj1 ANT) as STRM8.
    pose proof (act_sep_s_strm _ _ AOK : id _) as SEPst.
    destruct s as [inp sout sav stin stout]. cbn [s_in s_out s_avail_out s_tin s_tout] in *.
    pose proof DM as DM0. open_dmemF DM. b0img. cbn [s_in s_out s_avail_out s_tin s_tout] in *.
    destruct (fuel_ok_pos _ _ _ (proj1 (dpureF_bl _ _ _ _ _ _ DP)) FU) as [f EF]. subst F.
    pose proof (drun_gbst f 36 L d (DSTRM inp sout sav stin stout)) as MD. apply (fuel_ok_gbst _ _ 36) in FU.
    pose proof (dpureF_in _ _ _ _ _ _ DP) as IR.
    set (bl := d_bsLive d) in *. set (bb := d_bsBuff d) in *.
    hide_all_but (HD, STRM, FRL, FRH).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (munch_refl [(S, S + 68); (b_strm cx, b_strm cx + 20); (a_P A, a_P A + 128); (a_P A + 344, a_P A + 760)]%Z mm) as MUL;
      pose proof (wmono_refl b0segs mm) as WML end.
    brun. if_cases K; zify_cond_z K.
    { (* [comment removed for export] *)
      brun_to 0xb1798%Z. sh_norm.
      gbA_exit HK MUL WML DP MD FU (sv_zn L).
    }
    { (* [comment removed for export] *)
      brun. if_cases K2_1; zify_cond K2_1.
      { (* [comment removed for export] *)
        assert (AI1 : (1 <= Z.of_nat (length inp))%Z) by (lin_unbox LIN; clear - K2_1 LIN; zb_masks; mlia). clear K2_1. destruct inp as [|bz1 inp1]; [exfalso; cbn in AI1; lia|]. destruct (in_rel_head (a_payload A) _ _ _ IR eq_refl) as [b8_1 [NTH1 Ebz1]]. cbn [s_in length] in NTH1. cbn [length] in *. rewrite Nat2Z.inj_succ in *. subst bz1.
        brun_to 0xb16b0%Z. forget_reg 23%Z wj23_1. forget_reg 25%Z wj25_1.
        ack_rd (b_src cx + (b_len cx - Z.succ (Z.of_nat (length inp1))))%Z 1%Z.
        brun_to 0xb16b8%Z. ack_merge.
        brun_to 0xb16bc%Z.
        pose proof (GbKitB.gbF_payload_tr _ _ AOK DI_B0 _ _ _ _ _ DM0 MUL) as PAYL. b0img.
        pose proof (u8ro_read b0segs _ (b_src cx) (a_payload A) (b_len cx - Z.succ (Z.of_nat (length inp1)))%Z b8_1 _ PAYL ltac:(rewrite <- NTH1; f_equal; lia) ltac:(lia) eq_refl) as RD.
        (let pv := reg_val 16%Z in lazymatch pv with Z_to_bv 64 ?e => replace e with (b_src cx + (b_len cx - Z.succ (Z.of_nat (length inp1))))%Z by lia end).
        wstepl. clear RD PAYL.
        brun_to 0xb1718%Z.
        (* [comment removed for export] *)
        cell_mod32 HD 32%nat. change (2^32)%Z with 4294967296%Z in HD. rewrite (pullw_mod32 bb b8_1) in HD by lia.
        set (bb1 := u32 (Z.lor (Z.shiftl bb 8) (bv_unsigned b8_1))) in *.
        pose proof (u32_range' (Z.lor (Z.shiftl bb 8) (bv_unsigned b8_1))) as Rbb1. change (u32 _) with bb1 in Rbb1.
        replace (b_src cx + (b_len cx - Z.succ (Z.of_nat (length inp1))) + 1)%Z with (b_src cx + (b_len cx - Z.of_nat (length inp1)))%Z in STRM by lia.
        replace (Z.succ (Z.of_nat (length inp1)) + -1)%Z with (Z.of_nat (length inp1)) in STRM by lia.
        erewrite (drun_pull_D _ _ _ _ _ _ (sv_zn L)) in MD by first [reflexivity | cbn; lia]. change (u32 _) with bb1 in MD.
        apply (fuel_ok_pull_D _ _ _ _ _ bb1 _ _ _ _ _ (stin + 1)) in FU.
        destruct (fuel_ok_gbst_S _ _ _ _ _ _ FU ltac:(lia)) as [f1 Ef1]. subst f.
        pose proof (in_rel_tail _ _ (DSTRM inp1 sout sav (stin + 1) stout) _ _ IR eq_refl eq_refl) as IR1.
        til_joinA 16%Z 0xb1730%Z HD STRM FRL FRH ST MU WM MI MUL WML.
        { brun. if_cases K3_1; [ til_useA JN | brun_to 0xb1730%Z; til_useA JN ]. }
        brun. if_cases KL1; zify_cond_z KL1.
        { (* [comment removed for export] *)
          brun_to 0xb1798%Z. sh_norm.
          gbA_exit HK MUL WML DP MD FU (sv_zn L).
        }
        { (* [comment removed for export] *)
          brun. if_cases K2_2; zify_cond K2_2.
          { (* [comment removed for export] *)
            assert (AI2 : (1 <= Z.of_nat (length inp1))%Z) by (lin_unbox LIN; clear - K2_2 LIN; zb_masks; mlia). clear K2_2. destruct inp1 as [|bz2 inp2]; [exfalso; cbn in AI2; lia|]. destruct (in_rel_head (a_payload A) _ _ _ IR1 eq_refl) as [b8_2 [NTH2 Ebz2]]. cbn [s_in length] in NTH2. cbn [length] in *. rewrite Nat2Z.inj_succ in *. subst bz2.
            brun_to 0xb16b0%Z. forget_reg 25%Z wj25_2.
            ack_rd (b_src cx + (b_len cx - Z.succ (Z.of_nat (length inp2))))%Z 1%Z.
            brun_to 0xb16b8%Z. ack_merge.
            brun_to 0xb16bc%Z.
            pose proof (GbKitB.gbF_payload_tr _ _ AOK DI_B0 _ _ _ _ _ DM0 MUL) as PAYL. b0img.
            pose proof (u8ro_read b0segs _ (b_src cx) (a_payload A) (b_len cx - Z.succ (Z.of_nat (length inp2)))%Z b8_2 _ PAYL ltac:(rewrite <- NTH2; f_equal; lia) ltac:(lia) eq_refl) as RD.
            (let pv := reg_val 16%Z in lazymatch pv with Z_to_bv 64 ?e => replace e with (b_src cx + (b_len cx - Z.succ (Z.of_nat (length inp2))))%Z by lia end).
            wstepl. clear RD PAYL.
            brun_to 0xb1718%Z.
            (* [comment removed for export] *)
            cell_mod32 HD 32%nat. change (2^32)%Z with 4294967296%Z in HD. rewrite (pullw_mod32 bb1 b8_2) in HD by lia.
            set (bb2 := u32 (Z.lor (Z.shiftl bb1 8) (bv_unsigned b8_2))) in *.
            pose proof (u32_range' (Z.lor (Z.shiftl bb1 8) (bv_unsigned b8_2))) as Rbb2. change (u32 _) with bb2 in Rbb2.
            replace (b_src cx + (b_len cx - Z.succ (Z.of_nat (length inp2))) + 1)%Z with (b_src cx + (b_len cx - Z.of_nat (length inp2)))%Z in STRM by lia.
            replace (Z.succ (Z.of_nat (length inp2)) + -1)%Z with (Z.of_nat (length inp2)) in STRM by lia.
            erewrite (drun_pull_D _ _ _ _ _ _ (sv_zn L)) in MD by first [reflexivity | cbn; lia]. change (u32 _) with bb2 in MD.
            apply (fuel_ok_pull_D _ _ _ _ _ bb2 _ _ _ _ _ (stin + 2)) in FU.
            destruct (fuel_ok_gbst_S _ _ _ _ _ _ FU ltac:(lia)) as [f2 Ef2]. subst f1.
            pose proof (in_rel_tail _ _ (DSTRM inp2 sout sav (stin + 2) stout) _ _ IR1 eq_refl eq_refl) as IR2.
            til_joinA 16%Z 0xb1730%Z HD STRM FRL FRH ST MU WM MI MUL WML.
            { brun. if_cases K3_2; [ til_useA JN | brun_to 0xb1730%Z; til_useA JN ]. }
            brun. if_cases KL2; zify_cond_z KL2.
            { (* [comment removed for export] *)
              brun_to 0xb1798%Z. sh_norm.
              gbA_exit HK MUL WML DP MD FU (sv_zn L).
            }
            { (* [comment removed for export] *)
              brun. if_cases K2_3; zify_cond K2_3.
              { (* [comment removed for export] *)
                assert (AI3 : (1 <= Z.of_nat (length inp2))%Z) by (lin_unbox LIN; clear - K2_3 LIN; zb_masks; mlia). clear K2_3. destruct inp2 as [|bz3 inp3]; [exfalso; cbn in AI3; lia|]. destruct (in_rel_head (a_payload A) _ _ _ IR2 eq_refl) as [b8_3 [NTH3 Ebz3]]. cbn [s_in length] in NTH3. cbn [length] in *. rewrite Nat2Z.inj_succ in *. subst bz3.
                brun_to 0xb16b0%Z. forget_reg 25%Z wj25_3.
                ack_rd (b_src cx + (b_len cx - Z.succ (Z.of_nat (length inp3))))%Z 1%Z.
                brun_to 0xb16b8%Z. ack_merge.
                brun_to 0xb16bc%Z.
                pose proof (GbKitB.gbF_payload_tr _ _ AOK DI_B0 _ _ _ _ _ DM0 MUL) as PAYL. b0img.
                pose proof (u8ro_read b0segs _ (b_src cx) (a_payload A) (b_len cx - Z.succ (Z.of_nat (length inp3)))%Z b8_3 _ PAYL ltac:(rewrite <- NTH3; f_equal; lia) ltac:(lia) eq_refl) as RD.
                (let pv := reg_val 16%Z in lazymatch pv with Z_to_bv 64 ?e => replace e with (b_src cx + (b_len cx - Z.succ (Z.of_nat (length inp3))))%Z by lia end).
                wstepl. clear RD PAYL.
                brun_to 0xb1718%Z.
                (* [comment removed for export] *)
                cell_mod32 HD 32%nat. change (2^32)%Z with 4294967296%Z in HD. rewrite (pullw_mod32 bb2 b8_3) in HD by lia.
                set (bb3 := u32 (Z.lor (Z.shiftl bb2 8) (bv_unsigned b8_3))) in *.
                pose proof (u32_range' (Z.lor (Z.shiftl bb2 8) (bv_unsigned b8_3))) as Rbb3. change (u32 _) with bb3 in Rbb3.
                replace (b_src cx + (b_len cx - Z.succ (Z.of_nat (length inp3))) + 1)%Z with (b_src cx + (b_len cx - Z.of_nat (length inp3)))%Z in STRM by lia.
                replace (Z.succ (Z.of_nat (length inp3)) + -1)%Z with (Z.of_nat (length inp3)) in STRM by lia.
                erewrite (drun_pull_D _ _ _ _ _ _ (sv_zn L)) in MD by first [reflexivity | cbn; lia]. change (u32 _) with bb3 in MD.
                apply (fuel_ok_pull_D _ _ _ _ _ bb3 _ _ _ _ _ (stin + 3)) in FU.
                destruct (fuel_ok_gbst_S _ _ _ _ _ _ FU ltac:(lia)) as [f3 Ef3]. subst f2.
                pose proof (in_rel_tail _ _ (DSTRM inp3 sout sav (stin + 3) stout) _ _ IR2 eq_refl eq_refl) as IR3.
                til_joinA 16%Z 0xb1730%Z HD STRM FRL FRH ST MU WM MI MUL WML.
                { brun. if_cases K3_3; [ til_useA JN | brun_to 0xb1730%Z; til_useA JN ]. }
                brun. if_true_z.
                brun_to 0xb1798%Z. sh_norm.
                gbA_exit HK MUL WML DP MD FU (sv_zn L).
              }
              { (* [comment removed for export] *)
                assert (inp2 = []) as -> by (lin_unbox LIN; destruct inp2; [reflexivity| exfalso; cbn [length] in K2_3, LIN; rewrite Nat2Z.inj_succ in K2_3, LIN; clear -K2_3 LIN; zb_masks; mlia]). clear K2_3.
                brun_to 0xa9f7c%Z.
                gbA_ret HRET MUL WML DP MD NB (sv_zn L).
              }
            }
          }
          { (* [comment removed for export] *)
            assert (inp1 = []) as -> by (lin_unbox LIN; destruct inp1; [reflexivity| exfalso; cbn [length] in K2_2, LIN; rewrite Nat2Z.inj_succ in K2_2, LIN; clear -K2_2 LIN; zb_masks; mlia]). clear K2_2.
            brun_to 0xa9f7c%Z.
            gbA_ret HRET MUL WML DP MD NB (sv_zn L).
          }
        }
      }
      { (* [comment removed for export] *)
        assert (inp = []) as -> by (lin_unbox LIN; destruct inp; [reflexivity| exfalso; cbn [length] in K2_1, LIN; rewrite Nat2Z.inj_succ in K2_1, LIN; clear -K2_1 LIN; zb_masks; mlia]). clear K2_1.
        brun_to 0xa9f7c%Z.
        gbA_ret HRET MUL WML DP MD NB (sv_zn L).
      }
    }
  Qed.

  (* [comment removed for export] *)
  Lemma B0F_gb_b49a4 : forall (Q : dres -> machine_state -> Prop), B0F_RET_OK A Q ->
    forall (F : nat) (L : dsv) (d : dst) (s : dstrm) (J : jk)
           (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x23 x24 x25 x28 x29 x30 x31 : word)
           (m : word -> option byte)
           (w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 : word)
           (w344 w352 w360 w368 w376 w384 w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 w496 w504 w520 w528 w720 w736 w744 w752 : word),
    dmem DI_B0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J d s) ->
    B0FL A m w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 ->
    B0FH A m w344 w352 w360 w368 w376 w384 (Z_to_bv 64 (a_shs A)) w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 (Z_to_bv 64 (sv_nblock L)) w496 w504 (Z_to_bv 64 (a_fb A)) w520 w528 (Z_to_bv 64 (a_shs A + 1)) w720 (Z_to_bv 64 (sv_zn L)) w736 w744 w752 ->
    aframe A m ->
    stk b0segs m (a_lo A) (a_P A) ->
    munch W (a_m0 A) m -> wmono b0segs (a_m0 A) m -> mem_inv b0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J d s ->
    (0 <= sv_nblock L <= 900000)%Z ->
    (1 <= sv_zn L <= 20)%Z ->
    fuel_ok F d s ->
    (forall (F1 : nat) (bb' bl' : Z) (inp' : list Z) (tin' : Z) (til' tih' : word) (m' : word -> option byte),
       let d2 := gbst d 38 bb' bl' in
       let s1 := DSTRM inp' (s_out s) (s_avail_out s) tin' (s_tout s) in
       drun F 38 L d s = dgo F1 (gb_after 38 (gbval bb' bl' (sv_zn L)) L (d_set_bsLive d2 (bl' - (sv_zn L))) s1) ->
       fuel_ok F1 (d_set_bsLive d2 (bl' - (sv_zn L))) s1 -> (F1 < F)%nat ->
       dmem DI_B0 cx (a_g1 A) (a_sv A) (a_payload A) m' (dvF cx (jk_set_t J til' tih') d2 s1) ->
       aframe A m' ->
       stk b0segs m' (a_lo A) (a_P A) ->
       munch W (a_m0 A) m' -> wmono b0segs (a_m0 A) m' -> mem_inv b0segs m' ->
       dpureF cx (a_b0 A) (a_payload A) (jk_set_t J til' tih') d2 s1 ->
       (0 <= bb' < 2^32)%Z -> (sv_zn L <= bl' <= 32)%Z ->
       (8 * Z.of_nat (length inp') + bl' = 8 * Z.of_nat (length (s_in s)) + d_bsLive d)%Z ->
       forall (y6 y7 y12 y13 y14 y15 y16 y18 y19 y21 y23 y24 y25 y29 y30 y31 yw64 yw80 yw88 yw112 : word),
       B0FL A m' w0 w8 w16 w24 w32 w40 w48 w56 yw64 w72 yw80 yw88 w96 w104 yw112 w120 ->
       B0FH A m' w344 w352 w360 w368 w376 w384 (Z_to_bv 64 (a_shs A)) w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 (Z_to_bv 64 (sv_nblock L)) w496 w504 (Z_to_bv 64 (a_fb A)) w520 w528 (Z_to_bv 64 (a_shs A + 1)) w720 (Z_to_bv 64 (sv_zn L)) w736 w744 w752 ->
       evt b0segs (Q (drun F 38 L d s))
         (MS (mkR (Z_to_bv 64 (bl')) (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) (Z_to_bv 64 (a_shs A + -2147450876)) y6 y7 (a_sp A) (Z_to_bv 64 (a_P A)) (Z_to_bv 64 (S + 36)) (Z_to_bv 64 (S + 32)) y12 y13 y14 y15 y16 (Z_to_bv 64 (a_shs A + 4)) y18 y19 (Z_to_bv 64 (S + 64036)) y21 (Z_to_bv 64 2147450880) y23 y24 y25 (Z_to_bv 64 S) (Z_to_bv 64 (a_shf A)) (Z_to_bv 64 (bl')) y29 y30 y31)
             (a_F A) (Z_to_bv 64 0xb4e60) (a_fc A) None m' (seg_rom b0segs))) ->
    evt b0segs (Q (drun F 38 L d s))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) x5 x6 x7 (a_sp A) (Z_to_bv 64 (a_P A)) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 (S + 64036)) x21 (Z_to_bv 64 2147450880) x23 x24 x25 (Z_to_bv 64 S) (Z_to_bv 64 (a_shf A)) x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0xb4c68) (a_fc A) None m (seg_rom b0segs)).
  Proof.
    intros Q HRET. intros until w752. intros DM FRL FRH AF ST MU WM MI DP NB ZNR FU HK.
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN. pose proof rnums_words_length as RNL. lin_natZ RNL.
    unfold_W14 MU. open_ash ASH AOK. pose proof (proj2 ANS : saddr S (a_shs A)) as ANS0. pose proof (proj1 ANS) as S8. pose proof (proj1 ANT) as STRM8.
    pose proof (act_sep_s_strm _ _ AOK : id _) as SEPst.
    destruct s as [inp sout sav stin stout]. cbn [s_in s_out s_avail_out s_tin s_tout] in *.
    pose proof DM as DM0. open_dmemF DM. b0img. cbn [s_in s_out s_avail_out s_tin s_tout] in *.
    destruct (fuel_ok_pos _ _ _ (proj1 (dpureF_bl _ _ _ _ _ _ DP)) FU) as [f EF]. subst F.
    pose proof (drun_gbst f 38 L d (DSTRM inp sout sav stin stout)) as MD. apply (fuel_ok_gbst _ _ 38) in FU.
    pose proof (dpureF_in _ _ _ _ _ _ DP) as IR.
    set (bl := d_bsLive d) in *. set (bb := d_bsBuff d) in *.
    hide_all_but (HD, STRM, FRL, FRH).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (munch_refl [(S, S + 68); (b_strm cx, b_strm cx + 20); (a_P A, a_P A + 128); (a_P A + 344, a_P A + 760)]%Z mm) as MUL;
      pose proof (wmono_refl b0segs mm) as WML end.
    brun. if_cases K; zify_cond_z K.
    { (* [comment removed for export] *)
      brun_to 0xb4e60%Z. sh_norm.
      gbA_exit HK MUL WML DP MD FU (sv_zn L).
    }
    { (* [comment removed for export] *)
      brun. if_cases K2_1; zify_cond K2_1.
      { (* [comment removed for export] *)
        assert (AI1 : (1 <= Z.of_nat (length inp))%Z) by (lin_unbox LIN; clear - K2_1 LIN; zb_masks; mlia). clear K2_1. destruct inp as [|bz1 inp1]; [exfalso; cbn in AI1; lia|]. destruct (in_rel_head (a_payload A) _ _ _ IR eq_refl) as [b8_1 [NTH1 Ebz1]]. cbn [s_in length] in NTH1. cbn [length] in *. rewrite Nat2Z.inj_succ in *. subst bz1.
        brun_to 0xb4d70%Z. forget_reg 23%Z wj23_1. forget_reg 25%Z wj25_1.
        ack_rd (b_src cx + (b_len cx - Z.succ (Z.of_nat (length inp1))))%Z 1%Z.
        brun_to 0xb4d78%Z. ack_merge.
        brun_to 0xb4d7c%Z.
        pose proof (GbKitB.gbF_payload_tr _ _ AOK DI_B0 _ _ _ _ _ DM0 MUL) as PAYL. b0img.
        pose proof (u8ro_read b0segs _ (b_src cx) (a_payload A) (b_len cx - Z.succ (Z.of_nat (length inp1)))%Z b8_1 _ PAYL ltac:(rewrite <- NTH1; f_equal; lia) ltac:(lia) eq_refl) as RD.
        (let pv := reg_val 16%Z in lazymatch pv with Z_to_bv 64 ?e => replace e with (b_src cx + (b_len cx - Z.succ (Z.of_nat (length inp1))))%Z by lia end).
        wstepl. clear RD PAYL.
        brun_to 0xb4de0%Z.
        (* [comment removed for export] *)
        cell_mod32 HD 32%nat. change (2^32)%Z with 4294967296%Z in HD. rewrite (pullw_mod32 bb b8_1) in HD by lia.
        set (bb1 := u32 (Z.lor (Z.shiftl bb 8) (bv_unsigned b8_1))) in *.
        pose proof (u32_range' (Z.lor (Z.shiftl bb 8) (bv_unsigned b8_1))) as Rbb1. change (u32 _) with bb1 in Rbb1.
        replace (b_src cx + (b_len cx - Z.succ (Z.of_nat (length inp1))) + 1)%Z with (b_src cx + (b_len cx - Z.of_nat (length inp1)))%Z in STRM by lia.
        replace (Z.succ (Z.of_nat (length inp1)) + -1)%Z with (Z.of_nat (length inp1)) in STRM by lia.
        erewrite (drun_pull_D _ _ _ _ _ _ (sv_zn L)) in MD by first [reflexivity | cbn; lia]. change (u32 _) with bb1 in MD.
        apply (fuel_ok_pull_D _ _ _ _ _ bb1 _ _ _ _ _ (stin + 1)) in FU.
        destruct (fuel_ok_gbst_S _ _ _ _ _ _ FU ltac:(lia)) as [f1 Ef1]. subst f.
        pose proof (in_rel_tail _ _ (DSTRM inp1 sout sav (stin + 1) stout) _ _ IR eq_refl eq_refl) as IR1.
        til_joinA 16%Z 0xb4df8%Z HD STRM FRL FRH ST MU WM MI MUL WML.
        { brun. if_cases K3_1; [ til_useA JN | brun_to 0xb4df8%Z; til_useA JN ]. }
        brun. if_cases KL1; zify_cond_z KL1.
        { (* [comment removed for export] *)
          brun_to 0xb4e60%Z. sh_norm.
          gbA_exit HK MUL WML DP MD FU (sv_zn L).
        }
        { (* [comment removed for export] *)
          brun. if_cases K2_2; zify_cond K2_2.
          { (* [comment removed for export] *)
            assert (AI2 : (1 <= Z.of_nat (length inp1))%Z) by (lin_unbox LIN; clear - K2_2 LIN; zb_masks; mlia). clear K2_2. destruct inp1 as [|bz2 inp2]; [exfalso; cbn in AI2; lia|]. destruct (in_rel_head (a_payload A) _ _ _ IR1 eq_refl) as [b8_2 [NTH2 Ebz2]]. cbn [s_in length] in NTH2. cbn [length] in *. rewrite Nat2Z.inj_succ in *. subst bz2.
            brun_to 0xb4d70%Z. forget_reg 25%Z wj25_2.
            ack_rd (b_src cx + (b_len cx - Z.succ (Z.of_nat (length inp2))))%Z 1%Z.
            brun_to 0xb4d78%Z. ack_merge.
            brun_to 0xb4d7c%Z.
            pose proof (GbKitB.gbF_payload_tr _ _ AOK DI_B0 _ _ _ _ _ DM0 MUL) as PAYL. b0img.
            pose proof (u8ro_read b0segs _ (b_src cx) (a_payload A) (b_len cx - Z.succ (Z.of_nat (length inp2)))%Z b8_2 _ PAYL ltac:(rewrite <- NTH2; f_equal; lia) ltac:(lia) eq_refl) as RD.
            (let pv := reg_val 16%Z in lazymatch pv with Z_to_bv 64 ?e => replace e with (b_src cx + (b_len cx - Z.succ (Z.of_nat (length inp2))))%Z by lia end).
            wstepl. clear RD PAYL.
            brun_to 0xb4de0%Z.
            (* [comment removed for export] *)
            cell_mod32 HD 32%nat. change (2^32)%Z with 4294967296%Z in HD. rewrite (pullw_mod32 bb1 b8_2) in HD by lia.
            set (bb2 := u32 (Z.lor (Z.shiftl bb1 8) (bv_unsigned b8_2))) in *.
            pose proof (u32_range' (Z.lor (Z.shiftl bb1 8) (bv_unsigned b8_2))) as Rbb2. change (u32 _) with bb2 in Rbb2.
            replace (b_src cx + (b_len cx - Z.succ (Z.of_nat (length inp2))) + 1)%Z with (b_src cx + (b_len cx - Z.of_nat (length inp2)))%Z in STRM by lia.
            replace (Z.succ (Z.of_nat (length inp2)) + -1)%Z with (Z.of_nat (length inp2)) in STRM by lia.
            erewrite (drun_pull_D _ _ _ _ _ _ (sv_zn L)) in MD by first [reflexivity | cbn; lia]. change (u32 _) with bb2 in MD.
            apply (fuel_ok_pull_D _ _ _ _ _ bb2 _ _ _ _ _ (stin + 2)) in FU.
            destruct (fuel_ok_gbst_S _ _ _ _ _ _ FU ltac:(lia)) as [f2 Ef2]. subst f1.
            pose proof (in_rel_tail _ _ (DSTRM inp2 sout sav (stin + 2) stout) _ _ IR1 eq_refl eq_refl) as IR2.
            til_joinA 16%Z 0xb4df8%Z HD STRM FRL FRH ST MU WM MI MUL WML.
            { brun. if_cases K3_2; [ til_useA JN | brun_to 0xb4df8%Z; til_useA JN ]. }
            brun. if_cases KL2; zify_cond_z KL2.
            { (* [comment removed for export] *)
              brun_to 0xb4e60%Z. sh_norm.
              gbA_exit HK MUL WML DP MD FU (sv_zn L).
            }
            { (* [comment removed for export] *)
              brun. if_cases K2_3; zify_cond K2_3.
              { (* [comment removed for export] *)
                assert (AI3 : (1 <= Z.of_nat (length inp2))%Z) by (lin_unbox LIN; clear - K2_3 LIN; zb_masks; mlia). clear K2_3. destruct inp2 as [|bz3 inp3]; [exfalso; cbn in AI3; lia|]. destruct (in_rel_head (a_payload A) _ _ _ IR2 eq_refl) as [b8_3 [NTH3 Ebz3]]. cbn [s_in length] in NTH3. cbn [length] in *. rewrite Nat2Z.inj_succ in *. subst bz3.
                brun_to 0xb4d70%Z. forget_reg 25%Z wj25_3.
                ack_rd (b_src cx + (b_len cx - Z.succ (Z.of_nat (length inp3))))%Z 1%Z.
                brun_to 0xb4d78%Z. ack_merge.
                brun_to 0xb4d7c%Z.
                pose proof (GbKitB.gbF_payload_tr _ _ AOK DI_B0 _ _ _ _ _ DM0 MUL) as PAYL. b0img.
                pose proof (u8ro_read b0segs _ (b_src cx) (a_payload A) (b_len cx - Z.succ (Z.of_nat (length inp3)))%Z b8_3 _ PAYL ltac:(rewrite <- NTH3; f_equal; lia) ltac:(lia) eq_refl) as RD.
                (let pv := reg_val 16%Z in lazymatch pv with Z_to_bv 64 ?e => replace e with (b_src cx + (b_len cx - Z.succ (Z.of_nat (length inp3))))%Z by lia end).
                wstepl. clear RD PAYL.
                brun_to 0xb4de0%Z.
                (* [comment removed for export] *)
                cell_mod32 HD 32%nat. change (2^32)%Z with 4294967296%Z in HD. rewrite (pullw_mod32 bb2 b8_3) in HD by lia.
                set (bb3 := u32 (Z.lor (Z.shiftl bb2 8) (bv_unsigned b8_3))) in *.
                pose proof (u32_range' (Z.lor (Z.shiftl bb2 8) (bv_unsigned b8_3))) as Rbb3. change (u32 _) with bb3 in Rbb3.
                replace (b_src cx + (b_len cx - Z.succ (Z.of_nat (length inp3))) + 1)%Z with (b_src cx + (b_len cx - Z.of_nat (length inp3)))%Z in STRM by lia.
                replace (Z.succ (Z.of_nat (length inp3)) + -1)%Z with (Z.of_nat (length inp3)) in STRM by lia.
                erewrite (drun_pull_D _ _ _ _ _ _ (sv_zn L)) in MD by first [reflexivity | cbn; lia]. change (u32 _) with bb3 in MD.
                apply (fuel_ok_pull_D _ _ _ _ _ bb3 _ _ _ _ _ (stin + 3)) in FU.
                destruct (fuel_ok_gbst_S _ _ _ _ _ _ FU ltac:(lia)) as [f3 Ef3]. subst f2.
                pose proof (in_rel_tail _ _ (DSTRM inp3 sout sav (stin + 3) stout) _ _ IR2 eq_refl eq_refl) as IR3.
                til_joinA 16%Z 0xb4df8%Z HD STRM FRL FRH ST MU WM MI MUL WML.
                { brun. if_cases K3_3; [ til_useA JN | brun_to 0xb4df8%Z; til_useA JN ]. }
                brun. if_true_z.
                brun_to 0xb4e60%Z. sh_norm.
                gbA_exit HK MUL WML DP MD FU (sv_zn L).
              }
              { (* [comment removed for export] *)
                assert (inp2 = []) as -> by (lin_unbox LIN; destruct inp2; [reflexivity| exfalso; cbn [length] in K2_3, LIN; rewrite Nat2Z.inj_succ in K2_3, LIN; clear -K2_3 LIN; zb_masks; mlia]). clear K2_3.
                brun_to 0xa9f7c%Z.
                gbA_ret HRET MUL WML DP MD NB (sv_zn L).
              }
            }
          }
          { (* [comment removed for export] *)
            assert (inp1 = []) as -> by (lin_unbox LIN; destruct inp1; [reflexivity| exfalso; cbn [length] in K2_2, LIN; rewrite Nat2Z.inj_succ in K2_2, LIN; clear -K2_2 LIN; zb_masks; mlia]). clear K2_2.
            brun_to 0xa9f7c%Z.
            gbA_ret HRET MUL WML DP MD NB (sv_zn L).
          }
        }
      }
      { (* [comment removed for export] *)
        assert (inp = []) as -> by (lin_unbox LIN; destruct inp; [reflexivity| exfalso; cbn [length] in K2_1, LIN; rewrite Nat2Z.inj_succ in K2_1, LIN; clear -K2_1 LIN; zb_masks; mlia]). clear K2_1.
        brun_to 0xa9f7c%Z.
        gbA_ret HRET MUL WML DP MD NB (sv_zn L).
      }
    }
  Qed.

End R.

End ACeilS1.
