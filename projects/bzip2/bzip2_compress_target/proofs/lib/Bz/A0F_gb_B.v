(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzDefs BzModel BzTac BzTac2 BzInv BzTables BzContracts.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK DecCutFA DecTacFA A0F_decV A0F_decRet.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import AsanKit.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutFA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decV OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decRet.
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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require GbKitA.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import GbTacA.
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
  Hypothesis AOK : act_ok AIHI0 A.
  Hypothesis ASH : act_sh DI_A0 A.

  Notation usp := (bv_unsigned (a_sp A)).
  Notation cx := (a_cx A).
  Notation S := (b_s (a_cx A)).
  Notation W := (W14 A).

  (* [comment removed for export] *)
  Lemma A0F_gb_9f5bc : forall (Q : dres -> machine_state -> Prop), A0F_RET_OK A Q ->
    forall (F : nat) (L : dsv) (d : dst) (s : dstrm) (J : jk)
           (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte)
           (w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word)
           (w496 w504 w512 w520 w528 w536 w544 w552 w568 w576 w584 w592 w600 w608 w616 w624 w632 w640 w656 w664 w680 w696 w704 w712 w720 : word),
    dmem DI_A0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J d s) ->
    A0FL A m w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 ->
    A0FH A m w496 w504 w512 w520 w528 w536 w544 w552 (Z_to_bv 64 (a_shs A)) w568 w576 w584 w592 w600 w608 w616 w624 w632 w640 (Z_to_bv 64 (sv_nblock L)) w656 w664 (Z_to_bv 64 (a_fb A)) w680 (Z_to_bv 64 (a_shs A + 1)) w696 w704 w712 w720 ->
    aframe A m ->
    stk a0segs m (a_lo A) (a_P A) ->
    munch W (a_m0 A) m -> wmono a0segs (a_m0 A) m -> mem_inv a0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J d s ->
    (0 <= sv_nblock L <= 900000)%Z ->
    fuel_ok F d s ->
    (forall (F1 : nat) (bb' bl' : Z) (inp' : list Z) (tin' : Z) (til' tih' : word) (m' : word -> option byte),
       let d2 := gbst d 20 bb' bl' in
       let s1 := DSTRM inp' (s_out s) (s_avail_out s) tin' (s_tout s) in
       drun F 20 L d s = dgo F1 (gb_after 20 (gbval bb' bl' 8) L (d_set_bsLive d2 (bl' - 8)) s1) ->
       fuel_ok F1 (d_set_bsLive d2 (bl' - 8)) s1 -> (F1 < F)%nat ->
       dmem DI_A0 cx (a_g1 A) (a_sv A) (a_payload A) m' (dvF cx (jk_set_t J til' tih') d2 s1) ->
       aframe A m' ->
       stk a0segs m' (a_lo A) (a_P A) ->
       munch W (a_m0 A) m' -> wmono a0segs (a_m0 A) m' -> mem_inv a0segs m' ->
       dpureF cx (a_b0 A) (a_payload A) (jk_set_t J til' tih') d2 s1 ->
       (0 <= bb' < 2^32)%Z -> (8 <= bl' <= 32)%Z ->
       (8 * Z.of_nat (length inp') + bl' = 8 * Z.of_nat (length (s_in s)) + d_bsLive d)%Z ->
       forall (y1 y6 y7 y11 y12 y13 y14 y15 y16 y18 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 yw16 : word),
       A0FL A m' w0 w8 yw16 w24 w32 w40 w48 w56 w64 w72 w80 w88 ->
       A0FH A m' w496 w504 w512 w520 w528 w536 w544 w552 (Z_to_bv 64 (a_shs A)) w568 w576 w584 w592 w600 w608 w616 w624 w632 w640 (Z_to_bv 64 (sv_nblock L)) w656 w664 (Z_to_bv 64 (a_fb A)) w680 (Z_to_bv 64 (a_shs A + 1)) w696 w704 w712 w720 ->
       evt a0segs (Q (drun F 20 L d s))
         (MS (mkR y1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) (Z_to_bv 64 (a_shs A + 4)) y6 y7 (a_sp A) (Z_to_bv 64 (a_P A)) (Z_to_bv 64 (S + 36)) y11 y12 y13 y14 y15 y16 (Z_to_bv 64 (bl')) y18 (Z_to_bv 64 (S + 64036)) (Z_to_bv 64 S) (Z_to_bv 64 2147450880) y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
             (a_F A) (Z_to_bv 64 0x9f918) (a_fc A) None m' (seg_rom a0segs))) ->
    evt a0segs (Q (drun F 20 L d s))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) x5 x6 x7 (a_sp A) (Z_to_bv 64 (a_P A)) x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (S + 64036)) (Z_to_bv 64 S) (Z_to_bv 64 2147450880) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0x9f8d8) (a_fc A) None m (seg_rom a0segs)).
  Proof.
    intros Q HRET. intros until w720. intros DM FRL FRH AF ST MU WM MI DP NB FU HK.
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN. pose proof rnums_words_length as RNL. lin_natZ RNL.
    unfold_W14 MU. open_ash ASH AOK. pose proof (proj2 ANS : saddr S (a_shs A)) as ANS0.
    pose proof (act_sep_s_strm _ _ AOK : id _) as SEPst.
    destruct s as [inp sout sav stin stout]. cbn [s_in s_out s_avail_out s_tin s_tout] in *.
    pose proof DM as DM0. open_dmemF DM. a0img. cbn [s_in s_out s_avail_out s_tin s_tout] in *.
    destruct (fuel_ok_pos _ _ _ (proj1 (dpureF_bl _ _ _ _ _ _ DP)) FU) as [f EF]. subst F.
    pose proof (drun_gbst f 20 L d (DSTRM inp sout sav stin stout)) as MD. apply (fuel_ok_gbst _ _ 20) in FU.
    pose proof (dpureF_in _ _ _ _ _ _ DP) as IR.
    set (bl := d_bsLive d) in *. set (bb := d_bsBuff d) in *.
    hide_all_but (HD, STRM, FRL, FRH).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (munch_refl [(S, S + 68); (b_strm cx, b_strm cx + 20); (a_P A, a_P A + 96); (a_P A + 496, a_P A + 728)]%Z mm) as MUL;
      pose proof (wmono_refl a0segs mm) as WML end.
    arun. if_cases K; zify_cond_z K.
    { (* [comment removed for export] *)
      arun_to 0x9f918%Z. sh_norm.
      gbA_exit HK MUL WML DP MD FU 8%Z.
    }
    { (* [comment removed for export] *)
      arun. if_cases K2_1; zify_cond K2_1.
      { (* [comment removed for export] *)
        assert (AI1 : (1 <= Z.of_nat (length inp))%Z) by (lin_unbox LIN; clear - K2_1 LIN; zb_masks; mlia). clear K2_1. destruct inp as [|bz1 inp1]; [exfalso; cbn in AI1; lia|]. destruct (in_rel_head (a_payload A) _ _ _ IR eq_refl) as [b8_1 [NTH1 Ebz1]]. cbn [s_in length] in NTH1. cbn [length] in *. rewrite Nat2Z.inj_succ in *. subst bz1.
        arun_to 0xa1450%Z. forget_reg 1%Z wj1_1. forget_reg 22%Z wj22_1. forget_reg 23%Z wj23_1. forget_reg 30%Z wj30_1.
        ack_rd (b_src cx + (b_len cx - Z.succ (Z.of_nat (length inp1))))%Z 1%Z.
        arun_to 0xa1458%Z. ack_merge.
        arun_to 0xa145c%Z.
        pose proof (GbKitA.gbF_payload_tr _ _ AOK DI_A0 _ _ _ _ _ DM0 MUL) as PAYL. a0img.
        pose proof (u8ro_read a0segs _ (b_src cx) (a_payload A) (b_len cx - Z.succ (Z.of_nat (length inp1)))%Z b8_1 _ PAYL ltac:(rewrite <- NTH1; f_equal; lia) ltac:(lia) eq_refl) as RD.
        (let pv := reg_val 16%Z in lazymatch pv with Z_to_bv 64 ?e => replace e with (b_src cx + (b_len cx - Z.succ (Z.of_nat (length inp1))))%Z by lia end).
        wstepl. clear RD PAYL.
        arun_to 0xa14a4%Z.
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
        til_joinA 16%Z 0xa14bc%Z HD STRM FRL FRH ST MU WM MI MUL WML.
        { arun. if_cases K3_1; [ til_useA JN | arun_to 0xa14bc%Z; til_useA JN ]. }
        arun. if_false_z.
        arun_to 0x9f918%Z. sh_norm.
        gbA_exit HK MUL WML DP MD FU 8%Z.
      }
      { (* [comment removed for export] *)
        assert (inp = []) as -> by (lin_unbox LIN; destruct inp; [reflexivity| exfalso; cbn [length] in K2_1, LIN; rewrite Nat2Z.inj_succ in K2_1, LIN; clear -K2_1 LIN; zb_masks; mlia]). clear K2_1.
        arun_to 0x9eb34%Z.
        gbA_ret HRET MUL WML DP MD NB 8%Z.
      }
    }
  Qed.

  (* [comment removed for export] *)
  Lemma A0F_gb_9f65c : forall (Q : dres -> machine_state -> Prop), A0F_RET_OK A Q ->
    forall (F : nat) (L : dsv) (d : dst) (s : dstrm) (J : jk)
           (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte)
           (w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word)
           (w496 w504 w512 w520 w528 w536 w544 w552 w568 w576 w584 w592 w600 w608 w616 w624 w632 w640 w656 w664 w680 w696 w704 w712 w720 : word),
    dmem DI_A0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J d s) ->
    A0FL A m w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 ->
    A0FH A m w496 w504 w512 w520 w528 w536 w544 w552 (Z_to_bv 64 (a_shs A)) w568 w576 w584 w592 w600 w608 w616 w624 w632 w640 (Z_to_bv 64 (sv_nblock L)) w656 w664 (Z_to_bv 64 (a_fb A)) w680 (Z_to_bv 64 (a_shs A + 1)) w696 w704 w712 w720 ->
    aframe A m ->
    stk a0segs m (a_lo A) (a_P A) ->
    munch W (a_m0 A) m -> wmono a0segs (a_m0 A) m -> mem_inv a0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J d s ->
    (0 <= sv_nblock L <= 900000)%Z ->
    fuel_ok F d s ->
    (forall (F1 : nat) (bb' bl' : Z) (inp' : list Z) (tin' : Z) (til' tih' : word) (m' : word -> option byte),
       let d2 := gbst d 21 bb' bl' in
       let s1 := DSTRM inp' (s_out s) (s_avail_out s) tin' (s_tout s) in
       drun F 21 L d s = dgo F1 (gb_after 21 (gbval bb' bl' 8) L (d_set_bsLive d2 (bl' - 8)) s1) ->
       fuel_ok F1 (d_set_bsLive d2 (bl' - 8)) s1 -> (F1 < F)%nat ->
       dmem DI_A0 cx (a_g1 A) (a_sv A) (a_payload A) m' (dvF cx (jk_set_t J til' tih') d2 s1) ->
       aframe A m' ->
       stk a0segs m' (a_lo A) (a_P A) ->
       munch W (a_m0 A) m' -> wmono a0segs (a_m0 A) m' -> mem_inv a0segs m' ->
       dpureF cx (a_b0 A) (a_payload A) (jk_set_t J til' tih') d2 s1 ->
       (0 <= bb' < 2^32)%Z -> (8 <= bl' <= 32)%Z ->
       (8 * Z.of_nat (length inp') + bl' = 8 * Z.of_nat (length (s_in s)) + d_bsLive d)%Z ->
       forall (y1 y6 y7 y11 y12 y13 y14 y15 y16 y18 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 yw16 : word),
       A0FL A m' w0 w8 yw16 w24 w32 w40 w48 w56 w64 w72 w80 w88 ->
       A0FH A m' w496 w504 w512 w520 w528 w536 w544 w552 (Z_to_bv 64 (a_shs A)) w568 w576 w584 w592 w600 w608 w616 w624 w632 w640 (Z_to_bv 64 (sv_nblock L)) w656 w664 (Z_to_bv 64 (a_fb A)) w680 (Z_to_bv 64 (a_shs A + 1)) w696 w704 w712 w720 ->
       evt a0segs (Q (drun F 21 L d s))
         (MS (mkR y1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) (Z_to_bv 64 (a_shs A + 4)) y6 y7 (a_sp A) (Z_to_bv 64 (a_P A)) (Z_to_bv 64 (S + 36)) y11 y12 y13 y14 y15 y16 (Z_to_bv 64 (bl')) y18 (Z_to_bv 64 (S + 64036)) (Z_to_bv 64 S) (Z_to_bv 64 2147450880) y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
             (a_F A) (Z_to_bv 64 0x9f9b8) (a_fc A) None m' (seg_rom a0segs))) ->
    evt a0segs (Q (drun F 21 L d s))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) x5 x6 x7 (a_sp A) (Z_to_bv 64 (a_P A)) x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (S + 64036)) (Z_to_bv 64 S) (Z_to_bv 64 2147450880) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0x9f978) (a_fc A) None m (seg_rom a0segs)).
  Proof.
    intros Q HRET. intros until w720. intros DM FRL FRH AF ST MU WM MI DP NB FU HK.
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN. pose proof rnums_words_length as RNL. lin_natZ RNL.
    unfold_W14 MU. open_ash ASH AOK. pose proof (proj2 ANS : saddr S (a_shs A)) as ANS0.
    pose proof (act_sep_s_strm _ _ AOK : id _) as SEPst.
    destruct s as [inp sout sav stin stout]. cbn [s_in s_out s_avail_out s_tin s_tout] in *.
    pose proof DM as DM0. open_dmemF DM. a0img. cbn [s_in s_out s_avail_out s_tin s_tout] in *.
    destruct (fuel_ok_pos _ _ _ (proj1 (dpureF_bl _ _ _ _ _ _ DP)) FU) as [f EF]. subst F.
    pose proof (drun_gbst f 21 L d (DSTRM inp sout sav stin stout)) as MD. apply (fuel_ok_gbst _ _ 21) in FU.
    pose proof (dpureF_in _ _ _ _ _ _ DP) as IR.
    set (bl := d_bsLive d) in *. set (bb := d_bsBuff d) in *.
    hide_all_but (HD, STRM, FRL, FRH).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (munch_refl [(S, S + 68); (b_strm cx, b_strm cx + 20); (a_P A, a_P A + 96); (a_P A + 496, a_P A + 728)]%Z mm) as MUL;
      pose proof (wmono_refl a0segs mm) as WML end.
    arun. if_cases K; zify_cond_z K.
    { (* [comment removed for export] *)
      arun_to 0x9f9b8%Z. sh_norm.
      gbA_exit HK MUL WML DP MD FU 8%Z.
    }
    { (* [comment removed for export] *)
      arun. if_cases K2_1; zify_cond K2_1.
      { (* [comment removed for export] *)
        assert (AI1 : (1 <= Z.of_nat (length inp))%Z) by (lin_unbox LIN; clear - K2_1 LIN; zb_masks; mlia). clear K2_1. destruct inp as [|bz1 inp1]; [exfalso; cbn in AI1; lia|]. destruct (in_rel_head (a_payload A) _ _ _ IR eq_refl) as [b8_1 [NTH1 Ebz1]]. cbn [s_in length] in NTH1. cbn [length] in *. rewrite Nat2Z.inj_succ in *. subst bz1.
        arun_to 0xa1170%Z. forget_reg 1%Z wj1_1. forget_reg 22%Z wj22_1. forget_reg 23%Z wj23_1. forget_reg 30%Z wj30_1.
        ack_rd (b_src cx + (b_len cx - Z.succ (Z.of_nat (length inp1))))%Z 1%Z.
        arun_to 0xa1178%Z. ack_merge.
        arun_to 0xa117c%Z.
        pose proof (GbKitA.gbF_payload_tr _ _ AOK DI_A0 _ _ _ _ _ DM0 MUL) as PAYL. a0img.
        pose proof (u8ro_read a0segs _ (b_src cx) (a_payload A) (b_len cx - Z.succ (Z.of_nat (length inp1)))%Z b8_1 _ PAYL ltac:(rewrite <- NTH1; f_equal; lia) ltac:(lia) eq_refl) as RD.
        (let pv := reg_val 16%Z in lazymatch pv with Z_to_bv 64 ?e => replace e with (b_src cx + (b_len cx - Z.succ (Z.of_nat (length inp1))))%Z by lia end).
        wstepl. clear RD PAYL.
        arun_to 0xa11c4%Z.
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
        til_joinA 16%Z 0xa11dc%Z HD STRM FRL FRH ST MU WM MI MUL WML.
        { arun. if_cases K3_1; [ til_useA JN | arun_to 0xa11dc%Z; til_useA JN ]. }
        arun. if_false_z.
        arun_to 0x9f9b8%Z. sh_norm.
        gbA_exit HK MUL WML DP MD FU 8%Z.
      }
      { (* [comment removed for export] *)
        assert (inp = []) as -> by (lin_unbox LIN; destruct inp; [reflexivity| exfalso; cbn [length] in K2_1, LIN; rewrite Nat2Z.inj_succ in K2_1, LIN; clear -K2_1 LIN; zb_masks; mlia]). clear K2_1.
        arun_to 0x9eb34%Z.
        gbA_ret HRET MUL WML DP MD NB 8%Z.
      }
    }
  Qed.

  (* [comment removed for export] *)
  Lemma A0F_gb_9f6fc : forall (Q : dres -> machine_state -> Prop), A0F_RET_OK A Q ->
    forall (F : nat) (L : dsv) (d : dst) (s : dstrm) (J : jk)
           (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte)
           (w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word)
           (w496 w504 w512 w520 w528 w536 w544 w552 w568 w576 w584 w592 w600 w608 w616 w624 w632 w640 w656 w664 w680 w696 w704 w712 w720 : word),
    dmem DI_A0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J d s) ->
    A0FL A m w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 ->
    A0FH A m w496 w504 w512 w520 w528 w536 w544 w552 (Z_to_bv 64 (a_shs A)) w568 w576 w584 w592 w600 w608 w616 w624 w632 w640 (Z_to_bv 64 (sv_nblock L)) w656 w664 (Z_to_bv 64 (a_fb A)) w680 (Z_to_bv 64 (a_shs A + 1)) w696 w704 w712 w720 ->
    aframe A m ->
    stk a0segs m (a_lo A) (a_P A) ->
    munch W (a_m0 A) m -> wmono a0segs (a_m0 A) m -> mem_inv a0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J d s ->
    (0 <= sv_nblock L <= 900000)%Z ->
    fuel_ok F d s ->
    (forall (F1 : nat) (bb' bl' : Z) (inp' : list Z) (tin' : Z) (til' tih' : word) (m' : word -> option byte),
       let d2 := gbst d 22 bb' bl' in
       let s1 := DSTRM inp' (s_out s) (s_avail_out s) tin' (s_tout s) in
       drun F 22 L d s = dgo F1 (gb_after 22 (gbval bb' bl' 8) L (d_set_bsLive d2 (bl' - 8)) s1) ->
       fuel_ok F1 (d_set_bsLive d2 (bl' - 8)) s1 -> (F1 < F)%nat ->
       dmem DI_A0 cx (a_g1 A) (a_sv A) (a_payload A) m' (dvF cx (jk_set_t J til' tih') d2 s1) ->
       aframe A m' ->
       stk a0segs m' (a_lo A) (a_P A) ->
       munch W (a_m0 A) m' -> wmono a0segs (a_m0 A) m' -> mem_inv a0segs m' ->
       dpureF cx (a_b0 A) (a_payload A) (jk_set_t J til' tih') d2 s1 ->
       (0 <= bb' < 2^32)%Z -> (8 <= bl' <= 32)%Z ->
       (8 * Z.of_nat (length inp') + bl' = 8 * Z.of_nat (length (s_in s)) + d_bsLive d)%Z ->
       forall (y1 y6 y7 y11 y12 y13 y14 y15 y16 y18 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 yw16 : word),
       A0FL A m' w0 w8 yw16 w24 w32 w40 w48 w56 w64 w72 w80 w88 ->
       A0FH A m' w496 w504 w512 w520 w528 w536 w544 w552 (Z_to_bv 64 (a_shs A)) w568 w576 w584 w592 w600 w608 w616 w624 w632 w640 (Z_to_bv 64 (sv_nblock L)) w656 w664 (Z_to_bv 64 (a_fb A)) w680 (Z_to_bv 64 (a_shs A + 1)) w696 w704 w712 w720 ->
       evt a0segs (Q (drun F 22 L d s))
         (MS (mkR y1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) (Z_to_bv 64 (a_shs A + 4)) y6 y7 (a_sp A) (Z_to_bv 64 (a_P A)) (Z_to_bv 64 (S + 36)) y11 y12 y13 y14 y15 y16 (Z_to_bv 64 (bl')) y18 (Z_to_bv 64 (S + 64036)) (Z_to_bv 64 S) (Z_to_bv 64 2147450880) y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
             (a_F A) (Z_to_bv 64 0x9fa58) (a_fc A) None m' (seg_rom a0segs))) ->
    evt a0segs (Q (drun F 22 L d s))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) x5 x6 x7 (a_sp A) (Z_to_bv 64 (a_P A)) x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (S + 64036)) (Z_to_bv 64 S) (Z_to_bv 64 2147450880) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0x9fa18) (a_fc A) None m (seg_rom a0segs)).
  Proof.
    intros Q HRET. intros until w720. intros DM FRL FRH AF ST MU WM MI DP NB FU HK.
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN. pose proof rnums_words_length as RNL. lin_natZ RNL.
    unfold_W14 MU. open_ash ASH AOK. pose proof (proj2 ANS : saddr S (a_shs A)) as ANS0.
    pose proof (act_sep_s_strm _ _ AOK : id _) as SEPst.
    destruct s as [inp sout sav stin stout]. cbn [s_in s_out s_avail_out s_tin s_tout] in *.
    pose proof DM as DM0. open_dmemF DM. a0img. cbn [s_in s_out s_avail_out s_tin s_tout] in *.
    destruct (fuel_ok_pos _ _ _ (proj1 (dpureF_bl _ _ _ _ _ _ DP)) FU) as [f EF]. subst F.
    pose proof (drun_gbst f 22 L d (DSTRM inp sout sav stin stout)) as MD. apply (fuel_ok_gbst _ _ 22) in FU.
    pose proof (dpureF_in _ _ _ _ _ _ DP) as IR.
    set (bl := d_bsLive d) in *. set (bb := d_bsBuff d) in *.
    hide_all_but (HD, STRM, FRL, FRH).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (munch_refl [(S, S + 68); (b_strm cx, b_strm cx + 20); (a_P A, a_P A + 96); (a_P A + 496, a_P A + 728)]%Z mm) as MUL;
      pose proof (wmono_refl a0segs mm) as WML end.
    arun. if_cases K; zify_cond_z K.
    { (* [comment removed for export] *)
      arun_to 0x9fa58%Z. sh_norm.
      gbA_exit HK MUL WML DP MD FU 8%Z.
    }
    { (* [comment removed for export] *)
      arun. if_cases K2_1; zify_cond K2_1.
      { (* [comment removed for export] *)
        assert (AI1 : (1 <= Z.of_nat (length inp))%Z) by (lin_unbox LIN; clear - K2_1 LIN; zb_masks; mlia). clear K2_1. destruct inp as [|bz1 inp1]; [exfalso; cbn in AI1; lia|]. destruct (in_rel_head (a_payload A) _ _ _ IR eq_refl) as [b8_1 [NTH1 Ebz1]]. cbn [s_in length] in NTH1. cbn [length] in *. rewrite Nat2Z.inj_succ in *. subst bz1.
        arun_to 0xa0d14%Z. forget_reg 1%Z wj1_1. forget_reg 22%Z wj22_1. forget_reg 23%Z wj23_1. forget_reg 30%Z wj30_1.
        ack_rd (b_src cx + (b_len cx - Z.succ (Z.of_nat (length inp1))))%Z 1%Z.
        arun_to 0xa0d1c%Z. ack_merge.
        arun_to 0xa0d20%Z.
        pose proof (GbKitA.gbF_payload_tr _ _ AOK DI_A0 _ _ _ _ _ DM0 MUL) as PAYL. a0img.
        pose proof (u8ro_read a0segs _ (b_src cx) (a_payload A) (b_len cx - Z.succ (Z.of_nat (length inp1)))%Z b8_1 _ PAYL ltac:(rewrite <- NTH1; f_equal; lia) ltac:(lia) eq_refl) as RD.
        (let pv := reg_val 16%Z in lazymatch pv with Z_to_bv 64 ?e => replace e with (b_src cx + (b_len cx - Z.succ (Z.of_nat (length inp1))))%Z by lia end).
        wstepl. clear RD PAYL.
        arun_to 0xa0d68%Z.
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
        til_joinA 16%Z 0xa0d80%Z HD STRM FRL FRH ST MU WM MI MUL WML.
        { arun. if_cases K3_1; [ til_useA JN | arun_to 0xa0d80%Z; til_useA JN ]. }
        arun. if_false_z.
        arun_to 0x9fa58%Z. sh_norm.
        gbA_exit HK MUL WML DP MD FU 8%Z.
      }
      { (* [comment removed for export] *)
        assert (inp = []) as -> by (lin_unbox LIN; destruct inp; [reflexivity| exfalso; cbn [length] in K2_1, LIN; rewrite Nat2Z.inj_succ in K2_1, LIN; clear -K2_1 LIN; zb_masks; mlia]). clear K2_1.
        arun_to 0x9eb34%Z.
        gbA_ret HRET MUL WML DP MD NB 8%Z.
      }
    }
  Qed.

  (* [comment removed for export] *)
  Lemma A0F_gb_9f79c : forall (Q : dres -> machine_state -> Prop), A0F_RET_OK A Q ->
    forall (F : nat) (L : dsv) (d : dst) (s : dstrm) (J : jk)
           (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte)
           (w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word)
           (w496 w504 w512 w520 w528 w536 w544 w552 w568 w576 w584 w592 w600 w608 w616 w624 w632 w640 w656 w664 w680 w696 w704 w712 w720 : word),
    dmem DI_A0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J d s) ->
    A0FL A m w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 ->
    A0FH A m w496 w504 w512 w520 w528 w536 w544 w552 (Z_to_bv 64 (a_shs A)) w568 w576 w584 w592 w600 w608 w616 w624 w632 w640 (Z_to_bv 64 (sv_nblock L)) w656 w664 (Z_to_bv 64 (a_fb A)) w680 (Z_to_bv 64 (a_shs A + 1)) w696 w704 w712 w720 ->
    aframe A m ->
    stk a0segs m (a_lo A) (a_P A) ->
    munch W (a_m0 A) m -> wmono a0segs (a_m0 A) m -> mem_inv a0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J d s ->
    (0 <= sv_nblock L <= 900000)%Z ->
    fuel_ok F d s ->
    (forall (F1 : nat) (bb' bl' : Z) (inp' : list Z) (tin' : Z) (til' tih' : word) (m' : word -> option byte),
       let d2 := gbst d 23 bb' bl' in
       let s1 := DSTRM inp' (s_out s) (s_avail_out s) tin' (s_tout s) in
       drun F 23 L d s = dgo F1 (gb_after 23 (gbval bb' bl' 8) L (d_set_bsLive d2 (bl' - 8)) s1) ->
       fuel_ok F1 (d_set_bsLive d2 (bl' - 8)) s1 -> (F1 < F)%nat ->
       dmem DI_A0 cx (a_g1 A) (a_sv A) (a_payload A) m' (dvF cx (jk_set_t J til' tih') d2 s1) ->
       aframe A m' ->
       stk a0segs m' (a_lo A) (a_P A) ->
       munch W (a_m0 A) m' -> wmono a0segs (a_m0 A) m' -> mem_inv a0segs m' ->
       dpureF cx (a_b0 A) (a_payload A) (jk_set_t J til' tih') d2 s1 ->
       (0 <= bb' < 2^32)%Z -> (8 <= bl' <= 32)%Z ->
       (8 * Z.of_nat (length inp') + bl' = 8 * Z.of_nat (length (s_in s)) + d_bsLive d)%Z ->
       forall (y1 y6 y7 y11 y12 y13 y14 y15 y16 y18 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 yw16 : word),
       A0FL A m' w0 w8 yw16 w24 w32 w40 w48 w56 w64 w72 w80 w88 ->
       A0FH A m' w496 w504 w512 w520 w528 w536 w544 w552 (Z_to_bv 64 (a_shs A)) w568 w576 w584 w592 w600 w608 w616 w624 w632 w640 (Z_to_bv 64 (sv_nblock L)) w656 w664 (Z_to_bv 64 (a_fb A)) w680 (Z_to_bv 64 (a_shs A + 1)) w696 w704 w712 w720 ->
       evt a0segs (Q (drun F 23 L d s))
         (MS (mkR y1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) (Z_to_bv 64 (a_shs A + 4)) y6 y7 (a_sp A) (Z_to_bv 64 (a_P A)) (Z_to_bv 64 (S + 36)) y11 y12 y13 y14 y15 y16 (Z_to_bv 64 (bl')) y18 (Z_to_bv 64 (S + 64036)) (Z_to_bv 64 S) (Z_to_bv 64 2147450880) y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
             (a_F A) (Z_to_bv 64 0x9faf4) (a_fc A) None m' (seg_rom a0segs))) ->
    evt a0segs (Q (drun F 23 L d s))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) x5 x6 x7 (a_sp A) (Z_to_bv 64 (a_P A)) x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (S + 64036)) (Z_to_bv 64 S) (Z_to_bv 64 2147450880) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0x9fab8) (a_fc A) None m (seg_rom a0segs)).
  Proof.
    intros Q HRET. intros until w720. intros DM FRL FRH AF ST MU WM MI DP NB FU HK.
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN. pose proof rnums_words_length as RNL. lin_natZ RNL.
    unfold_W14 MU. open_ash ASH AOK. pose proof (proj2 ANS : saddr S (a_shs A)) as ANS0.
    pose proof (act_sep_s_strm _ _ AOK : id _) as SEPst.
    destruct s as [inp sout sav stin stout]. cbn [s_in s_out s_avail_out s_tin s_tout] in *.
    pose proof DM as DM0. open_dmemF DM. a0img. cbn [s_in s_out s_avail_out s_tin s_tout] in *.
    destruct (fuel_ok_pos _ _ _ (proj1 (dpureF_bl _ _ _ _ _ _ DP)) FU) as [f EF]. subst F.
    pose proof (drun_gbst f 23 L d (DSTRM inp sout sav stin stout)) as MD. apply (fuel_ok_gbst _ _ 23) in FU.
    pose proof (dpureF_in _ _ _ _ _ _ DP) as IR.
    set (bl := d_bsLive d) in *. set (bb := d_bsBuff d) in *.
    hide_all_but (HD, STRM, FRL, FRH).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (munch_refl [(S, S + 68); (b_strm cx, b_strm cx + 20); (a_P A, a_P A + 96); (a_P A + 496, a_P A + 728)]%Z mm) as MUL;
      pose proof (wmono_refl a0segs mm) as WML end.
    arun. if_cases K; zify_cond_z K.
    { (* [comment removed for export] *)
      arun. if_cases K2_1; zify_cond K2_1.
      { (* [comment removed for export] *)
        assert (AI1 : (1 <= Z.of_nat (length inp))%Z) by (lin_unbox LIN; clear - K2_1 LIN; zb_masks; mlia). clear K2_1. destruct inp as [|bz1 inp1]; [exfalso; cbn in AI1; lia|]. destruct (in_rel_head (a_payload A) _ _ _ IR eq_refl) as [b8_1 [NTH1 Ebz1]]. cbn [s_in length] in NTH1. cbn [length] in *. rewrite Nat2Z.inj_succ in *. subst bz1.
        arun_to 0xa0328%Z. forget_reg 1%Z wj1_1. forget_reg 22%Z wj22_1. forget_reg 23%Z wj23_1. forget_reg 30%Z wj30_1.
        ack_rd (b_src cx + (b_len cx - Z.succ (Z.of_nat (length inp1))))%Z 1%Z.
        arun_to 0xa0330%Z. ack_merge.
        arun_to 0xa0334%Z.
        pose proof (GbKitA.gbF_payload_tr _ _ AOK DI_A0 _ _ _ _ _ DM0 MUL) as PAYL. a0img.
        pose proof (u8ro_read a0segs _ (b_src cx) (a_payload A) (b_len cx - Z.succ (Z.of_nat (length inp1)))%Z b8_1 _ PAYL ltac:(rewrite <- NTH1; f_equal; lia) ltac:(lia) eq_refl) as RD.
        (let pv := reg_val 16%Z in lazymatch pv with Z_to_bv 64 ?e => replace e with (b_src cx + (b_len cx - Z.succ (Z.of_nat (length inp1))))%Z by lia end).
        wstepl. clear RD PAYL.
        arun_to 0xa037c%Z.
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
        til_joinA 16%Z 0xa0394%Z HD STRM FRL FRH ST MU WM MI MUL WML.
        { arun. if_cases K3_1; [ til_useA JN | arun_to 0xa0394%Z; til_useA JN ]. }
        arun. if_false_z.
        arun_to 0x9faf4%Z. sh_norm.
        gbA_exit HK MUL WML DP MD FU 8%Z.
      }
      { (* [comment removed for export] *)
        assert (inp = []) as -> by (lin_unbox LIN; destruct inp; [reflexivity| exfalso; cbn [length] in K2_1, LIN; rewrite Nat2Z.inj_succ in K2_1, LIN; clear -K2_1 LIN; zb_masks; mlia]). clear K2_1.
        arun_to 0x9eb34%Z.
        gbA_ret HRET MUL WML DP MD NB 8%Z.
      }
    }
    { (* [comment removed for export] *)
      arun_to 0x9faf4%Z. sh_norm.
      gbA_exit HK MUL WML DP MD FU 8%Z.
    }
  Qed.

  (* [comment removed for export] *)
  Lemma A0F_gb_9f838 : forall (Q : dres -> machine_state -> Prop), A0F_RET_OK A Q ->
    forall (F : nat) (L : dsv) (d : dst) (s : dstrm) (J : jk)
           (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte)
           (w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word)
           (w496 w504 w512 w520 w528 w536 w544 w552 w568 w576 w584 w592 w600 w608 w616 w624 w632 w640 w656 w664 w680 w696 w704 w712 w720 : word),
    dmem DI_A0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J d s) ->
    A0FL A m w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 ->
    A0FH A m w496 w504 w512 w520 w528 w536 w544 w552 (Z_to_bv 64 (a_shs A)) w568 w576 w584 w592 w600 w608 w616 w624 w632 w640 (Z_to_bv 64 (sv_nblock L)) w656 w664 (Z_to_bv 64 (a_fb A)) w680 (Z_to_bv 64 (a_shs A + 1)) w696 w704 w712 w720 ->
    aframe A m ->
    stk a0segs m (a_lo A) (a_P A) ->
    munch W (a_m0 A) m -> wmono a0segs (a_m0 A) m -> mem_inv a0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J d s ->
    (0 <= sv_nblock L <= 900000)%Z ->
    fuel_ok F d s ->
    (forall (F1 : nat) (bb' bl' : Z) (inp' : list Z) (tin' : Z) (til' tih' : word) (m' : word -> option byte),
       let d2 := gbst d 24 bb' bl' in
       let s1 := DSTRM inp' (s_out s) (s_avail_out s) tin' (s_tout s) in
       drun F 24 L d s = dgo F1 (gb_after 24 (gbval bb' bl' 1) L (d_set_bsLive d2 (bl' - 1)) s1) ->
       fuel_ok F1 (d_set_bsLive d2 (bl' - 1)) s1 -> (F1 < F)%nat ->
       dmem DI_A0 cx (a_g1 A) (a_sv A) (a_payload A) m' (dvF cx (jk_set_t J til' tih') d2 s1) ->
       aframe A m' ->
       stk a0segs m' (a_lo A) (a_P A) ->
       munch W (a_m0 A) m' -> wmono a0segs (a_m0 A) m' -> mem_inv a0segs m' ->
       dpureF cx (a_b0 A) (a_payload A) (jk_set_t J til' tih') d2 s1 ->
       (0 <= bb' < 2^32)%Z -> (1 <= bl' <= 32)%Z ->
       (8 * Z.of_nat (length inp') + bl' = 8 * Z.of_nat (length (s_in s)) + d_bsLive d)%Z ->
       forall (y1 y6 y7 y11 y12 y13 y14 y15 y16 y18 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 yw8 yw16 : word),
       A0FL A m' w0 yw8 yw16 w24 w32 w40 w48 w56 w64 w72 w80 w88 ->
       A0FH A m' w496 w504 w512 w520 w528 w536 w544 w552 (Z_to_bv 64 (a_shs A)) w568 w576 w584 w592 w600 w608 w616 w624 w632 w640 (Z_to_bv 64 (sv_nblock L)) w656 w664 (Z_to_bv 64 (a_fb A)) w680 (Z_to_bv 64 (a_shs A + 1)) w696 w704 w712 w720 ->
       evt a0segs (Q (drun F 24 L d s))
         (MS (mkR y1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) (Z_to_bv 64 (a_shs A + 4)) y6 y7 (a_sp A) (Z_to_bv 64 (a_P A)) (Z_to_bv 64 (S + 36)) y11 y12 y13 y14 y15 y16 (Z_to_bv 64 (bl')) y18 (Z_to_bv 64 (S + 64036)) (Z_to_bv 64 S) (Z_to_bv 64 2147450880) y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
             (a_F A) (Z_to_bv 64 0x9fb90) (a_fc A) None m' (seg_rom a0segs))) ->
    evt a0segs (Q (drun F 24 L d s))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) x5 x6 x7 (a_sp A) (Z_to_bv 64 (a_P A)) x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (S + 64036)) (Z_to_bv 64 S) (Z_to_bv 64 2147450880) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0x9fb54) (a_fc A) None m (seg_rom a0segs)).
  Proof.
    intros Q HRET. intros until w720. intros DM FRL FRH AF ST MU WM MI DP NB FU HK.
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN. pose proof rnums_words_length as RNL. lin_natZ RNL.
    unfold_W14 MU. open_ash ASH AOK. pose proof (proj2 ANS : saddr S (a_shs A)) as ANS0.
    pose proof (act_sep_s_strm _ _ AOK : id _) as SEPst.
    destruct s as [inp sout sav stin stout]. cbn [s_in s_out s_avail_out s_tin s_tout] in *.
    pose proof DM as DM0. open_dmemF DM. a0img. cbn [s_in s_out s_avail_out s_tin s_tout] in *.
    destruct (fuel_ok_pos _ _ _ (proj1 (dpureF_bl _ _ _ _ _ _ DP)) FU) as [f EF]. subst F.
    pose proof (drun_gbst f 24 L d (DSTRM inp sout sav stin stout)) as MD. apply (fuel_ok_gbst _ _ 24) in FU.
    pose proof (dpureF_in _ _ _ _ _ _ DP) as IR.
    set (bl := d_bsLive d) in *. set (bb := d_bsBuff d) in *.
    hide_all_but (HD, STRM, FRL, FRH).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (munch_refl [(S, S + 68); (b_strm cx, b_strm cx + 20); (a_P A, a_P A + 96); (a_P A + 496, a_P A + 728)]%Z mm) as MUL;
      pose proof (wmono_refl a0segs mm) as WML end.
    arun. if_cases K; zify_cond_z K.
    { (* [comment removed for export] *)
      arun_to 0x9fb90%Z. sh_norm.
      gbA_exit HK MUL WML DP MD FU 1%Z.
    }
    { (* [comment removed for export] *)
      arun. if_cases K2_1; zify_cond K2_1.
      { (* [comment removed for export] *)
        assert (AI1 : (1 <= Z.of_nat (length inp))%Z) by (lin_unbox LIN; clear - K2_1 LIN; zb_masks; mlia). clear K2_1. destruct inp as [|bz1 inp1]; [exfalso; cbn in AI1; lia|]. destruct (in_rel_head (a_payload A) _ _ _ IR eq_refl) as [b8_1 [NTH1 Ebz1]]. cbn [s_in length] in NTH1. cbn [length] in *. rewrite Nat2Z.inj_succ in *. subst bz1.
        arun_to 0xa0e8c%Z. forget_reg 26%Z wj26_1. forget_reg 23%Z wj23_1. forget_reg 25%Z wj25_1.
        ack_rd (b_src cx + (b_len cx - Z.succ (Z.of_nat (length inp1))))%Z 1%Z.
        arun_to 0xa0e94%Z. ack_merge.
        arun_to 0xa0e98%Z.
        pose proof (GbKitA.gbF_payload_tr _ _ AOK DI_A0 _ _ _ _ _ DM0 MUL) as PAYL. a0img.
        pose proof (u8ro_read a0segs _ (b_src cx) (a_payload A) (b_len cx - Z.succ (Z.of_nat (length inp1)))%Z b8_1 _ PAYL ltac:(rewrite <- NTH1; f_equal; lia) ltac:(lia) eq_refl) as RD.
        (let pv := reg_val 16%Z in lazymatch pv with Z_to_bv 64 ?e => replace e with (b_src cx + (b_len cx - Z.succ (Z.of_nat (length inp1))))%Z by lia end).
        wstepl. clear RD PAYL.
        arun_to 0xa0ee0%Z.
        (* [comment removed for export] *)
        cell_mod32 HD 32%nat. change (2^32)%Z with 4294967296%Z in HD. rewrite (pullw_mod32 bb b8_1) in HD by lia.
        set (bb1 := u32 (Z.lor (Z.shiftl bb 8) (bv_unsigned b8_1))) in *.
        pose proof (u32_range' (Z.lor (Z.shiftl bb 8) (bv_unsigned b8_1))) as Rbb1. change (u32 _) with bb1 in Rbb1.
        replace (b_src cx + (b_len cx - Z.succ (Z.of_nat (length inp1))) + 1)%Z with (b_src cx + (b_len cx - Z.of_nat (length inp1)))%Z in STRM by lia.
        replace (Z.succ (Z.of_nat (length inp1)) + -1)%Z with (Z.of_nat (length inp1)) in STRM by lia.
        erewrite (drun_pull_D _ _ _ _ _ _ 1%Z) in MD by first [reflexivity | cbn; lia]. change (u32 _) with bb1 in MD.
        apply (fuel_ok_pull_D _ _ _ _ _ bb1 _ _ _ _ _ (stin + 1)) in FU.
        destruct (fuel_ok_gbst_S _ _ _ _ _ _ FU ltac:(lia)) as [f1 Ef1]. subst f.
        pose proof (in_rel_tail _ _ (DSTRM inp1 sout sav (stin + 1) stout) _ _ IR eq_refl eq_refl) as IR1.
        til_joinA 16%Z 0xa0ef8%Z HD STRM FRL FRH ST MU WM MI MUL WML.
        { arun. if_cases K3_1; [ til_useA JN | arun_to 0xa0ef8%Z; til_useA JN ]. }
        arun. if_false_z.
        arun_to 0x9fb90%Z. sh_norm.
        gbA_exit HK MUL WML DP MD FU 1%Z.
      }
      { (* [comment removed for export] *)
        assert (inp = []) as -> by (lin_unbox LIN; destruct inp; [reflexivity| exfalso; cbn [length] in K2_1, LIN; rewrite Nat2Z.inj_succ in K2_1, LIN; clear -K2_1 LIN; zb_masks; mlia]). clear K2_1.
        arun_to 0x9eb34%Z.
        gbA_ret HRET MUL WML DP MD NB 1%Z.
      }
    }
  Qed.

  (* [comment removed for export] *)
  Lemma A0F_gb_9f8e4 : forall (Q : dres -> machine_state -> Prop), A0F_RET_OK A Q ->
    forall (F : nat) (L : dsv) (d : dst) (s : dstrm) (J : jk)
           (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte)
           (w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word)
           (w496 w504 w512 w520 w528 w536 w544 w552 w568 w576 w584 w592 w600 w608 w616 w624 w632 w640 w656 w664 w680 w696 w704 w712 w720 : word),
    dmem DI_A0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J d s) ->
    A0FL A m w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 ->
    A0FH A m w496 w504 w512 w520 w528 w536 w544 w552 (Z_to_bv 64 (a_shs A)) w568 w576 w584 w592 w600 w608 w616 w624 w632 w640 (Z_to_bv 64 (sv_nblock L)) w656 w664 (Z_to_bv 64 (a_fb A)) w680 (Z_to_bv 64 (a_shs A + 1)) w696 w704 w712 w720 ->
    aframe A m ->
    stk a0segs m (a_lo A) (a_P A) ->
    munch W (a_m0 A) m -> wmono a0segs (a_m0 A) m -> mem_inv a0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J d s ->
    (0 <= sv_nblock L <= 900000)%Z ->
    fuel_ok F d s ->
    (forall (F1 : nat) (bb' bl' : Z) (inp' : list Z) (tin' : Z) (til' tih' : word) (m' : word -> option byte),
       let d2 := gbst d 25 bb' bl' in
       let s1 := DSTRM inp' (s_out s) (s_avail_out s) tin' (s_tout s) in
       drun F 25 L d s = dgo F1 (gb_after 25 (gbval bb' bl' 8) L (d_set_bsLive d2 (bl' - 8)) s1) ->
       fuel_ok F1 (d_set_bsLive d2 (bl' - 8)) s1 -> (F1 < F)%nat ->
       dmem DI_A0 cx (a_g1 A) (a_sv A) (a_payload A) m' (dvF cx (jk_set_t J til' tih') d2 s1) ->
       aframe A m' ->
       stk a0segs m' (a_lo A) (a_P A) ->
       munch W (a_m0 A) m' -> wmono a0segs (a_m0 A) m' -> mem_inv a0segs m' ->
       dpureF cx (a_b0 A) (a_payload A) (jk_set_t J til' tih') d2 s1 ->
       (0 <= bb' < 2^32)%Z -> (8 <= bl' <= 32)%Z ->
       (8 * Z.of_nat (length inp') + bl' = 8 * Z.of_nat (length (s_in s)) + d_bsLive d)%Z ->
       forall (y1 y6 y7 y11 y12 y13 y14 y15 y16 y18 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 yw16 : word),
       A0FL A m' w0 w8 yw16 w24 w32 w40 w48 w56 w64 w72 w80 w88 ->
       A0FH A m' w496 w504 w512 w520 w528 w536 w544 w552 (Z_to_bv 64 (a_shs A)) w568 w576 w584 w592 w600 w608 w616 w624 w632 w640 (Z_to_bv 64 (sv_nblock L)) w656 w664 (Z_to_bv 64 (a_fb A)) w680 (Z_to_bv 64 (a_shs A + 1)) w696 w704 w712 w720 ->
       evt a0segs (Q (drun F 25 L d s))
         (MS (mkR y1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) (Z_to_bv 64 (a_shs A + 4)) y6 y7 (a_sp A) (Z_to_bv 64 (a_P A)) (Z_to_bv 64 (S + 36)) y11 y12 y13 y14 y15 y16 (Z_to_bv 64 (bl')) y18 (Z_to_bv 64 (S + 64036)) (Z_to_bv 64 S) (Z_to_bv 64 2147450880) y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
             (a_F A) (Z_to_bv 64 0x9fc3c) (a_fc A) None m' (seg_rom a0segs))) ->
    evt a0segs (Q (drun F 25 L d s))
      (MS (mkR x1 (Z_to_bv 64 (a_P A)) (a_gp A) (a_tp A) x5 x6 x7 (a_sp A) (Z_to_bv 64 (a_P A)) x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (S + 64036)) (Z_to_bv 64 S) (Z_to_bv 64 2147450880) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0x9fc00) (a_fc A) None m (seg_rom a0segs)).
  Proof.
    intros Q HRET. intros until w720. intros DM FRL FRH AF ST MU WM MI DP NB FU HK.
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN. pose proof rnums_words_length as RNL. lin_natZ RNL.
    unfold_W14 MU. open_ash ASH AOK. pose proof (proj2 ANS : saddr S (a_shs A)) as ANS0.
    pose proof (act_sep_s_strm _ _ AOK : id _) as SEPst.
    destruct s as [inp sout sav stin stout]. cbn [s_in s_out s_avail_out s_tin s_tout] in *.
    pose proof DM as DM0. open_dmemF DM. a0img. cbn [s_in s_out s_avail_out s_tin s_tout] in *.
    destruct (fuel_ok_pos _ _ _ (proj1 (dpureF_bl _ _ _ _ _ _ DP)) FU) as [f EF]. subst F.
    pose proof (drun_gbst f 25 L d (DSTRM inp sout sav stin stout)) as MD. apply (fuel_ok_gbst _ _ 25) in FU.
    pose proof (dpureF_in _ _ _ _ _ _ DP) as IR.
    set (bl := d_bsLive d) in *. set (bb := d_bsBuff d) in *.
    hide_all_but (HD, STRM, FRL, FRH).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (munch_refl [(S, S + 68); (b_strm cx, b_strm cx + 20); (a_P A, a_P A + 96); (a_P A + 496, a_P A + 728)]%Z mm) as MUL;
      pose proof (wmono_refl a0segs mm) as WML end.
    arun. if_cases K; zify_cond_z K.
    { (* [comment removed for export] *)
      arun. if_cases K2_1; zify_cond K2_1.
      { (* [comment removed for export] *)
        assert (AI1 : (1 <= Z.of_nat (length inp))%Z) by (lin_unbox LIN; clear - K2_1 LIN; zb_masks; mlia). clear K2_1. destruct inp as [|bz1 inp1]; [exfalso; cbn in AI1; lia|]. destruct (in_rel_head (a_payload A) _ _ _ IR eq_refl) as [b8_1 [NTH1 Ebz1]]. cbn [s_in length] in NTH1. cbn [length] in *. rewrite Nat2Z.inj_succ in *. subst bz1.
        arun_to 0xa01b8%Z. forget_reg 1%Z wj1_1. forget_reg 22%Z wj22_1. forget_reg 23%Z wj23_1. forget_reg 30%Z wj30_1.
        ack_rd (b_src cx + (b_len cx - Z.succ (Z.of_nat (length inp1))))%Z 1%Z.
        arun_to 0xa01c0%Z. ack_merge.
        arun_to 0xa01c4%Z.
        pose proof (GbKitA.gbF_payload_tr _ _ AOK DI_A0 _ _ _ _ _ DM0 MUL) as PAYL. a0img.
        pose proof (u8ro_read a0segs _ (b_src cx) (a_payload A) (b_len cx - Z.succ (Z.of_nat (length inp1)))%Z b8_1 _ PAYL ltac:(rewrite <- NTH1; f_equal; lia) ltac:(lia) eq_refl) as RD.
        (let pv := reg_val 16%Z in lazymatch pv with Z_to_bv 64 ?e => replace e with (b_src cx + (b_len cx - Z.succ (Z.of_nat (length inp1))))%Z by lia end).
        wstepl. clear RD PAYL.
        arun_to 0xa020c%Z.
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
        til_joinA 16%Z 0xa0224%Z HD STRM FRL FRH ST MU WM MI MUL WML.
        { arun. if_cases K3_1; [ til_useA JN | arun_to 0xa0224%Z; til_useA JN ]. }
        arun. if_false_z.
        arun_to 0x9fc3c%Z. sh_norm.
        gbA_exit HK MUL WML DP MD FU 8%Z.
      }
      { (* [comment removed for export] *)
        assert (inp = []) as -> by (lin_unbox LIN; destruct inp; [reflexivity| exfalso; cbn [length] in K2_1, LIN; rewrite Nat2Z.inj_succ in K2_1, LIN; clear -K2_1 LIN; zb_masks; mlia]). clear K2_1.
        arun_to 0x9eb34%Z.
        gbA_ret HRET MUL WML DP MD NB 8%Z.
      }
    }
    { (* [comment removed for export] *)
      arun_to 0x9fc3c%Z. sh_norm.
      gbA_exit HK MUL WML DP MD FU 8%Z.
    }
  Qed.

End R.

End ACeilS1.
