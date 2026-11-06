(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Wf_nat.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0 SegsB0 StoreFast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel BzTac BzDefs BzInv BzTables BzLemmasT BzLemmasMtf BzWalkArith BzWalkArith2 S0_bzd_out BzSepTac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem CmpArith BzCLemmas1.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDOut BzDOK BzDOKp BzDOKS DecCutF DecTacF.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOut OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOKp OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOKS OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacF.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import S0F_bzd_out S0F_bzd_outS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require S0F_bzd_fr1 S0F_bzd_fr2 S0F_bzd_fr3.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac2 AsanKit AsanCut AsanCutB0 AsanKitB0 DecCutB B0F_decV B0F_bzdV B0F_bzd_uV.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import S0F_bzd_outS S0F_bzd_fr1 S0F_bzd_fr2 S0F_bzd_fr3 S0F_bzd_outR S0F_bzd_snr1 S0F_bzd_sr1.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require B0F_bzd_fr1.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFastZ StoreFastC.   (* [comment removed for export] *)
Local Ltac mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | mem_after_store_fast ].
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Ltac unhide_disj := repeat match goal with H : id (?A \/ ?B) |- _ => unfold id in H end.
Ltac hide_disj := repeat match goal with H : ?A \/ ?B |- _ => change (A \/ B) with (id (A \/ B)) in H end.
Local Ltac tlia ::= first [ Zify.zify; xlia zchecker
                         | sf_unhide; unhide_disj;
                           first [ zify_prune_neg; Zify.zify; xlia zchecker
                                 | zify_prune_plain; Zify.zify; xlia zchecker
                                 | Zify.zify; xlia zchecker ] ].
Local Ltac tslia ::= tslia_sep.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import NatLit.
Local Ltac Zify.zify_pre_hook ::= NatLit.natlen_ctx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require NormFast RelLiaA SasFastF RelLiaS.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Bz.BzSepTac.tlia2 ::= first [ RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; Bz.BzSepTac.unhide_disj; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac lia ::= RelLiaA.lia_rf.
Local Ltac BzTac.bz32 ::= NormFast.bz32_m.
Local Ltac BzTac2.bz32l ::= NormFast.bz32l_m.
Local Ltac Zify.zify_pre_hook ::= NormFast.nf_pre_natlen.
Local Ltac DecCutF.unset_Z ::= NormFast.unset_Z_subst.
Local Ltac simpl_arr_sizes ::= SasFastF.sas6F_all.
Local Ltac tlia ::= RelLiaS.tlia_bzd_r.
Local Ltac BzSepTac.tlia1 ::= RelLiaS.tlia1_r.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Lib.Step.solve_load ::= AsanKit.asan_solve_load.
Local Ltac AsanKit.a_norm ::= AsanKit.sh_fold; AsanKit.sh_norm.
Section ACeilS1. Context {ACEIL__ : ACeil}.

Section FR.
  Variable c : foctx.
  Variable SHS : Z. Variable w0 w8 w40 w48 w56 w64 w72 w88 : word.
  Notation cx := (o_cx c). Notation J := (o_J c). Notation d0 := (o_d c). Notation s0 := (o_s c).
  Notation S := (b_s (o_cx c)). Notation STRM := (b_strm (o_cx c)). Notation DST := (b_dst (o_cx c)). Notation dlen := (b_dlen (o_cx c)).
  Notation n := (b_n (o_cx c)). Notation TT := (b_tt (o_cx c)).
  Notation snb := (sv_nblock (d_sv (o_d c))). Notation av0 := (s_avail_out (o_s c)). Notation PP := (sv_nblock (d_sv (o_d c)) + 1)%Z.
  Notation cap := (100000 * b_n (o_cx c))%Z.
  Notation F := (o_F c). Notation fc := (o_fc c). Notation KQ := (o_KQ c). Notation m0 := (o_m0 c).
  Notation uspi := (bv_unsigned (o_SP c)).
  Notation RO := (FROfA DI_B0 c). Notation WB := (FWBA c).
  Hypothesis OK : foctx_okA c BIHI0. Hypothesis OKF : foctx_okFA c BIHI0. Hypothesis ALT : (b_tt (o_cx c) mod 4 = 0)%Z.
  Hypothesis ANS : sanchor S SHS.
  Hypothesis SH : obz_sh DI_B0 c WB m0.
  Hypothesis KJ : B0_FKjoin c SHS w0 (FROfA DI_B0 c) (FWBA c).
  Hypothesis KE : B0_FKexit c SHS w0 (FROfA DI_B0 c) (FWBA c).
  Hypothesis RD1 : d_rand (o_d c) = 1%Z.

  Notation pst := S0F_bzd_snr1.pst. Notation PST := S0F_bzd_snr1.PST.
  Notation p_oc := S0F_bzd_snr1.p_oc. Notation p_ol := S0F_bzd_snr1.p_ol. Notation p_nu := S0F_bzd_snr1.p_nu. Notation p_k0 := S0F_bzd_snr1.p_k0.
  Notation p_tp := S0F_bzd_snr1.p_tp. Notation p_rn := S0F_bzd_snr1.p_rn. Notation p_rt := S0F_bzd_snr1.p_rt. Notation p_cb := S0F_bzd_snr1.p_cb.
  Notation p_out := S0F_bzd_snr1.p_out. Notation p_av := S0F_bzd_snr1.p_av. Notation p_tout := S0F_bzd_snr1.p_tout.
  Notation p_tol := S0F_bzd_snr1.p_tol. Notation p_toh := S0F_bzd_snr1.p_toh.
  Notation D := (S0F_bzd_snr1.D c). Notation Ss := (S0F_bzd_snr1.Ss c). Notation Jp := (S0F_bzd_snr1.Jp c).
  Notation sinvR := (S0F_bzd_sr1.sinvR c). Notation DR := (S0F_bzd_sr1.DR c).

  Notation cstrm := (Z_to_bv 64 (b_strm (o_cx c))). Notation csnb := (Z_to_bv 64 (sv_nblock (d_sv (o_d c)))).
  Notation cpp := (Z_to_bv 64 (sv_nblock (d_sv (o_d c)) + 1)). Notation cnn := (Z_to_bv 64 (b_n (o_cx c) * 100000)).
  Notation cm4 := (Z_to_bv 64 (-4)).
  Notation ctt := (Z_to_bv 64 (b_tt (o_cx c))).
  Notation cntt := (Z_to_bv 64 (18446744073709551615 - b_tt (o_cx c))).   (* [comment removed for export] *)
  Notation hs7 := (Z_to_bv 64 (SHS + -2147450878)).   (* [comment removed for export] *)
  Notation hs9 := (Z_to_bv 64 (SHS + -2147450879)).   (* [comment removed for export] *)
  Notation c16 := (Z_to_bv 64 (SHS + 2)).             (* [comment removed for export] *)
  Notation c24 := (Z_to_bv 64 (SHS + 3)).             (* [comment removed for export] *)
  Notation c60 := (Z_to_bv 64 (SHS + 7)).             (* [comment removed for export] *)
  Notation c64 := (Z_to_bv 64 (SHS + 8)).             (* [comment removed for export] *)
  Notation cnu := (Z_to_bv 64 (SHS + 136)).           (* [comment removed for export] *)

  (* [comment removed for export] *)
  Notation CHf := (B0F_bzd_fr1.CHf c SHS w0 w8 w40 w48 w56 w64 w72 w88).
  Notation H0S := (B0F_bzd_fr1.H0S c SHS w0 w8 w40 w48 w56 w64 w72 w88). Notation GS := (B0F_bzd_fr1.GS c SHS w0 w8 w40 w48 w56 w64 w72 w88).
  Notation R1S := (B0F_bzd_fr1.R1S c SHS w0 w8 w40 w48 w56 w64 w72 w88). Notation R2S := (B0F_bzd_fr1.R2S c SHS w0 w8 w40 w48 w56 w64 w72 w88).
  Notation R3S := (B0F_bzd_fr1.R3S c SHS w0 w8 w40 w48 w56 w64 w72 w88). Notation R4S := (B0F_bzd_fr1.R4S c SHS w0 w8 w40 w48 w56 w64 w72 w88).
  Notation R5S := (B0F_bzd_fr1.R5S c SHS w0 w8 w40 w48 w56 w64 w72 w88).
  Ltac pcut := cbn [S0F_bzd_snr1.p_oc S0F_bzd_snr1.p_ol S0F_bzd_snr1.p_nu S0F_bzd_snr1.p_k0 S0F_bzd_snr1.p_tp S0F_bzd_snr1.p_rn S0F_bzd_snr1.p_rt
                    S0F_bzd_snr1.p_cb S0F_bzd_snr1.p_out S0F_bzd_snr1.p_av S0F_bzd_snr1.p_tout S0F_bzd_snr1.p_tol S0F_bzd_snr1.p_toh].
  Ltac pcut_in H := cbn [S0F_bzd_snr1.p_oc S0F_bzd_snr1.p_ol S0F_bzd_snr1.p_nu S0F_bzd_snr1.p_k0 S0F_bzd_snr1.p_tp S0F_bzd_snr1.p_rn S0F_bzd_snr1.p_rt
                    S0F_bzd_snr1.p_cb S0F_bzd_snr1.p_out S0F_bzd_snr1.p_av S0F_bzd_snr1.p_tout S0F_bzd_snr1.p_tol S0F_bzd_snr1.p_toh] in H.
  Ltac pcut_all := cbn [S0F_bzd_snr1.p_oc S0F_bzd_snr1.p_ol S0F_bzd_snr1.p_nu S0F_bzd_snr1.p_k0 S0F_bzd_snr1.p_tp S0F_bzd_snr1.p_rn S0F_bzd_snr1.p_rt
                    S0F_bzd_snr1.p_cb S0F_bzd_snr1.p_out S0F_bzd_snr1.p_av S0F_bzd_snr1.p_tout S0F_bzd_snr1.p_tol S0F_bzd_snr1.p_toh] in *.
  Ltac unRO H := let GOT := ident:(GOT) in cps_destruct H as (SAV & TTA & CRC & RNA & GOT & MI); unfold FGOTA in GOT; b0img.
  Ltac unDS H := cps_destruct H as (HD & NBU & MID & SM).
  Ltac unCH H := let DSm := fresh "DSm" in let DE := fresh "DE" in let ROm := fresh "ROm" in let FSL := ident:(FSL) in
    cps_destruct H as (DSm & DE & FSL & ROm & MU & WM); unDS DSm; cps_destruct DE as (DSTA & DL & Edb & Lout); unRO ROm;
    unfold B0F_bzd_fr1.FSLs, bzd_slots in FSL.
  Ltac unSH := let SHbf := ident:(SHbf) in let SH' := fresh "SH" in pose proof SH as SH';
    cps_destruct SH' as (SHs & SHt & SHd & SHc & SHr & SHbf & _); b0img;
    let OKF' := fresh "OKF" in pose proof OKF as OKF'; specialize (SHbf (proj1 OKF')); clear OKF'.
  Ltac prep :=
    let JWF := ident:(JWF) in let ENT := ident:(ENT) in let ALS := ident:(ALS) in let ALM := ident:(ALM) in let OK' := fresh "OK" in pose proof OK as OK';
    cps_destruct OK' as (HS & HSTRM & HDST & Hdlen & HSP & (ALS & ALM) & SEP_SM & SEP_SD & SEP_MD & IAS & IAM & IAD & HIHI & JWF & ENT);
    let OKF' := fresh "OKF" in pose proof OKF as OKF';
    cps_destruct OKF' as (HSM & HTT & SEP_ST & SEP_MT & SEP_DT & IAT);
    destruct (zmod16_lin _ ALS) as [qS EqS]; destruct (zmod8_lin _ ALM) as [qSTRM EqSTRM]; destruct (zmod4_lin _ ALT) as [qTT EqTT];
    clear ALS ALM;
    cps_destruct ENT as (En & Rn & Esm & Rsnb & Rsnb1 & Rav0 & Lout0 & Eol0 & RtP0 & NK0 & Rcb0 & Roc0 & Rr01 & Rrnd & _ & Rtt & _ & _);
    cps_destruct JWF as (Lp1 & Lp2 & Lp3 & Ls1 & Ls2 & Lq1 & Lq2);
    unfold disj, bzd_img_apart in *;
    unfold FWBA, FWB in *; cbn [app] in *; pose proof alloc_ceiling_range as ACR;
    pose proof (zw32_length (d_tt d0) cap ltac:(lia)) as TTL; pose proof rnums_words_length as RNL; pose proof crc_words_length as CRCL;
    pose proof (proj2 ANS : saddr S SHS) as ANS0;
    hide_disj.
  Ltac ro_close := unfold FROfA, FGOTA; b0img; repeat match goal with |- _ /\ _ => split end; assumption.
  Ltac dsg_close := let HD := ident:(HD) in let NBU := ident:(NBU) in let MID := ident:(MID) in let SM := ident:(SM) in
    unfold DSgA; b0img; focbn; repeat match goal with |- _ /\ _ => split end; [exact_cells HD | exact_cells NBU | exact_cells MID | exact_cells SM].
  Ltac destg_close := unfold DESTgA; b0img; focbn; repeat match goal with |- _ /\ _ => split end; first [eassumption | cbn [length]; lia].
  Ltac fsl_close := let FSL := ident:(FSL) in first [ exact FSL | unfold bzd_slots; exact FSL | unfold B0F_bzd_fr1.FSLs, bzd_slots; exact FSL ].
  Ltac ch_close MU WM := repeat match goal with |- _ /\ _ => split end; [dsg_close | destg_close | fsl_close | ro_close | exact MU | exact WM].
  Ltac unhide_k0 := try match goal with H : id ((0 <= _ < 256)%Z \/ _) |- _ => unfold id in H end.
  Ltac sinv_close := unfold S0F_bzd_sr1.sinvR; pcut;
    repeat match goal with |- _ /\ _ => split end; first [assumption | cbn [length]; lia].
  Ltac sbl := wstep; lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?w)) _) => rewrite ?le1_sx32_lit, ?BzInv.le1_lit; mem_after_store end.
  Ltac exitK MU WM := eapply KE; [dsg_close | destg_close | fsl_close | ro_close | exact MU | exact WM | unfold oexit; focbn; lia].
  Ltac joinK MU WM := eapply KJ; [dsg_close | destg_close | fsl_close | ro_close | exact MU | exact WM | ];
    unfold ojoin; focbn; unhide_k0; repeat match goal with |- _ /\ _ => split end;
    first [assumption | lia | intros; lia | idtac].
  Ltac open_cut :=
    unfold B0F_bzd_fr1.CHf, S0F_bzd_sr1.DR, S0F_bzd_snr1.D, S0F_bzd_snr1.Ss, S0F_bzd_snr1.Jp, S0F_bzd_sr1.sinvR in *; pcut_all.
  (* [comment removed for export] *)
  Ltac tt_load pc i :=
    brun_to pc;
    lazymatch goal with TTA : u32arr _ ?mm TT _ |- _ =>
      let RD := fresh "RD" in
      pose proof (zw32_read b0segs mm TT (d_tt d0) cap i _ TTA ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD; wstep; clear RD end.
  (* [comment removed for export] *)
  Ltac rn_load pc i :=
    brun_to pc;
    lazymatch goal with RNA : u32arr _ ?mm 858432 rnums_words |- _ =>
      let RD := fresh "RD" in
      pose proof (u32arr_read b0segs mm 858432 rnums_words i (Z_to_bv 64 (rNums i)) _ RNA (rnums_words_nth i ltac:(lia)) ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD;
      wstep; clear RD; rewrite ?(sx32_of_Z (rNums i)) by lia end.
  (* [comment removed for export] *)
  Ltac nbu_fix v := match goal with H : rw_cells _ _ (_ + 1092)%Z [C4 (Z_to_bv 64 ?e)] |- _ => replace e with v in H by lia end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma fr_G1 : forall f, (forall f' p', f = Datatypes.S f' -> R1S f' p') -> forall p, GS f p.
  Proof.
    intros f IHR1 p. unfold B0F_bzd_fr1.GS. intros until rest. intros CHm SI Hf Hav Hol.
    destruct p as [oc ol nu k0 tp rn rt cb out av tout tol toh]. open_cut. subst ol.
    cps_destruct SI as (Rcb & Roc & Rol & Rnu & Rk0 & Rtp & Rrn & Rrt & Rav & Lout').
    unCH CHm. prep. unSH.
    unfold DSgA, DESTgA in *. b0img. focbn_in HD. focbn_in NBU. focbn_in MID. focbn_in SM. focbn_in SAV. focbn_in Edb. focbn_in Lout.
    move SAV at bottom.
    (* [comment removed for export] *)
    brun_to 0x85854%Z. try rewrite (sx32_of_Z nu) by lia.
    (* [comment removed for export] *)
    brun_to 0x85860%Z. try rewrite (sx32_of_Z snb) by lia.
    (* [comment removed for export] *)
    brun_to 0x8586c%Z.
    (* [comment removed for export] *)
    wstep. if_cases K1; zify_cond K1.
    2:{ rewrite K_PG_done by (s8; lia). wstep. joinK MU WM. }
    (* [comment removed for export] *)
    wstep. wstep. if_cases K2; zify_cond K2; rewrite ?signed_lit_small in K2 by lia.
    2:{ rewrite K_PG_over by (s8; lia). wstep. exitK MU WM. }
    rewrite K_PG_go by (s8; lia). s8.
    (* [comment removed for export] *)
    brun_to 0x8588c%Z. wstep.
    (* [comment removed for export] *)
    brun_to 0x858bc%Z.
    unfold id in Rk0. destruct Rk0 as [Rk0 | [Hnu0 Htp0]].
    - (* [comment removed for export] *)
      try rewrite (sx32_of_Z k0) by lia.
      (* [comment removed for export] *)
      brun_to 0x858c0%Z. sbl. try rewrite (unsigned_lit k0) in HD by lia.
      (* [comment removed for export] *)
      brun_to 0x858e4%Z. try rewrite (zx32_of_Z tp) by lia.
      (* [comment removed for export] *)
      brun_to 0x858ec%Z. rewrite ?En. try rewrite (sx32_of_Z n) by lia.
      (* [comment removed for export] *)
      brun_to 0x858f8%Z.
      (* [comment removed for export] *)
      pose proof (word_urange (Z_to_bv 64 tp)) as TPR.
      wstep. if_cases K3; zify_cond K3.
      2:{ assert (K3' : (cap <= bv_swrap 32 (tp + 0) mod 18446744073709551616)%Z) by lia.
        pose proof (sextw_ge tp cap ltac:(lia) ltac:(lia) K3') as GE.
        change (2^32)%Z with 4294967296%Z in GE. rewrite (Z.mod_small tp 4294967296) in GE by lia.
        rewrite PG1_None by (apply get_sym_None; s8; unfold blk_cap; lia).
        wstep. exitK MU WM. }
      assert (K3' : (bv_swrap 32 (tp + 0) mod 18446744073709551616 < cap)%Z) by lia.
      destruct (sextw_lt tp cap ltac:(lia) ltac:(lia) K3') as [LT XV].
      change (2^32)%Z with 4294967296%Z in LT, XV. rewrite (Z.mod_small tp 4294967296) in LT, XV by lia.
      pose proof (get_sym_FR (set8 d0 k0 1 nu k0 tp rn rt cb) ltac:(s8; unfold blk_cap; lia) ltac:(s8; rewrite Esm; exact HSM) ltac:(s8; rewrite RD1; lia)) as GS1.
      rewrite gsF_set8 in GS1. cbv zeta in GS1.
      rewrite (PG1_b _ _ _ _ _ _ GS1). clear GS1.
      pose proof (rNn_range rn rt ltac:(lia) ltac:(lia)) as RN1. pose proof (rTn_range rn rt ltac:(lia)) as RT1.
      (* [comment removed for export] *)
      tt_load 0x85964%Z tp. pose proof (Rtt tp) as Rw1. set (w1 := zget (d_tt d0) tp) in *. pose proof (div256_range w1 Rw1) as Dw1.
      try rewrite (zx32_of_Z w1) by lia.
      (* [comment removed for export] *)
      brun_to 0x85980%Z. try rewrite (Z.shiftr_div_pow2 w1 8) by lia. try change (2^8)%Z with 256%Z. wstep.
      (* [comment removed for export] *)
      brun_to 0x85994%Z. try rewrite (sx32_of_Z rn) by lia.
      destruct f as [|f']; [exfalso; cbn [Z.of_nat] in Hf; lia|]. rewrite Nat2Z.inj_succ in Hf.
      (* [comment removed for export] *)
      wstep. if_cases K4; zify_cond K4.
      { rewrite (rNn_nz rn rt K4), (rTn_nz rn rt K4).
        pose proof (IHR1 f' (PST k0 1 nu k0 (w1 / 256)%Z rn rt cb out av tout tol toh) eq_refl) as CR1.
        unfold B0F_bzd_fr1.R1S, B0F_bzd_fr1.CHf, S0F_bzd_sr1.DR, S0F_bzd_snr1.D, S0F_bzd_snr1.Ss, S0F_bzd_snr1.Jp in CR1. pcut_in CR1.
        enter_with (CR1 _ _ _ _ _ w1 _ dbytes rest);
          [ st_eq
          | ch_close MU WM
          | sinv_close
          | lia | lia | reflexivity | reflexivity | lia | lia | lia | reflexivity | lia ]. }
      (* [comment removed for export] *)
      brun_to 0x859b0%Z. try rewrite (sx32_of_Z rt) by lia.
      (* [comment removed for export] *)
      rn_load 0x859ec%Z rt. pose proof (rNums_range rt ltac:(lia)) as RNR.
      (* [comment removed for export] *)
      brun_to 0x859f8%Z. wstep.
      (* [comment removed for export] *)
      brun_to 0x85a08%Z. wstep. wstep. wstep. wstep. rewrite (rtpos_wrap rt) by lia.
      pose proof (Z.mod_pos_bound (rt + 1) 512 ltac:(lia)) as RT'.
      (* [comment removed for export] *)
      brun_to 0x85a24%Z.
      assert (Ez : rn = 0%Z) by lia. rewrite Ez. rewrite rNn_z, (rTn_z rt) by lia.
      pose proof (IHR1 f' (PST k0 1 nu k0 (w1 / 256)%Z (rNums rt) ((rt + 1) mod 512)%Z cb out av tout tol toh) eq_refl) as CR1.
      unfold B0F_bzd_fr1.R1S, B0F_bzd_fr1.CHf, S0F_bzd_sr1.DR, S0F_bzd_snr1.D, S0F_bzd_snr1.Ss, S0F_bzd_snr1.Jp in CR1. pcut_in CR1.
      enter_with (CR1 _ _ _ _ _ w1 _ dbytes rest);
        [ st_eq
        | ch_close MU WM
        | sinv_close
        | lia | lia | reflexivity | reflexivity | lia | lia | lia | reflexivity | lia ].
    - (* [comment removed for export] *)
      subst nu.
      brun_to 0x858c0%Z. sbl.
      brun_to 0x858e4%Z. try rewrite (zx32_of_Z tp) by lia.
      brun_to 0x858ec%Z. rewrite ?En. try rewrite (sx32_of_Z n) by lia.
      brun_to 0x858f8%Z.
      pose proof (word_urange (Z_to_bv 64 tp)) as TPR.
      wstep. if_cases K3; zify_cond K3.
      { exfalso. assert (K3' : (bv_swrap 32 (tp + 0) mod 18446744073709551616 < cap)%Z) by lia.
        destruct (sextw_lt tp cap ltac:(lia) ltac:(lia) K3') as [LT _].
        change (2^32)%Z with 4294967296%Z in LT. rewrite (Z.mod_small tp 4294967296) in LT by lia. lia. }
      rewrite PG1_None by (apply get_sym_None; s8; unfold blk_cap; lia).
      wstep. exitK MU WM.
  Time Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac dst_write av oc :=
    lazymatch goal with DSTA : u8arr _ _ DST ?bs, Edb : _ = map _ (rev ?out) ++ ?rst |- _ =>
      lazymatch goal with DL : Z.of_nat (length bs) = _ |- _ =>
      let r0 := fresh "r0" in let rest' := fresh "rest" in let LR := fresh "LR" in
      pose proof (f_equal (@length byte) Edb) as LR; rewrite length_app, length_map, length_rev in LR;
      destruct rst as [|r0 rest']; [exfalso; cbn [length] in LR; lia|]; cbn [length] in LR;
      let E' := fresh "Edb" in
      pose proof (dest_snoc out (r0 :: rest') oc r0 rest' eq_refl) as E';
      replace (length out) with (Z.to_nat (dlen - av)) in E' by lia; rewrite <- Edb in E'; clear Edb LR;
      let SOK := fresh "SOK" in
      pose proof (u8arr_store_ok b0segs _ DST _ (dlen - av) _ DSTA ltac:(lia) eq_refl) as SOK;
      wstep; rewrite BzInv.le1_lit;
      let D := fresh "DSTB" in
      pose proof (u8arr_write b0segs _ DST _ (dlen - av) (Z_to_bv 8 oc) DSTA ltac:(lia)) as D;
      clear DSTA; store_done; try clear SOK; rename D into DSTA;
      let D2 := fresh "DLB" in
      pose proof DL as D2; rewrite <- (upd_length bs (Z.to_nat (dlen - av)) (Z_to_bv 8 oc)) in D2; clear DL; rename D2 into DL;
      let db := fresh "dbytes" in
      remember (upd bs (Z.to_nat (dlen - av)) (Z_to_bv 8 oc)) as db eqn:Xdb; clear Xdb; rename E' into Edb
      end end.
  Ltac crc_load pclw crc ch :=
    let Hidx := fresh "Hidx" in
    pose proof (crc_idx_byte crc ch ltac:(lia) ltac:(lia)) as Hidx;
    brun_to pclw;
    lazymatch goal with CRC : u32arr _ ?mm 857056 crc_words |- _ =>
      let RD := fresh "RD" in
      pose proof (u32arr_read b0segs mm 857056 crc_words (Z.lxor (crc / 16777216) ch) _ _ CRC (crc_words_nth _ Hidx) ltac:(lia) eq_refl) as RD;
      wstep; clear RD end; clear Hidx.
  Ltac cs_split cs w :=
    lazymatch cs with
    | C4 w :: ?post => constr:((@nil cell, post))
    | ?c1 :: ?cs' => let r := cs_split cs' w in lazymatch r with (?pre, ?post) => constr:((c1 :: pre, post)) end
    end.
  Ltac recell H w v :=
    lazymatch type of H with rw_cells ?sg ?mm ?A ?cs =>
      let r := cs_split cs w in
      lazymatch r with (?pre, ?post) =>
        apply (C4_recell sg mm A pre w v post) in H; [ cbn [app] in H | ]
      end
    end.

  Lemma fr_H0 : forall f, (forall p, GS f p) -> forall k p, Z.to_nat (p_ol p) = k -> H0S f p.
  Proof.
    intros f G k. induction k as [k IH] using lt_wf_ind. intros p Hk.
    unfold B0F_bzd_fr1.H0S. intros until rest. intros CHm SI Hf.
    pose proof CHm as CH0. pose proof SI as SI0.
    destruct p as [oc ol nu k0 tp rn rt cb out av tout tol toh].
    unfold B0F_bzd_fr1.CHf, S0F_bzd_snr1.D, S0F_bzd_snr1.Ss, S0F_bzd_snr1.Jp, S0F_bzd_sr1.sinvR in CHm, SI, Hf, Hk |- *.
    pcut_all.
    cps_destruct SI as (Rcb & Roc & Rol & Rnu & Rk0 & Rtp & Rrn & Rrt & Rav & Lout').
    unCH CHm. prep. unSH.
    unfold DSgA, DESTgA in *. b0img. focbn_in HD. focbn_in NBU. focbn_in MID. focbn_in SM. focbn_in SAV. focbn_in Edb. focbn_in Lout.
    (* [comment removed for export] *)
    wstep. try rewrite (sx32_of_Z av) by lia.
    (* [comment removed for export] *)
    wstep. if_cases K1; zify_cond K1.
    2:{ rewrite K_PM_ret by (s8; lia). wstep. joinK MU WM. }
    rewrite K_PM_go by (s8; lia).
    (* [comment removed for export] *)
    assert (Hav1 : (1 <= av)%Z) by lia. clear K1.
    (* [comment removed for export] *)
    brun_to 0x855e0%Z. try rewrite (sx32_of_Z ol) by lia.
    wstep. if_cases K2; zify_cond K2.
    { rewrite K_PH_0 by (s8; lia).
      (* [comment removed for export] *)
      pose proof (G (PST oc ol nu k0 tp rn rt cb out av tout tol toh)) as G0. unfold B0F_bzd_fr1.GS in G0. pcut_in G0.
      eapply G0; [exact CH0 | exact SI0 | lia | lia | lia]. }
    assert (Hol1 : (1 <= ol)%Z) by lia. clear K2.
    rewrite K_PH_step by (s8; lia). cbv zeta. s8. rewrite K_PM_fold.
    pose proof (u8arr_bound _ _ _ _ DSTA) as DB.
    (* [comment removed for export] *)
    brun_to 0x8561c%Z. ack_rd (DST + (dlen - av))%Z 1%Z.
    (* [comment removed for export] *)
    wstep. rewrite zxb_lit8 by lia.
    ack_merge.
    (* [comment removed for export] *)
    dst_write av oc.
    (* [comment removed for export] *)
    brun_to 0x85638%Z. try rewrite (zx32_of_Z cb) by lia.
    (* [comment removed for export] *)
    wstep. rewrite zxb_lit8 by lia.
    (* [comment removed for export] *)
    pose proof (crc_idx_byte cb oc ltac:(lia) ltac:(lia)) as CIR.
    crc_load 0x85674%Z cb oc. clear CIR.
    (* [comment removed for export] *)
    brun_to 0x85684%Z.
    pose proof (crc_step_rel (Z_to_bv 64 cb) cb oc ltac:(rewrite unsigned_lit by lia; apply Z.mod_small; lia) ltac:(lia) ltac:(lia)) as Hcrc'.
    rewrite (unsigned_lit cb) in Hcrc' by lia. try rewrite (Z.mod_small (cb * 256) 18446744073709551616) in Hcrc' by lia.
    pose proof (crc_update_range cb oc ltac:(lia)) as CR'.
    (* [comment removed for export] *)
    wstep.
    let crcw := reg_val 10%Z in recell MID crcw (crc_update cb oc); [| rewrite Hcrc'; symmetry; apply Z.mod_small; lia].
    (* [comment removed for export] *)
    brun_to 0x85694%Z. try rewrite (sx32_of_Z ol) by lia.
    (* [comment removed for export] *)
    brun_to 0x856a8%Z. wstep.
    (* [comment removed for export] *)
    brun_to 0x8570c%Z.
    replace (DST + (dlen - av) + 1)%Z with (DST + (dlen - (av - 1)))%Z in SM by lia.
    (* [comment removed for export] *)
    brun_to 0x85724%Z. try rewrite (sx32_of_Z av) by lia.
    (* [comment removed for export] *)
    brun_to 0x8574c%Z.
    (* [comment removed for export] *)
    Ltac back IH MU WM oc ol nu k0 tp rn rt cb out av tout dbytes rest :=
      enter_with (IH (Z.to_nat (ol - 1)) ltac:(lia) (PST oc (ol - 1) nu k0 tp rn rt (crc_update cb oc) (oc :: out) (av - 1) (tout + 1) _ _) ltac:(reflexivity)
                    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ dbytes rest);
      [ pcut; unfold S0F_bzd_snr1.D, S0F_bzd_snr1.Ss; st_eq
      | unfold B0F_bzd_fr1.CHf; unfold S0F_bzd_snr1.D, S0F_bzd_snr1.Ss, S0F_bzd_snr1.Jp; pcut; ch_close MU WM
      | sinv_close
      | pcut; lia ].
    wstep. if_cases KT; zify_cond KT.
    - brun_to 0x855c4%Z.
      lazymatch goal with DSTA : u8arr _ _ DST ?db, Edb : ?db = _ ++ ?r |- _ => back IH MU WM oc ol nu k0 tp rn rt cb out av tout db r end.
    - brun_to 0x855c4%Z.
      lazymatch goal with DSTA : u8arr _ _ DST ?db, Edb : ?db = _ ++ ?r |- _ => back IH MU WM oc ol nu k0 tp rn rt cb out av tout db r end.
  Time Qed.
End FR.
End ACeilS1.
