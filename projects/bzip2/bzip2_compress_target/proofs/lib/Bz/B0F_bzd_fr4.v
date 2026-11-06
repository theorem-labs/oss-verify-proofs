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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require B0F_bzd_fr1 B0F_bzd_fr2 B0F_bzd_fr3.
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
  (* [comment removed for export] *)
  Ltac sinv_close := unfold S0F_bzd_sr1.sinvR; pcut;
    repeat match goal with |- _ /\ _ => split end; first [assumption | cbn [length]; lia].
  (* [comment removed for export] *)
  Ltac exitK MU WM := eapply KE; [dsg_close | destg_close | fsl_close | ro_close | exact MU | exact WM | unfold oexit; focbn; lia].
  (* [comment removed for export] *)
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
  Let fr_G1 := B0F_bzd_fr2.fr_G1 c SHS w0 w8 w40 w48 w56 w64 w72 w88 OK OKF ALT ANS SH KJ KE RD1.
  Let fr_H0 := B0F_bzd_fr2.fr_H0 c SHS w0 w8 w40 w48 w56 w64 w72 w88 OK OKF ALT ANS SH KJ RD1.
  Let fr_L1 := B0F_bzd_fr3.fr_L1 c SHS w0 w8 w40 w48 w56 w64 w72 w88 OK OKF ALT ANS SH KE RD1.
  Let fr_L2 := B0F_bzd_fr3.fr_L2 c SHS w0 w8 w40 w48 w56 w64 w72 w88 OK OKF ALT ANS SH KE RD1.
  Let fr_L3 := B0F_bzd_fr3.fr_L3 c SHS w0 w8 w40 w48 w56 w64 w72 w88 OK OKF ALT ANS SH KE RD1.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma fr_L4 : forall f', (forall p', R5S f' p') -> forall p, R4S f' p.
  Proof.
    intros f' IHR5 p. unfold B0F_bzd_fr1.R4S. intros until rest. intros CHm SI Hf Hav Hol Hoc Rk0 Hnu Hw Htp HrN1.
    destruct p as [oc ol nu k0 tp rn rt cb out av tout tol toh]. open_cut. subst ol oc.
    cps_destruct SI as (Rcb & Roc & Rol & Rnu & _ & Rtp & Rrn & Rrt & Rav & Lout').
    unCH CHm. prep. unSH.
    unfold DSgA, DESTgA in *. b0img. focbn_in HD. focbn_in NBU. focbn_in MID. focbn_in SM. focbn_in SAV. focbn_in Edb. focbn_in Lout.
    subst tp. pose proof (div256_range w Hw) as Dw.
    unfold PG4b. s8.
    (* [comment removed for export] *)
    brun_to 0x85e10%Z. try rewrite (sx32_of_Z rn) by lia.
    (* [comment removed for export] *)
    brun_to 0x85e2c%Z. wstep.
    (* [comment removed for export] *)
    brun_to 0x85e44%Z. wstep. try nbu_fix (nu + 1)%Z.
    (* [comment removed for export] *)
    brun_to 0x85e50%Z. wstep. wstep. wstep. wstep.
    rewrite (mask_b2z rn ltac:(lia)).
    set (k1 := Z.lxor (Z.land w 255) (rmask rn)) in *.
    assert (Rk1 : (0 <= k1 < 256)%Z) by (subst k1; apply lxor_byte_bit; [pose proof (BzWalkArith.land255_range w); lia | destruct (rn - 1 =? 1)%Z; lia]).
    (* [comment removed for export] *)
    wstep. wstep.
    (* [comment removed for export] *)
    wstep. if_cases K3; zify_cond K3.
    2:{ rewrite PG5_None by (apply get_sym_None; s8; unfold blk_cap; lia).
      wstep. exitK MU WM. }
    pose proof (get_sym_FR (set8 d0 k0 (k1 + 4) (nu + 1) k0 (w / 256)%Z (rn - 1) rt cb) ltac:(s8; unfold blk_cap; lia) ltac:(s8; rewrite Esm; exact HSM) ltac:(s8; rewrite RD1; lia)) as GSk.
    rewrite gsF_set8 in GSk. cbv zeta in GSk.
    rewrite (PG5_Some _ _ _ _ _ GSk). clear GSk. s8.
    pose proof (rNn_range (rn - 1)%Z rt ltac:(lia) ltac:(lia)) as RN1. pose proof (rTn_range (rn - 1)%Z rt ltac:(lia)) as RT1.
    (* [comment removed for export] *)
    tt_load 0x85ea0%Z (w / 256)%Z. pose proof (Rtt (w / 256)%Z) as Rw2. set (w2 := zget (d_tt d0) (w / 256)) in *. pose proof (div256_range w2 Rw2) as Dw2.
    try rewrite (zx32_of_Z w2) by lia.
    pose proof (BzWalkArith.land255_range w2) as CH5.
    (* [comment removed for export] *)
    brun_to 0x85ebc%Z. wstep.
    (* [comment removed for export] *)
    brun_to 0x85ecc%Z. try rewrite (Z.shiftr_div_pow2 w2 8) by lia. try change (2^8)%Z with 256%Z. wstep.
    (* [comment removed for export] *)
    wstep. if_cases K4; zify_cond K4.
    { rewrite (rNn_nz (rn - 1)%Z rt K4), (rTn_nz (rn - 1)%Z rt K4).
      pose proof (IHR5 (PST k0 (k1 + 4) (nu + 1) (Z.land w2 255) (w2 / 256)%Z (rn - 1) rt cb out av tout tol toh)) as CR5.
      unfold B0F_bzd_fr1.R5S, B0F_bzd_fr1.CHf, S0F_bzd_snr1.D, S0F_bzd_snr1.Ss, S0F_bzd_snr1.Jp in CR5. pcut_in CR5.
      try replace (nu + 2)%Z with (nu + 1 + 1)%Z by lia.
      enter_with (CR5 _ _ _ _ _ _ _ _ _ _ _ _ _ dbytes rest);
        [ st_eq | ch_close MU WM | sinv_close
        | lia | lia | lia | lia | lia | lia | lia ]. }
    (* [comment removed for export] *)
    brun_to 0x85ee8%Z. try rewrite (sx32_of_Z rt) by lia.
    rn_load 0x85f24%Z rt. pose proof (rNums_range rt ltac:(lia)) as RNR.
    (* [comment removed for export] *)
    brun_to 0x85f34%Z. wstep.
    (* [comment removed for export] *)
    brun_to 0x85f44%Z. wstep. wstep. wstep. wstep. rewrite (rtpos_wrap rt) by lia.
    pose proof (Z.mod_pos_bound (rt + 1) 512 ltac:(lia)) as RT'.
    (* [comment removed for export] *)
    brun_to 0x85f58%Z.
    assert (Ez : (rn - 1)%Z = 0%Z) by lia. rewrite Ez. rewrite rNn_z, (rTn_z rt) by lia.
    pose proof (IHR5 (PST k0 (k1 + 4) (nu + 1) (Z.land w2 255) (w2 / 256)%Z (rNums rt) ((rt + 1) mod 512)%Z cb out av tout tol toh)) as CR5.
    unfold B0F_bzd_fr1.R5S, B0F_bzd_fr1.CHf, S0F_bzd_snr1.D, S0F_bzd_snr1.Ss, S0F_bzd_snr1.Jp in CR5. pcut_in CR5.
    try replace (nu + 2)%Z with (nu + 1 + 1)%Z by lia.
    enter_with (CR5 _ _ _ _ _ _ _ _ _ _ _ _ _ dbytes rest);
      [ st_eq | ch_close MU WM | sinv_close
      | lia | lia | lia | lia | lia | lia | lia ].
  Time Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma fr_L5 : forall f', (forall p', H0S f' p') -> forall p, R5S f' p.
  Proof.
    intros f' IHH0 p. unfold B0F_bzd_fr1.R5S. intros until rest. intros CHm SI Hf Hav Hol Rk0 Hnu Htp HrN1.
    destruct p as [oc ol nu k0 tp rn rt cb out av tout tol toh]. open_cut.
    cps_destruct SI as (Rcb & Roc & Rol & Rnu & _ & Rtp & Rrn & Rrt & Rav & Lout').
    unCH CHm. prep. unSH.
    unfold DSgA, DESTgA in *. b0img. focbn_in HD. focbn_in NBU. focbn_in MID. focbn_in SM. focbn_in SAV. focbn_in Edb. focbn_in Lout.
    (* [comment removed for export] *)
    brun_to 0x85f64%Z. try rewrite (sx32_of_Z rn) by lia.
    (* [comment removed for export] *)
    brun_to 0x85f7c%Z. wstep.
    (* [comment removed for export] *)
    brun_to 0x85f8c%Z. wstep. wstep. wstep. rewrite (mask_b2z rn ltac:(lia)).
    set (k5 := Z.lxor k0 (rmask rn)) in *.
    assert (Rk5 : (0 <= k5 < 256)%Z) by (subst k5; apply lxor_byte_bit; [lia | destruct (rn - 1 =? 1)%Z; lia]).
    (* [comment removed for export] *)
    wstep. wstep.
    (* [comment removed for export] *)
    brun_to 0x85fb4%Z. wstep. try nbu_fix (nu + 1)%Z.
    (* [comment removed for export] *)
    brun_to 0x855c4%Z.
    pose proof (IHH0 (PST oc ol (nu + 1) k5 tp (rn - 1) rt cb out av tout tol toh)) as M.
    unfold B0F_bzd_fr1.H0S, B0F_bzd_fr1.CHf, S0F_bzd_snr1.D, S0F_bzd_snr1.Ss, S0F_bzd_snr1.Jp in M. pcut_in M.
    enter_with (M _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ dbytes rest);
      [ st_eq | ch_close MU WM | sinv_close | lia ].
  Time Qed.

  (* [comment removed for export] *)
  Lemma fr_knot : forall f, (forall p, GS f p) /\ (forall p, H0S f p).
  Proof.
    induction f as [|f IH].
    - assert (G : forall p, GS 0%nat p) by (intros p; eapply fr_G1; intros f' p' E; discriminate E).
      assert (H0 : forall p, H0S 0%nat p) by (intros p; eapply fr_H0; [exact G | reflexivity]).
      exact (conj G H0).
    - cps_destruct IH as (G' & H0').
      assert (R5 : forall p, R5S f p) by (intros p; eapply fr_L5; exact H0').
      assert (R4 : forall p, R4S f p) by (intros p; eapply fr_L4; exact R5).
      assert (R3 : forall p, R3S f p) by (intros p; eapply fr_L3; [exact R4 | exact H0']).
      assert (R2 : forall p, R2S f p) by (intros p; eapply fr_L2; [exact R3 | exact H0']).
      assert (R1 : forall p, R1S f p) by (intros p; eapply fr_L1; [exact R2 | exact H0']).
      assert (G : forall p, GS (Datatypes.S f) p) by (intros p; eapply fr_G1; intros f' p' E; injection E as <-; apply R1).
      assert (H0 : forall p, H0S (Datatypes.S f) p) by (intros p; eapply fr_H0; [exact G | reflexivity]).
      exact (conj G H0).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem B0F_fastr : forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 t3 t4 t5 t6 : word) (m : word -> option byte) (dbytes rest : list byte),
    DSgA DI_B0 c m J d0 s0 -> DESTgA DI_B0 c m s0 dbytes rest ->
    rw_cells b0segs m uspi
      (bzd_slots S SHS w0 w8 w40 w48 w56 w64 w72 w88 (Z_to_bv 64 (SHS + -2147450744)) (Z_to_bv 64 (SHS + -2147442870))) ->
    RO m -> munch WB m0 m -> wmono b0segs m0 m ->
    evt b0segs (KQ (unRLE d0 s0))
      (MS (B0RR c SHS ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 hs7 hs9 t3 t4 t5 t6) F (Z_to_bv 64 0x8558c) fc None m (seg_rom b0segs)).
  Proof.
    intros until rest. intros DSm DE FSL0 ROm MU WM.
    pose proof DSm as DSm0. pose proof DE as DE0. pose proof ROm as RO0.
    unDS DSm. cps_destruct DE as (DSTA & DL & Edb & Lout). unRO ROm. prep. unSH.
    unfold id in NK0. pose proof (Rrnd RD1) as [RrN0 RrT0].
    rewrite (unRLE_plain d0 s0 (Z.to_nat (PP + 2 - d_nused d0))) by (first [rewrite RD1; destruct (smallb d0); reflexivity | lia]).
    cps_destruct (fr_knot (Z.to_nat (PP + 2 - d_nused d0))) as (_ & H0).
    remember (Z.to_nat (PP + 2 - d_nused d0)) as f eqn:Hf.
    set (p0 := PST (d_out_ch d0) (d_out_len d0) (d_nused d0) (d_k0 d0) (d_tPos d0) (d_rNToGo d0) (d_rTPos d0) (d_cbcrc d0)
                   (s_out s0) (s_avail_out s0) (s_tout s0) (j_tol J) (j_toh J)).
    assert (ED : set8 d0 (d_out_ch d0) (d_out_len d0) (d_nused d0) (d_k0 d0) (d_tPos d0) (d_rNToGo d0) (d_rTPos d0) (d_cbcrc d0) = d0) by apply set8_id.
    assert (ES : smod s0 (s_out s0) (s_avail_out s0) (s_tout s0) = s0) by apply smod_id.
    assert (EJ : jk_set_o J (j_tol J) (j_toh J) = J) by apply jk_set_o_id.
    pose proof (H0 p0) as H. unfold B0F_bzd_fr1.H0S, B0F_bzd_fr1.CHf in H. subst p0.
    unfold S0F_bzd_snr1.D, S0F_bzd_snr1.Ss, S0F_bzd_snr1.Jp in H. pcut_in H.
    rewrite ED, ES, EJ in H.
    unfold DSgA in HD, NBU, MID, SM. b0img. focbn_in HD. focbn_in NBU. focbn_in MID. focbn_in SM.
    brun_to 0x855c4%Z.
    enter_with (H _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ dbytes rest);
      [ st_eq
      | repeat match goal with |- _ /\ _ => split end; [exact DSm0 | exact DE0 | unfold B0F_bzd_fr1.FSLs; exact FSL0 | exact RO0 | exact MU | exact WM]
      | unfold S0F_bzd_sr1.sinvR; pcut;
        repeat match goal with |- _ /\ _ => split end; first [lia | reflexivity | exact Lout]
      | lia ].
  Time Qed.
End FR.
End ACeilS1.
