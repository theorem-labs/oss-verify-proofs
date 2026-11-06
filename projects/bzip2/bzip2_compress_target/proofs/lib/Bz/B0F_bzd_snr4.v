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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require S0F_bzd_snr1.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac2 AsanKit AsanCut AsanCutB0 AsanKitB0 DecCutB B0F_decV B0F_bzdV B0F_bzd_uV B0F_leafCut.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require B0F_bzd_snr1 B0F_bzd_iifV.
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

Section SNR.
  Variable c : foctx.
  Variable SHS : Z. Variable w0 : word. Variable slo : Z.
  Notation cx := (o_cx c). Notation J := (o_J c). Notation d0 := (o_d c). Notation s0 := (o_s c).
  Notation S := (b_s (o_cx c)). Notation STRM := (b_strm (o_cx c)). Notation DST := (b_dst (o_cx c)). Notation dlen := (b_dlen (o_cx c)).
  Notation n := (b_n (o_cx c)). Notation L16 := (b_ll16 (o_cx c)). Notation L4 := (b_ll4 (o_cx c)).
  Notation snb := (sv_nblock (d_sv (o_d c))). Notation av0 := (s_avail_out (o_s c)). Notation PP := (sv_nblock (d_sv (o_d c)) + 1)%Z.
  Notation cap := (100000 * b_n (o_cx c))%Z.
  Notation cf := (d_cftab (o_d c)).
  Notation F := (o_F c). Notation fc := (o_fc c). Notation KQ := (o_KQ c). Notation m0 := (o_m0 c).
  Notation uspi := (bv_unsigned (o_SP c)).
  Notation RO := (FROsB c slo). Notation WB := (FWBAc c).
  Hypothesis OK : foctx_okA c BIHI0. Hypothesis OKS : foctx_okSA c BIHI0.
  Hypothesis OKB : (BIHI0 <= slo /\ alloc_ceiling <= slo /\ slo + 16 <= bv_unsigned (o_SP c) /\ BIHI0 <= b_s (o_cx c) /\ b_ll16 (o_cx c) mod 2 = 0)%Z.
  Hypothesis ANS : sanchor S SHS.
  Hypothesis SH : obz_sh DI_B0 c WB m0.
  Hypothesis KJ : B0_FKjoin c SHS w0 (FROsB c slo) (FWBAc c).
  Hypothesis KE : B0_FKexit c SHS w0 (FROsB c slo) (FWBAc c).

  (* [comment removed for export] *)
  Notation pst := S0F_bzd_snr1.pst. Notation PST := S0F_bzd_snr1.PST.
  Notation p_oc := S0F_bzd_snr1.p_oc. Notation p_ol := S0F_bzd_snr1.p_ol. Notation p_nu := S0F_bzd_snr1.p_nu. Notation p_k0 := S0F_bzd_snr1.p_k0.
  Notation p_tp := S0F_bzd_snr1.p_tp. Notation p_rn := S0F_bzd_snr1.p_rn. Notation p_rt := S0F_bzd_snr1.p_rt. Notation p_cb := S0F_bzd_snr1.p_cb.
  Notation p_out := S0F_bzd_snr1.p_out. Notation p_av := S0F_bzd_snr1.p_av. Notation p_tout := S0F_bzd_snr1.p_tout.
  Notation p_tol := S0F_bzd_snr1.p_tol. Notation p_toh := S0F_bzd_snr1.p_toh.
  Notation D := (S0F_bzd_snr1.D c). Notation Ss := (S0F_bzd_snr1.Ss c). Notation Jp := (S0F_bzd_snr1.Jp c).
  Notation sinv := (S0F_bzd_snr1.sinv c).

  Notation cstrm := (Z_to_bv 64 (b_strm (o_cx c))). Notation csnb := (Z_to_bv 64 (sv_nblock (d_sv (o_d c)))).
  Notation cpp := (Z_to_bv 64 (sv_nblock (d_sv (o_d c)) + 1)). Notation cnn := (Z_to_bv 64 (b_n (o_cx c) * 100000)).
  Notation cm4 := (Z_to_bv 64 (-4)).
  Notation cl16 := (Z_to_bv 64 (b_ll16 (o_cx c))). Notation cl4 := (Z_to_bv 64 (b_ll4 (o_cx c))).
  (* [comment removed for export] *)
  Notation hs7 := (Z_to_bv 64 (SHS + -2147450878)).   (* [comment removed for export] *)
  Notation hs9 := (Z_to_bv 64 (SHS + -2147450879)).   (* [comment removed for export] *)
  Notation c16 := (Z_to_bv 64 (SHS + 2)).             (* [comment removed for export] *)
  Notation c40 := (Z_to_bv 64 (SHS + 5)).             (* [comment removed for export] *)
  Notation c60 := (Z_to_bv 64 (SHS + 7)).             (* [comment removed for export] *)
  Notation c64 := (Z_to_bv 64 (SHS + 8)).             (* [comment removed for export] *)
  Notation cnu := (Z_to_bv 64 (SHS + 136)).           (* [comment removed for export] *)
  Notation c3160 := (Z_to_bv 64 (SHS + 395)).         (* [comment removed for export] *)
  Notation c3168 := (Z_to_bv 64 (SHS + 396)).         (* [comment removed for export] *)
  Notation csnbsh := (Z_to_bv 64 (SHS + 8010)).       (* [comment removed for export] *)

  (* [comment removed for export] *)
  Hypothesis RD0 : d_rand (o_d c) = 0%Z.
  Notation CH := (B0F_bzd_snr1.CH c SHS w0 slo).
  Notation H0S := (B0F_bzd_snr1.H0S c SHS w0 slo). Notation GS := (B0F_bzd_snr1.GS c SHS w0 slo). Notation MS_ := (B0F_bzd_snr1.MS_ c SHS w0 slo).
  Notation T1S := (B0F_bzd_snr1.T1S c SHS w0 slo). Notation T2S := (B0F_bzd_snr1.T2S c SHS w0 slo). Notation T3S := (B0F_bzd_snr1.T3S c SHS w0 slo).
  Notation T4S := (B0F_bzd_snr1.T4S c SHS w0 slo). Notation T5S := (B0F_bzd_snr1.T5S c SHS w0 slo).
  Ltac pcut := cbn [S0F_bzd_snr1.p_oc S0F_bzd_snr1.p_ol S0F_bzd_snr1.p_nu S0F_bzd_snr1.p_k0 S0F_bzd_snr1.p_tp S0F_bzd_snr1.p_rn S0F_bzd_snr1.p_rt
                    S0F_bzd_snr1.p_cb S0F_bzd_snr1.p_out S0F_bzd_snr1.p_av S0F_bzd_snr1.p_tout S0F_bzd_snr1.p_tol S0F_bzd_snr1.p_toh].
  Ltac pcut_in H := cbn [S0F_bzd_snr1.p_oc S0F_bzd_snr1.p_ol S0F_bzd_snr1.p_nu S0F_bzd_snr1.p_k0 S0F_bzd_snr1.p_tp S0F_bzd_snr1.p_rn S0F_bzd_snr1.p_rt
                    S0F_bzd_snr1.p_cb S0F_bzd_snr1.p_out S0F_bzd_snr1.p_av S0F_bzd_snr1.p_tout S0F_bzd_snr1.p_tol S0F_bzd_snr1.p_toh] in H.
  Ltac pcut_all := cbn [S0F_bzd_snr1.p_oc S0F_bzd_snr1.p_ol S0F_bzd_snr1.p_nu S0F_bzd_snr1.p_k0 S0F_bzd_snr1.p_tp S0F_bzd_snr1.p_rn S0F_bzd_snr1.p_rt
                    S0F_bzd_snr1.p_cb S0F_bzd_snr1.p_out S0F_bzd_snr1.p_av S0F_bzd_snr1.p_tout S0F_bzd_snr1.p_tol S0F_bzd_snr1.p_toh] in *.
  (* [comment removed for export] *)
  Ltac unRO H := let GOT := ident:(GOT) in let ACG := ident:(ACG) in let ACV := ident:(ACV) in
    cps_destruct H as ((SAV & L16A & L4A & CFA & CRC & RNA & GOT & MI) & (ACG & ACV) & STK); unfold FGOTA in GOT; b0img;
    cbn [aci_segs aci_got_sh aci_shvar aci_c CmpCut.ci_segs B0C] in ACG, ACV.
  Ltac unDS H := cps_destruct H as (HD & NBU & MID & SM).
  Ltac unCH H := let DSm := fresh "DSm" in let DE := fresh "DE" in let ROm := fresh "ROm" in let FSL := ident:(FSL) in
    cps_destruct H as (DSm & DE & FSL & ROm & MU & WM); unDS DSm; cps_destruct DE as (DSTA & DL & Edb & Lout); unRO ROm;
    unfold B0F_bzd_snr1.FSLs, bzd_slots in FSL.
  Ltac unSH := let SHbs := ident:(SHbs) in let SH' := fresh "SH" in pose proof SH as SH';
    cps_destruct SH' as (SHs & SHt & SHd & SHc & SHr & _ & SHbs); b0img;
    let OKS' := fresh "OKS" in pose proof OKS as OKS'; specialize (SHbs (proj1 OKS')); clear OKS';
    cps_destruct SHbs as (SH16 & SH4).
  Ltac prep :=
    let JWF := ident:(JWF) in let ENT := ident:(ENT) in let ALS := ident:(ALS) in let ALM := ident:(ALM) in let AL16 := ident:(AL16) in
    let OK' := fresh "OK" in pose proof OK as OK';
    cps_destruct OK' as (HS & HSTRM & HDST & Hdlen & HSP & (ALS & ALM) & SEP_SM & SEP_SD & SEP_MD & IAS & IAM & IAD & HIHI & JWF & ENT);
    let OKS' := fresh "OKS" in pose proof OKS as OKS';
    cps_destruct OKS' as (HSM & HL16 & HL4 & SEP_S16 & SEP_M16 & SEP_D16 & SEP_S4 & SEP_M4 & SEP_D4 & SEP_164 & IA16 & IA4);
    let OKB' := fresh "OKB" in pose proof OKB as OKB';
    cps_destruct OKB' as (LOI & LOC & LOSP & LSI & AL16);
    destruct (zmod16_lin _ ALS) as [qS EqS]; destruct (zmod8_lin _ ALM) as [qSTRM EqSTRM]; destruct (zmod2_lin _ AL16) as [q16 Eq16];
    clear ALS ALM AL16;
    cps_destruct ENT as (En & Rn & Esm & Rsnb & Rsnb1 & Rav0 & Lout0 & Eol0 & RtP0 & NK0 & Rcb0 & Roc0 & Rr01 & Rrnd & Rcf & Rtt & Rl16 & Rl4);
    cps_destruct JWF as (Lp1 & Lp2 & Lp3 & Ls1 & Ls2 & Lq1 & Lq2);
    unfold disj, bzd_img_apart in *;
    unfold FWBAc, FWB in *; cbn [app] in *; pose proof alloc_ceiling_range as ACR;
    pose proof (zw32_length cf 257 ltac:(lia)) as CFL;
    pose proof (zh16_length (d_ll16 d0) (200000 * n) ltac:(lia)) as L16L; pose proof (zb8_length (d_ll4 d0) (50000 * n) ltac:(lia)) as L4L;
    pose proof rnums_words_length as RNL; pose proof crc_words_length as CRCL;
    pose proof (proj2 ANS : saddr S SHS) as ANS0;
    hide_disj.
  Ltac ro_close := unfold FROsB, FROsA, FGOTA, aconsts; b0img; cbn [aci_segs aci_got_sh aci_shvar aci_c CmpCut.ci_segs B0C];
    repeat match goal with |- _ /\ _ => split end; assumption.
  (* [comment removed for export] *)
  Ltac dsg_close := let HD := ident:(HD) in let NBU := ident:(NBU) in let MID := ident:(MID) in let SM := ident:(SM) in
    unfold DSgA; b0img; focbn; repeat match goal with |- _ /\ _ => split end; [exact_cells HD | exact_cells NBU | exact_cells MID | exact_cells SM].
  Ltac destg_close := unfold DESTgA; b0img; focbn; repeat match goal with |- _ /\ _ => split end; first [eassumption | cbn [length]; lia].
  Ltac fsl_close := let FSL := ident:(FSL) in first [ exact FSL | unfold bzd_slots; exact FSL | unfold B0F_bzd_snr1.FSLs, bzd_slots; exact FSL ].
  Ltac ch_close MU WM := repeat match goal with |- _ /\ _ => split end; [dsg_close | destg_close | fsl_close | ro_close | exact MU | exact WM].
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac sinv_close := unfold S0F_bzd_snr1.sinv; pcut;
    repeat match goal with |- _ /\ _ => split end; first [assumption | cbn [length]; lia].
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac exitK MU WM := eapply KE; [dsg_close | destg_close | fsl_close | ro_close | exact MU | exact WM | unfold oexit; focbn; lia].
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac l4_load i :=
    lazymatch goal with L4A : u8arr _ ?mm L4 _, R4 : forall i0 : Z, (0 <= zget (d_ll4 _) i0 < 256)%Z |- _ =>
      let RD := fresh "RD" in let R := fresh "Rv4" in
      pose proof (R4 i) as R;
      pose proof (zb8_read1 b0segs mm L4 (d_ll4 d0) (50000 * n) i _ L4A ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD;
      wstep; clear RD; rewrite zxb_lit8 by lia end.
  Ltac l16_load i :=
    lazymatch goal with L16A : u8arr _ ?mm L16 _, R16 : forall i0 : Z, (0 <= zget (d_ll16 _) i0 < 65536)%Z |- _ =>
      let RD := fresh "RD" in let R := fresh "Rv16" in
      pose proof (R16 i) as R;
      pose proof (zh16_read2 b0segs mm L16 (d_ll16 d0) (200000 * n) i _ L16A ltac:(lia) ltac:(lia) R ltac:(unfold wa; f_equal; lia)) as RD;
      wstep; clear RD; try rewrite (zx16_of_Z (zget (d_ll16 d0) i)) by lia end.
  (* [comment removed for export] *)
  Ltac name_sh tp sh :=
    let E := fresh "E" sh in let C := fresh "C" sh in
    remember (Z.land (tp * 4) 4) as sh eqn:E;
    pose proof (ll4_shift_cases tp) as C; rewrite <- E in C;
    let R := fresh "R" sh in assert (R : (0 <= sh <= 4)%Z) by lia; hide_disj.
  (* [comment removed for export] *)
  Ltac nbu_fix v := match goal with H : rw_cells _ _ (_ + 1092)%Z [C4 (Z_to_bv 64 ?e)] |- _ => replace e with v in H by lia end.
  (* [comment removed for export] *)
  Ltac srlw_norm v4 sh :=
    rewrite (Z.mod_small sh 32) by lia; rewrite (swrap32_id (Z.shiftr v4 sh)) by lia;
    try rewrite (Z.mod_small (Z.shiftr v4 sh) 18446744073709551616) by lia.
  (* [comment removed for export] *)
  Ltac fold_ll v16 v4 tp sh Esh :=
    rewrite (shl60_shr44 (Z.shiftr v4 sh)) by (apply Z.shiftr_nonneg; lia);
    rewrite (lor_hi16 v16 (Z.shiftr v4 sh mod 16)) by (first [lia | apply Z.mod_pos_bound; lia]);
    replace (Z.shiftr v4 sh mod 16 * 65536 + v16)%Z with (llval v16 v4 tp) by (unfold llval; rewrite <- Esh; lia).
  (* [comment removed for export] *)
  Ltac goM IHM pv dbytes rest MU WM :=
    let M := fresh "M" in
    pose proof (IHM pv) as M; unfold B0F_bzd_snr1.MS_, B0F_bzd_snr1.CH in M; unfold S0F_bzd_snr1.D, S0F_bzd_snr1.Ss, S0F_bzd_snr1.Jp in M;
    pcut_in M;
    enter_with (M _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ dbytes rest);
      [ st_eq | ch_close MU WM | sinv_close | lia | lia ].
  (* [comment removed for export] *)
  Ltac call_iif tpk :=
    let CFA := ident:(CFA) in let MI := ident:(MI) in let STK := ident:(STK) in let MU := ident:(MU) in let SHs := ident:(SHs) in
    let ACG := ident:(ACG) in let ACV := ident:(ACV) in let EqS := ident:(EqS) in
    call (B0F_bzd_iifV.B0_iif_U _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (S + 1096)%Z slo (zw32 cf 257));
    [ reflexivity | exact CFA | exact (zw32_length_nat cf 257) | exact MI | exact STK
      | lia
      | right; lia
      | rewrite EqS; clear; Z.div_mod_to_equations; lia
      | unfold aconsts; cbn [aci_segs aci_got_sh aci_shvar aci_c CmpCut.ci_segs B0C]; split; assumption
      | lia
      | lia
      | eapply (shzW_sub b0segs _ _ m0 _ _ _ _ _ SHs MU); [ unfold sub_fp; cbn [outside]; intros; lia | lia | lia ]
      | ];
    match goal with H : mem_inv _ _ |- _ => rename H into MI end;
    match goal with H : stk _ _ _ _ |- _ => rename H into STK end;
    rewrite (signed_lit_small tpk) by lia;
    lazymatch goal with Rcf : _ -> forall i0 : Z, _, Esm : d_small _ = _, HSM : b_small _ = 1%Z |- _ =>
      rewrite (index_into_f_zw32 cf tpk) by (intros i Hi; pose proof (Rcf ltac:(rewrite Esm, HSM; lia) i Hi); lia) end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma snr_T3 : forall f', (forall p', T4S f' p') -> (forall p', MS_ f' p') -> forall p, T3S f' p.
  Proof.
    intros f' IHT4 IHM p. unfold B0F_bzd_snr1.T3S, B0F_bzd_snr1.TcS. intros HnuP. intros until rest. intros CHm SI Hf Hav Hol Hoc Rk0 Hnu Htp.
    destruct p as [oc ol nu k0 tp rn rt cb out av tout tol toh].
    unfold B0F_bzd_snr1.CH, S0F_bzd_snr1.D, S0F_bzd_snr1.Ss, S0F_bzd_snr1.Jp, S0F_bzd_snr1.sinv in *.
    pcut_all. assert (ol = 3%Z) by lia. subst ol oc.
    cps_destruct SI as (Rcb & Roc & Rol & Rnu & _ & Rtp & Ern & Ert & Rav & Lout').
    unCH CHm. prep. unSH.
    unfold DSgA, DESTgA in *. b0img. focbn_in HD. focbn_in NBU. focbn_in MID. focbn_in SM. focbn_in SAV. focbn_in Edb. focbn_in Lout.
    (* [comment removed for export] *)
    pose proof (get_sym_SN (set8 d0 k0 3 nu k0 tp rn rt cb) ltac:(s8; unfold blk_cap; lia) ltac:(s8; rewrite Esm, HSM; lia) ltac:(s8; exact RD0)) as GS1.
    rewrite gsSN_set8 in GS1.
    rewrite (PG3_Some _ _ _ _ _ _ GS1). cbv zeta. s8.
    pose proof (Rl16 tp) as R16. pose proof (Rl4 (tp / 2)%Z) as R4.
    rewrite (get_ll_llval d0 tp) by lia.
    pose proof (indexIntoF_range tp cf) as KR. set (k1 := indexIntoF tp cf) in *.
    (* [comment removed for export] *)
    brun_to 0x86b34%Z. try rewrite (zx32_of_Z tp) by lia.
    (* [comment removed for export] *)
    brun_to 0x86bcc%Z. l16_load tp. set (v16 := zget (d_ll16 d0) tp) in *.
    (* [comment removed for export] *)
    brun_to 0x86bdc%Z. l4_load (tp / 2)%Z. set (v4 := zget (d_ll4 d0) (tp / 2)) in *.
    (* [comment removed for export] *)
    brun_to 0x86bf0%Z. name_sh tp sh. pose proof (shiftr_byte v4 sh ltac:(lia) ltac:(lia)) as SR4.
    (* [comment removed for export] *)
    wstep. srlw_norm v4 sh. wstep. wstep. wstep. fold_ll v16 v4 tp sh Esh.
    pose proof (llval_range v16 v4 tp ltac:(lia) ltac:(lia) ltac:(lia)) as TPR1. set (tp1 := llval v16 v4 tp) in *.
    (* [comment removed for export] *)
    wstep.
    (* [comment removed for export] *)
    brun_to 0x86c14%Z. try rewrite (sx32_of_Z nu) by lia.
    (* [comment removed for export] *)
    brun_to 0x86c2c%Z. wstep. try nbu_fix (nu + 1)%Z.
    (* [comment removed for export] *)
    move SAV at bottom.
    brun_to 0x86c44%Z. try rewrite (sx32_of_Z snb) by lia.
    (* [comment removed for export] *)
    brun_to 0x86c50%Z.
    (* [comment removed for export] *)
    wstep. if_cases K1; zify_cond K1.
    { rewrite (proj2 (Z.eqb_eq (nu + 1) PP)) by lia.
      goM IHM (PST k0 3 (nu + 1) k0 tp1 rn rt cb out av tout tol toh) dbytes rest MU WM. }
    rewrite (proj2 (Z.eqb_neq (nu + 1) PP)) by lia.
    (* [comment removed for export] *)
    brun_to 0x86c68%Z. try rewrite (sx32_of_Z k0) by lia.
    (* [comment removed for export] *)
    wstep. rewrite (land255_small k1) by lia.
    wstep. if_cases K2; zify_cond K2.
    { rewrite (proj2 (Z.eqb_neq k1 k0)) by lia. cbn [negb].
      (* [comment removed for export] *)
      brun_to 0x86f58%Z. wstep. wstep.
      goM IHM (PST k0 3 (nu + 1) k1 tp1 rn rt cb out av tout tol toh) dbytes rest MU WM. }
    rewrite (proj2 (Z.eqb_eq k1 k0)) by lia. cbn [negb].
    (* [comment removed for export] *)
    brun_to 0x86c84%Z. rewrite ?En. try rewrite (sx32_of_Z n) by lia.
    (* [comment removed for export] *)
    wstep. wstep.
    (* [comment removed for export] *)
    wstep. if_cases K3; zify_cond K3.
    2:{ rewrite PG4_None by (apply get_sym_None; s8; unfold blk_cap; lia).
      wstep. wstep. wstep. exitK MU WM. }
    (* [comment removed for export] *)
    wstep. wstep. wstep.
    call_iif tp1.
    pose proof (IHT4 (PST k0 3 (nu + 1) k0 tp1 rn rt cb out av tout tol toh)) as T4. unfold B0F_bzd_snr1.T4S, B0F_bzd_snr1.TcS, B0F_bzd_snr1.CH in T4; unfold S0F_bzd_snr1.D, S0F_bzd_snr1.Ss, S0F_bzd_snr1.Jp in T4.
    pcut_in T4. specialize (T4 ltac:(lia)).
    enter_with (T4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ dbytes rest);
      [ st_eq
      | ch_close MU WM
      | sinv_close
      | lia | lia | lia | reflexivity | lia | lia | lia ].
  Time Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma snr_T4 : forall f', (forall p', T5S f' p') -> forall p, T4S f' p.
  Proof.
    intros f' IHT5 p. unfold B0F_bzd_snr1.T4S, B0F_bzd_snr1.TcS. intros HnuP. intros until rest. intros CHm SI Hf Hav Hol Hoc Rk0 Hnu Htp.
    destruct p as [oc ol nu k0 tp rn rt cb out av tout tol toh].
    unfold B0F_bzd_snr1.CH, S0F_bzd_snr1.D, S0F_bzd_snr1.Ss, S0F_bzd_snr1.Jp, S0F_bzd_snr1.sinv in *.
    pcut_all. assert (ol = 3%Z) by lia. subst ol oc.
    cps_destruct SI as (Rcb & Roc & Rol & Rnu & _ & Rtp & Ern & Ert & Rav & Lout').
    unCH CHm. prep. unSH.
    unfold DSgA, DESTgA in *. b0img. focbn_in HD. focbn_in NBU. focbn_in MID. focbn_in SM. focbn_in SAV. focbn_in Edb. focbn_in Lout.
    (* [comment removed for export] *)
    pose proof (get_sym_SN (set8 d0 k0 3 nu k0 tp rn rt cb) ltac:(s8; unfold blk_cap; lia) ltac:(s8; rewrite Esm, HSM; lia) ltac:(s8; exact RD0)) as GS1.
    rewrite gsSN_set8 in GS1.
    rewrite (PG4_Some _ _ _ _ _ GS1). s8.
    pose proof (Rl16 tp) as R16. pose proof (Rl4 (tp / 2)%Z) as R4.
    rewrite (get_ll_llval d0 tp) by lia.
    pose proof (indexIntoF_range tp cf) as KR. set (k1 := indexIntoF tp cf) in *.
    (* [comment removed for export] *)
    brun_to 0x86cd0%Z. try rewrite (zx32_of_Z tp) by lia.
    brun_to 0x86d5c%Z. l16_load tp. set (v16 := zget (d_ll16 d0) tp) in *.
    (* [comment removed for export] *)
    brun_to 0x86d6c%Z. l4_load (tp / 2)%Z. set (v4 := zget (d_ll4 d0) (tp / 2)) in *.
    (* [comment removed for export] *)
    brun_to 0x86d80%Z. name_sh tp sh. pose proof (shiftr_byte v4 sh ltac:(lia) ltac:(lia)) as SR4.
    (* [comment removed for export] *)
    wstep. srlw_norm v4 sh. wstep. wstep. wstep. fold_ll v16 v4 tp sh Esh.
    pose proof (llval_range v16 v4 tp ltac:(lia) ltac:(lia) ltac:(lia)) as TPR1. set (tp1 := llval v16 v4 tp) in *.
    (* [comment removed for export] *)
    wstep.
    (* [comment removed for export] *)
    brun_to 0x86da4%Z. try rewrite (sx32_of_Z nu) by lia.
    (* [comment removed for export] *)
    brun_to 0x86db8%Z. wstep. try nbu_fix (nu + 1)%Z.
    (* [comment removed for export] *)
    brun_to 0x86dc8%Z. rewrite (land255_small k1) by lia. wstep. wstep.
    (* [comment removed for export] *)
    brun_to 0x86de4%Z. rewrite ?En. try rewrite (sx32_of_Z n) by lia.
    (* [comment removed for export] *)
    wstep. wstep.
    (* [comment removed for export] *)
    wstep. if_cases K3; zify_cond K3.
    2:{ rewrite PG5_None by (apply get_sym_None; s8; unfold blk_cap; lia).
      wstep. exitK MU WM. }
    (* [comment removed for export] *)
    wstep. wstep. wstep.
    call_iif tp1.
    pose proof (IHT5 (PST k0 (k1 + 4) (nu + 1) k0 tp1 rn rt cb out av tout tol toh)) as T5. unfold B0F_bzd_snr1.T5S, B0F_bzd_snr1.TcS, B0F_bzd_snr1.CH in T5; unfold S0F_bzd_snr1.D, S0F_bzd_snr1.Ss, S0F_bzd_snr1.Jp in T5.
    pcut_in T5. specialize (T5 ltac:(lia)).
    enter_with (T5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ dbytes rest);
      [ st_eq
      | ch_close MU WM
      | sinv_close
      | lia | lia | lia | reflexivity | lia | lia | lia ].
  Time Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma snr_T5 : forall f', (forall p', MS_ f' p') -> forall p, T5S f' p.
  Proof.
    intros f' IHM p. unfold B0F_bzd_snr1.T5S, B0F_bzd_snr1.TcS. intros HnuP. intros until rest. intros CHm SI Hf Hav Hol Hoc Rk0 Hnu Htp.
    destruct p as [oc ol nu k0 tp rn rt cb out av tout tol toh].
    unfold B0F_bzd_snr1.CH, S0F_bzd_snr1.D, S0F_bzd_snr1.Ss, S0F_bzd_snr1.Jp, S0F_bzd_snr1.sinv in *.
    pcut_all. subst oc.
    cps_destruct SI as (Rcb & Roc & Rol & Rnu & _ & Rtp & Ern & Ert & Rav & Lout').
    unCH CHm. prep. unSH.
    unfold DSgA, DESTgA in *. b0img. focbn_in HD. focbn_in NBU. focbn_in MID. focbn_in SM. focbn_in SAV. focbn_in Edb. focbn_in Lout.
    (* [comment removed for export] *)
    pose proof (get_sym_SN (set8 d0 k0 ol nu k0 tp rn rt cb) ltac:(s8; unfold blk_cap; lia) ltac:(s8; rewrite Esm, HSM; lia) ltac:(s8; exact RD0)) as GS1.
    rewrite gsSN_set8 in GS1.
    rewrite (PG5_Some _ _ _ _ _ GS1). s8.
    pose proof (Rl16 tp) as R16. pose proof (Rl4 (tp / 2)%Z) as R4.
    rewrite (get_ll_llval d0 tp) by lia.
    pose proof (indexIntoF_range tp cf) as KR. set (k1 := indexIntoF tp cf) in *.
    (* [comment removed for export] *)
    brun_to 0x86e10%Z. wstep.
    (* [comment removed for export] *)
    brun_to 0x86e40%Z. try rewrite (zx32_of_Z tp) by lia.
    brun_to 0x86ebc%Z. l16_load tp. set (v16 := zget (d_ll16 d0) tp) in *.
    (* [comment removed for export] *)
    brun_to 0x86ecc%Z. l4_load (tp / 2)%Z. set (v4 := zget (d_ll4 d0) (tp / 2)) in *.
    (* [comment removed for export] *)
    brun_to 0x86ee0%Z. name_sh tp sh. pose proof (shiftr_byte v4 sh ltac:(lia) ltac:(lia)) as SR4.
    (* [comment removed for export] *)
    wstep. srlw_norm v4 sh. wstep. wstep. wstep. fold_ll v16 v4 tp sh Esh.
    pose proof (llval_range v16 v4 tp ltac:(lia) ltac:(lia) ltac:(lia)) as TPR1. set (tp1 := llval v16 v4 tp) in *.
    (* [comment removed for export] *)
    wstep.
    (* [comment removed for export] *)
    brun_to 0x86f04%Z. try rewrite (sx32_of_Z nu) by lia.
    (* [comment removed for export] *)
    brun_to 0x86a2c%Z. wstep. try nbu_fix (nu + 1)%Z. wstep.
    goM IHM (PST k0 ol (nu + 1) k1 tp1 rn rt cb out av tout tol toh) dbytes rest MU WM.
  Time Qed.
End SNR.
End ACeilS1.
